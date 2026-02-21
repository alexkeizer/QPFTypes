import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Mathlib.Data.QPF.Multivariate.Constructions.Fix

import Qpf.Elab.ShapeType

import Qpf.Macro.Data.Constructors
import Qpf.Macro.Data.Replace
import Qpf.Macro.Data.Count
import Qpf.Macro.Data.View
import Qpf.Macro.Data.Ind
import Qpf.Macro.Common
import Qpf.Macro.Comp

open Lean Meta Elab.Command
open Elab (Modifiers elabModifiers)
open Parser.Term (namedArgument)
open PrettyPrinter (delab)

open Macro (withQPFTraceNode elabCommandAndTrace)

private def Array.enum (as : Array α) : Array (Nat × α) :=
  (Array.range as.size).zip as

/--
  Given a natural number `n`, produce a sequence of `n` calls of `.fs`, ending in `.fz`.

  The result corresponds to a `i : PFin2 _` such that `i.toNat == n`
-/
private def PFin2.quoteOfNat : Nat → Term
  | 0   => mkIdent ``PFin2.fz
  | n+1 => Syntax.mkApp (mkIdent ``PFin2.fs) #[(quoteOfNat n)]

private def Fin2.quoteOfNat : Nat → Term
  | 0   => mkIdent ``Fin2.fz
  | n+1 => Syntax.mkApp (mkIdent ``Fin2.fs) #[(quoteOfNat n)]


namespace Data.Command

/-!
  ## Parser
  for `data` and `codata` declarations
-/
section
  open Lean.Parser Lean.Parser.Command

  def inductive_like (cmd : String) : Parser
    := leading_parser cmd >> declId  >> optDeclSig
                        >> Parser.optional  (symbol " :=" <|> " where")
                        >> many ctor
                        >> optDeriving

  def data := inductive_like "data "
  def codata := inductive_like "codata "

  @[command_parser]
  def declaration : Parser
    := leading_parser declModifiers false >> (data <|> codata)
end

/-!
  ## Elaboration
-/
open Elab.Term (TermElabM)

def CtorView.declReplacePrefix (pref new_pref : Name) (ctor: CtorView) : CtorView :=
  { ctor with
      declName := ctor.declName.replacePrefix pref new_pref
  }


open Parser.Command (declId)
/-- Return a tuple of `declName, declId, shortDeclName` -/
private def addSuffixToDeclId {m} [Monad m] [MonadResolveName m] (declId : Syntax) (suffix : String) :
    m (Name × (TSyntax ``declId) × Name) := do
  let (id, _) := Elab.expandDeclIdCore declId
  let declName := Name.mkStr id suffix
  let declId := mkNode ``declId #[mkIdent declName, mkNullNode]

  let curNamespace ← getCurrNamespace
  let declName := curNamespace ++ declName

  let shortDeclName := Name.mkSimple suffix
  return (declName, declId, shortDeclName)

private def addSuffixToDeclIdent {m} [Monad m] [MonadResolveName m] (declId : Syntax) (suffix : String) :
    m Ident := do
  let (_, uncurriedDeclId, _) ← addSuffixToDeclId declId suffix
  pure ⟨uncurriedDeclId.raw[0]⟩

open private elabInductiveViews from Lean.Elab.MutualInductive in
open private elabCtors from Lean.Elab.Inductive in
private def elabInductiveView (vars : Array Expr) (view : InductiveView) : TermElabM Unit := do
  let view := {
    view
    elabCtors := fun rs r params => do
      let ctors ← elabCtors (rs.map (·.indFVar)) params r
      return { ctors }
  }
  let _ ← elabInductiveViews vars #[view]

open Parser in
/--
  Defines the "head" type of a polynomial functor

  That is, it defines a type with exactly as many constructor as the input type, but such that
  all constructors are constants (take no arguments).
-/
def mkHeadT (view : InductiveView) : CommandElabM Name := do
  let (declName, declId, shortDeclName) ← addSuffixToDeclId view.declId "HeadT"
  withQPFTraceNode m!"defining `{declName}`" (tag := "mkHeadT") <| do
  -- If the original declId was `MyType`, we want to register the head type under `MyType.HeadT`



  let modifiers : Modifiers := {
    isUnsafe := view.modifiers.isUnsafe
  }
  -- The head type is the same as the original type, but with all constructor arguments removed
  let ctors ← view.ctors.mapM fun ctor => do
    let declName := ctor.declName.replacePrefix view.declName declName
    pure { ctor with
      modifiers, declName,
      binders := mkNullNode,
      type? := none
      : CtorView
    }

  -- let type ← `(Type $(mkIdent `u))

  -- TODO: make `HeadT` universe polymorphic
  let view := { view with
    ctors, declId, declName, shortDeclName, modifiers,
    binders         := view.binders.setArgs #[]
  }

  withQPFTraceNode "elabInductiveViews" <|
    runTermElabM (elabInductiveView · view)
  pure declName

open Parser Parser.Term Parser.Command in
/--
  Defines the "child" family of type vectors for an `n`-ary polynomial functor

  That is, it defines a type `ChildT : HeadT → TypeVec n` such that number of inhabitants of
  `ChildT a i` corresponds to the times that constructor `a` takes an argument of the `i`-th type
  argument
-/
def mkChildT (view : InductiveView) (r : Replace) (headTName : Name) : CommandElabM Name := do
  -- If the original declId was `MyType`, we want to register the child type under `MyType.ChildT`
  let (declName, declId, _shortDeclName) ← addSuffixToDeclId view.declId "ChildT"
  withQPFTraceNode m!"defining `{declName}`" (tag := "mkChildT") <| do

  let target_type := Syntax.mkApp (mkIdent ``TypeVec) #[quote r.arity]

  let matchAlts ← view.ctors.mapM fun ctor => do
    let head := Lean.mkIdent (ctor.declName.replacePrefix view.declName headTName)

    let counts := countVarOccurences r ctor.type?
    let counts := counts.map fun n =>
                    Syntax.mkApp (mkIdent ``PFin2) #[quote n]

    `(matchAltExpr| | $head => (!![ $counts,* ]))

  let body ← `(declValEqns|
    $[$matchAlts:matchAlt]*
  )
  let headT := mkIdent headTName

  elabCommandAndTrace <|← `(
    def $declId : $headT → $target_type
      $body:declValEqns
  )

  pure declName



open Parser.Term in
/--
  Show that the `Shape` type is a qpf, through an isomorphism with the `Shape.P` pfunctor
-/
def mkQpf (shapeView : InductiveView) (ctorArgs : Array CtorArgs) (headT P : Ident) (arity : Nat) : CommandElabM Unit := do
  withQPFTraceNode m!"deriving instance of `MvQPF {shapeView.shortDeclName}`"
    (tag := "mkQPF") <| do

  let (shapeN, _) := Elab.expandDeclIdCore shapeView.declId
  let eqv := mkIdent $ Name.mkStr shapeN "equiv"
  let functor := mkIdent $ Name.mkStr shapeN "functor"
  let q := mkIdent $ Name.mkStr shapeN "qpf"
  let shape := mkIdent shapeN

  let ctors := shapeView.ctors.zip ctorArgs

  /-
    `box` maps objects from the curried form, to the internal uncurried form.
    See below, or [.ofPolynomial] for the signature

    Example, using a simple list type
    ```lean4
     fun x => match x with
    | MyList.Shape.nil a b => ⟨MyList.Shape.HeadT.nil, fun i => match i with
        | 0 => Fin2.elim0 (C:=fun _ => _)
        | 1 => fun j => match j with
                | (.ofNat' 0) => b
        | 2 => fun j => match j with
                | (.ofNat' 0) => a
    ⟩
    | MyList.Shape.cons a as => ⟨MyList.Shape.HeadT.cons, fun i j => match i with
        | 0 => match j with
                | .fz => as
        | 1 => Fin2.elim0 (C:=fun _ => _) j
        | 2 => match j with
                | .fz => a
    ```
  -/

  let boxBody ← ctors.mapM fun (ctor, args) => do
    let argsId  := args.args.map mkIdent
    let alt     := mkIdent ctor.declName
    let headAlt := mkIdent $ ctor.declName.replacePrefix shapeView.declName headT.getId

    `(matchAltExpr| | $alt:ident $argsId:ident* => ⟨$headAlt:ident, fun i => match i with
        $(
          ←args.per_type.enum.mapM fun (i, args) => do
            let i := arity - 1 - i
            let body ← if args.size == 0 then
                          -- `(fun j => Fin2.elim0 (C:=fun _ => _) j)
                          `(PFin2.elim0)
                        else
                          let alts ← args.enum.mapM fun (j, arg) =>
                              let arg := mkIdent arg
                              `(matchAltExpr| | $(PFin2.quoteOfNat j) => $arg)
                          `(
                            fun j => match j with
                              $alts:matchAlt*
                          )
            `(matchAltExpr| | $(Fin2.quoteOfNat i) => $body)
        ):matchAlt*
    ⟩)
  let box ← `(
    fun x => match x with
      $boxBody:matchAlt*
  )

  /-
    `unbox` does the opposite of `box`; it maps from uncurried to curried

    fun ⟨head, child⟩ => match head with
    | MyList.Shape.HeadT.nil  => MyList.Shape.nil (child 2 .fz) (child 1 .fz)
    | MyList.Shape.HeadT.cons => MyList.Shape.cons (child 2 .fz) (child 0 .fz)
  -/

  /- the `child` variable in the example above -/
  let unbox_child := mkIdent <|<- Elab.Term.mkFreshBinderName;
  let unboxBody ← ctors.mapM fun (ctor, args) => do
    let alt     := mkIdent ctor.declName
    let headAlt := mkIdent $ ctor.declName.replacePrefix shapeView.declName headT.getId

    let args : Array Term ← args.args.mapM fun arg => do
      -- find the pair `(i, j)` such that the argument is the `j`-th occurence of the `i`-th type
      let (i, j) := (args.per_type.enum.map fun (i, t) =>
        -- the order of types is reversed, since `TypeVec`s count right-to-left
        let i := arity - 1 - i
        ((t.idxOf? arg).map fun j => (i, j)).toList
      ).toList.flatten[0]!

      `($unbox_child $(Fin2.quoteOfNat i) $(PFin2.quoteOfNat j))

    let body := Syntax.mkApp alt args

    `(matchAltExpr| | $headAlt:ident => $body)

  let unbox ← `(
    fun ⟨head, $unbox_child⟩ => match head with
        $unboxBody:matchAlt*
  )

  let header := m!"showing that {shapeView.declName} is equivalent to a polynomial functor …"
  elabCommandAndTrace (header := header) <|← `(
    def $eqv:ident {Γ} : (@TypeFun.ofCurried $(quote arity) $shape) Γ ≃ ($P).Obj Γ where
      toFun     := $box
      invFun    := $unbox
      left_inv  := by
        simp only [Function.LeftInverse]
        intro x
        cases x
        <;> rfl
      right_inv := by
        simp only [Function.RightInverse, Function.LeftInverse]
        intro x
        rcases x with ⟨head, child⟩;
        cases head
        <;> simp
        <;> apply congrArg
        <;> (funext i; fin_cases i)
        <;> (funext (j : PFin2 _); fin_cases j)
        <;> rfl
  )
  elabCommandAndTrace (header := "defining {functor}") <|← `(
    instance $functor:ident : MvFunctor (@TypeFun.ofCurried $(quote arity) $shape) where
      map f x   := ($eqv).invFun <| ($P).map f <| ($eqv).toFun <| x
  )
  elabCommandAndTrace (header := "defining {q}") <|← `(
    instance $q:ident : MvQPF (@TypeFun.ofCurried $(quote arity) $shape) :=
      .ofEquiv (fun _ => $eqv)
  )

/-! ## mkShape -/

structure MkShapeResult where
  (r : Replace)
  (shape : Name)
  (P : Name)
  (effects : CommandElabM Unit)

open Parser in
def mkShape (view : DataView) : TermElabM MkShapeResult := do
  -- If the original declId was `MyType`, we want to register the shape type under `MyType.Shape`
  let (declName, declId, shortDeclName) ← addSuffixToDeclId view.declId "Shape"

  withQPFTraceNode m!"defining `{declName}`" (tag := "mkShape") <| do


  -- Extract the "shape" functors constructors
  let shapeIdent  := mkIdent shortDeclName
  let ((ctors, ctorArgs), r) ← Replace.shapeOfCtors view shapeIdent
  let ctors := ctors.map (CtorView.declReplacePrefix view.declName declName)

  trace[QPF] "r.getBinders = {←r.getBinders}"
  trace[QPF] "r.expr = {r.expr}"

  -- Assemble it back together, into the shape inductive type
  let binders ← r.getBinders
  let binders := view.binders.setArgs #[binders]
  let modifiers : Modifiers := {
    isUnsafe := view.modifiers.isUnsafe
  }
  let view : InductiveView := { view with
    ctors, declId, declName, shortDeclName, modifiers, binders,
    levelNames      := []
    computedFields  := #[]
    isClass := false
    allowIndices := false
    allowSortPolymorphism := false
    : InductiveView
  }

  withQPFTraceNode "shape view …" <| do
    trace[QPF] m!"{view}"
  let PName := Name.mkStr declName "P"
  return ⟨r, declName, PName, do
    withQPFTraceNode "mkShape effects" <| do

    runTermElabM (elabInductiveView · view)

    let headTName ← mkHeadT view
    let childTName ← mkChildT view r headTName

    let PId := mkIdent PName
    -- let u ← Elab.Term.mkFreshBinderName
    let PDeclId := mkNode ``Command.declId #[PId, mkNullNode
      -- #[ TODO: make this universe polymorphic
      --   mkAtom ".{",
      --   mkNullNode #[u],
      --   mkAtom "}"
      -- ]
    ]

    let headTId := mkIdent headTName
    let childTId := mkIdent childTName

    elabCommandAndTrace <|← `(
      def $PDeclId:declId :=
        MvPFunctor.mk $headTId $childTId
    )

    mkQpf view ctorArgs headTId PId r.expr.size
  ⟩

/--
  Take either the fixpoint or cofixpoint of `base` to produce an `Internal` uncurried QPF,
  and define the desired type as the curried version of `Internal`
-/
def mkType (view : DataView) (base : Term × Term) : CommandElabM Unit :=
  withQPFTraceNode m!"defining (co)datatype {view.declId}" (tag := "mkType") <| do

  let uncurriedIdent ← addSuffixToDeclIdent view.declId "Uncurried"
  let baseIdExt ← addSuffixToDeclIdent view.declId "Base"
  let baseIdent ← addSuffixToDeclIdent baseIdExt "Uncurried"
  let baseQPFIdent ← addSuffixToDeclIdent baseIdent "instQPF"

  let deadBinderNamedArgs ← view.deadBinderNames.mapM fun n =>
        `(namedArgument| ($n:ident := $n:term))
  let uncurriedApplied ← `($uncurriedIdent:ident $deadBinderNamedArgs:namedArgument*)
  let baseApplied ← `($baseIdent:ident $deadBinderNamedArgs:namedArgument*)

  let arity := view.liveBinders.size
  let fix_or_cofix := DataCommand.fixOrCofix view.command

  let ⟨base, q⟩ := base
  elabCommandAndTrace
    (header := m!"elaborating uncurried base functor {baseIdent} …") <|← `(
      abbrev $baseIdent:ident $view.deadBinders:bracketedBinder* :
          TypeFun $(quote <| arity + 1) :=
        $base
  )

  elabCommandAndTrace
    (header := m!"elaborating *curried* base functor {baseIdExt} …") <|← `(
      abbrev $baseIdExt $view.deadBinders:bracketedBinder* :=
        TypeFun.curried $baseApplied
  )

  elabCommandAndTrace
    (header := m!"elaborating qpf instance for {baseIdent} …") <|← `(
      instance $baseQPFIdent:ident : MvQPF ($baseApplied) := $q
  )

  elabCommandAndTrace
    (header := m!"elaborating uncurried (co)fixpoint {uncurriedIdent} …") <|← `(
      abbrev $uncurriedIdent:ident $view.deadBinders:bracketedBinder* :
          TypeFun $(quote arity) :=
        $fix_or_cofix $base
  )

  elabCommandAndTrace
    (header := m!"elaborating *curried* (co)fixpoint {view.declId} …")  <|← `(
      abbrev $(⟨view.declId⟩) $view.deadBinders:bracketedBinder* :=
        TypeFun.curried $uncurriedApplied
  )

open Macro Comp in
/--
  Top-level elaboration for both `data` and `codata` declarations
-/
@[command_elab declaration]
def elabData : CommandElab := fun stx =>
  withQPFTraceNode "elabData" (tag := "elabData") (collapsed := false) <| do

  let modifiers ← elabModifiers ⟨stx[0]⟩
  let decl := stx[1]

  let view ← runTermElabM fun _ =>
    dataSyntaxToView modifiers decl
  let view ← preProcessCtors view -- Transforms binders into simple lambda types

  let (nonRecView, ⟨r, shape, _P, eff⟩) ← runTermElabM fun _ => do
    let (nonRecView, _rho) ← makeNonRecursive view;
    pure (nonRecView, ←mkShape nonRecView)

  /- Execute the `ComandElabM` side-effects prescribed by `mkShape` -/
  let _ ← eff

  /- Composition pipeline -/
  let base ← elabQpfCompositionBody {
    liveBinders := nonRecView.liveBinders,
    deadBinders := nonRecView.deadBinders,
    type?   := none,
    target  := ←`(
      $(mkIdent shape):ident $r.expr:term*
    )
  }

  mkType view base
  mkConstructors view shape

  if let .Data := view.command then
    try genRecursors view
    catch e =>
      trace[QPF] m!"Failed to generate recursors.\
        \n\n{e.toMessageData}"


end Data.Command
