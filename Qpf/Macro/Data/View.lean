import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Mathlib.Data.QPF.Multivariate.Constructions.Fix

import Lean
import Qpf.Macro.Common

open Lean
open Meta Elab Elab.Command
open Parser.Term (bracketedBinder)
open Parser.Command (declId)

open Macro (withQPFTraceNode)

inductive DataCommand where
  | Data
  | Codata
  deriving BEq, Inhabited

namespace DataCommand

def fromSyntax : Syntax → TermElabM DataCommand
  | Syntax.atom _ "data"   => pure .Data
  | Syntax.atom _ "codata" => pure .Codata
  | stx => throwErrorAt stx "Expected either `data` or `codata`"

instance : ToString DataCommand where
  toString := fun
    | .Data => "data"
    | .Codata => "codata"

/--
  Return a syntax tree for `MvQPF.Fix` or `MvQPF.Cofix` when self is `Data`, resp. `Codata`.
-/
def fixOrCofix : DataCommand → Ident
  | .Data   => mkIdent ``_root_.MvQPF.Fix
  | .Codata => mkIdent ``_root_.MvQPF.Cofix

/--
  Return a syntax tree for `MvPFunctor.W` or `MvPFunctor.M` when self is `Data`, resp. `Codata`.
-/
def fixOrCofixPolynomial : DataCommand → Ident
  | .Data   => mkIdent ``_root_.MvPFunctor.W
  | .Codata => mkIdent ``_root_.MvPFunctor.M

end DataCommand





/-
  Mostly a replication of `InductiveView`, but for `data`/`codata`
  The `binders` field is replaced by `liveBinders`/`deadBindders`
-/
structure DataView where
  ref             : Syntax
  declId          : Syntax
  modifiers       : Modifiers
  shortDeclName   : Name
  declName        : Name
  levelNames      : List Name
  binders         : Syntax
  type?           : Option Syntax
  ctors           : Array CtorView
  derivingClasses : Array DerivingClassView
  /-- The declaration docstring, and whether it's Verso -/
  docString?      : Option (TSyntax ``Lean.Parser.Command.docComment × Bool)
  -- further elements are changed from inductiveView
  command         : DataCommand
  liveBinders     : TSyntaxArray ``Parser.Term.binderIdent
  deadBinders     : TSyntaxArray ``bracketedBinder
  deadBinderNames : Array Ident
    deriving Inhabited





def DataView.asInductive (view : DataView) : InductiveView
  := { view with
    -- TODO: find out what these computed fields are, add support for them in `data`/`codata`
    computedFields  := #[]
    isClass := false
    allowIndices := false
    allowSortPolymorphism := false
  }


open Lean.Parser in
def DataView.pushLiveBinder (view : DataView) (binderIdent : TSyntax ``Parser.Term.binderIdent) : DataView
  :=  let liveBinders := view.liveBinders.push binderIdent
      let binders := view.binders
      let binders := binders.setArgs (binders.getArgs.push binderIdent)
      { view with liveBinders, binders, }

def DataView.popLiveBinder (view : DataView) : DataView
  :=  if view.liveBinders.size == 0 then
        view
      else
        let liveBinders := view.liveBinders.pop
        let binders := view.binders
        let binders := binders.setArgs (binders.getArgs.pop)
        { view with liveBinders, binders, }


def DataView.setCtors (view : DataView) (ctors : Array CtorView) : DataView
  :=  { view with ctors, }



def DataView.addDeclNameSuffix (view : DataView) (suffix : String) : DataView
  :=  let declName := Name.mkStr view.declName suffix
      let declId   := mkNode ``Parser.Command.declId #[mkIdent declName, mkNullNode]
      let shortDeclName := Name.mkSimple suffix
      { view with declName, declId, shortDeclName }


/--
  Returns the fully applied form of the type to be defined.
  The `name` parameter allows the user to control what the const at the bottom of the type is.
  This lets the user get types that have the same parameters such as the DeepThunk types.
-/
def DataView.getExpectedTypeWithName (view : DataView) (name : Name) : Term :=
  Macro.getBinderIdents view.binders.getArgs false |> Syntax.mkApp (mkIdent name)

/-- Returns the fully applied form of the type to be defined -/
def DataView.getExpectedType (view : DataView) : Term :=
  view.getExpectedTypeWithName view.shortDeclName

/-- Returns the fully applied, explicit (`@`) form of the type to be defined -/
def DataView.getExplicitExpectedType (view : DataView) : CommandElabM Term
  :=  let args := Macro.getBinderIdents view.binders.getArgs true
      `(
        @$(mkIdent view.shortDeclName):ident $args:term*
      )

/-! ## MessageData -/

instance : ToMessageData CtorView where
  toMessageData ctor := m!"\{\
  modifiers := {ctor.modifiers},
  declName  := {ctor.declName},
  binders   := {ctor.binders},
  type?     := {ctor.type?},
}"

/-
We omit ref from the output, since it tends to dump a large amount of not
particularly interesting syntax -- especially considering ref is only used
as a reference to know where to throw an error
-/
instance : ToMessageData InductiveView where
  toMessageData view := m!"\{\
  declId          := {view.declId},
  modifiers       := {view.modifiers},
  ref             := <omitted>,
  declId          := {view.declId          },
  modifiers       := {view.modifiers       },
  shortDeclName   := {view.shortDeclName   },
  declName        := {view.declName        },
  levelNames      := {view.levelNames      },
  binders         := {view.binders         },
  type?           := {view.type?},
  ctors           := {view.ctors},
  derivingClasses := <omitted>,
}"

instance : ToMessageData DataView where
  toMessageData view := m!"\{\
  declId          := {view.declId},
  modifiers       := {view.modifiers},
  ref             := <omitted>,
  declId          := {view.declId          },
  modifiers       := {view.modifiers       },
  shortDeclName   := {view.shortDeclName   },
  declName        := {view.declName        },
  levelNames      := {view.levelNames      },
  binders         := {view.binders         },
  type?           := {view.type?},
  ctors           := {view.ctors},
  derivingClasses := <omitted>,
  command         := {view.command         },
  liveBinders     := {view.liveBinders     },
  deadBinders     := {view.deadBinders     },
  deadBinderNames := {view.deadBinderNames },
}"


@[deprecated]
def CtorView.debug (ctor: CtorView) : String :=
  (s!"\{
  modifiers := {ctor.modifiers},
  declName  := {ctor.declName},
  binders   := {ctor.binders},
  type?     := {ctor.type?},
}")

@[deprecated]
def DataView.debug (view : DataView) : String :=
  let ctors := view.ctors.map CtorView.debug
s!"\{
  declId          := {view.declId},
  modifiers       := {view.modifiers},
  ref             := {view.ref             },
  declId          := {view.declId          },
  modifiers       := {view.modifiers       },
  shortDeclName   := {view.shortDeclName   },
  declName        := {view.declName        },
  levelNames      := {view.levelNames      },
  binders         := {view.binders         },
  type?           := {view.type?},
  ctors           := {ctors},
  derivingClasses := TODO,
  command         := {view.command         },
  liveBinders     := {view.liveBinders     },
  deadBinders     := {view.deadBinders     },
  deadBinderNames := {view.deadBinderNames },
}"

instance : ToString (DataView) := ⟨
  fun view => view.debug
⟩


/-
  # Parsing syntax into a view
-/


/--
  Raises (hopefully) more informative errors when `data` or `codata` are used with unsupported
  specifications
-/
def DataView.doSanityChecks (view : DataView) : TermElabM Unit := do
  if view.liveBinders.isEmpty then
    if view.deadBinders.isEmpty then
      if view.command == .Codata then
        throwError "Due to a bug, codatatype without any parameters don't quite work yet. Please try adding parameters to your type"
      else
        throwError "Trying to define a datatype without variables, you probably want an `inductive` type instead"
    else
      throwErrorAt view.binders "You should mark some variables as live by removing the type ascription (they will be automatically inferred as `Type _`), or if you don't have variables of type `Type _`, you probably want an `inductive` type"

  -- TODO: remove once dead variables are fully supported
  if !view.deadBinders.isEmpty then
    dbg_trace "Dead variables are not fully supported yet"


  -- TODO: make this more intelligent. In particular, allow types like `Type`, `Type 3`, or `Type u`
  --       and only throw an error if the user tries to define a family of types
  match view.type? with
  | some t => throwErrorAt t "Unexpected type; type will be automatically inferred. Note that inductive families are not supported due to inherent limitations of QPFs"
  | none => pure ()


/-
  Heavily based on `inductiveSyntaxToView` from Lean.Elab.Inductive
-/
def dataSyntaxToView (modifiers : Modifiers) (decl : Syntax) : TermElabM DataView :=
  withQPFTraceNode "dataSyntaxToView" (tag := "dataSyntaxToView") <| do

  -- `data`/`codata` declarations may be noncomputable (not sure about partial, but we allow it for now)
  -- checkValidInductiveModifier modifiers

  let (binders, type?) := expandOptDeclSig decl[2]
  let declId           := decl[1]
  let ⟨name, declName, levelNames, docString?⟩ ← Term.expandDeclId (← getCurrNamespace) (← Term.getLevelNames) declId modifiers
  addDeclarationRangesForBuiltin declName modifiers.stx decl
  let ctors      ← decl[4].getArgs.mapM fun ctor => withRef ctor do
    /-
    ```
    def ctor := leading_parser optional docComment >> "\n| " >> declModifiers >> rawIdent >> optDeclSig
    ```
    -/
    let modifiersStx := ctor[2]
    let mut ctorModifiers ← elabModifiers ⟨modifiersStx⟩
    if let some leadingDocComment := ctor[0].getOptional? then
      if ctorModifiers.docString?.isSome then
        logErrorAt leadingDocComment "Duplicate doc string"
      ctorModifiers := { ctorModifiers with
        docString? := some (⟨leadingDocComment⟩, doc.verso.get (← getOptions)) }
    if ctorModifiers.isPrivate && modifiers.isPrivate then
      let hint ← do
        let .original .. := modifiersStx.getHeadInfo | pure .nil
        let some range := modifiersStx[2].getRangeWithTrailing? | pure .nil
        -- Drop the doc comment from both the `declModifiers` and outer `ctor`, as well as
        -- everything after the constructor name (yielding invalid syntax with the desired range)
        let previewSpan? := ctor.modifyArgs (·[2...4].toArray.modify 0 (·.modifyArgs (·[1...*])))
        MessageData.hint "Remove `private` modifier from constructor" #[{
          suggestion := ""
          span? := Syntax.ofRange range
          previewSpan?
          toCodeActionTitle? := some fun _ => "Delete `private` modifier"
        }]
      throwError m!"Constructor cannot be marked `private` because it is already in a `private` inductive datatype" ++ hint
    if ctorModifiers.isProtected && modifiers.isPrivate then
      throwError "Constructor cannot be `protected` because it is in a `private` inductive datatype"
    checkValidCtorModifier ctorModifiers
    let ctorName := ctor.getIdAt 3
    let ctorName := declName ++ ctorName
    let ctorName ← withRef ctor[3] <| applyVisibility ctorModifiers ctorName
    let (binders, type?) := expandOptDeclSig ctor[4]
    addDeclarationRangesFromSyntax ctorName ctor ctor[3]
    if modifiers.isMeta then
      modifyEnv (addMeta · ctorName)
    return { ref := ctor, declId := ctor[3], modifiers := ctorModifiers, declName := ctorName, binders := binders, type? := type? : CtorView }
  let classes ← getOptDerivingClasses decl[6]

  let command ← DataCommand.fromSyntax decl[0]
  let (liveBinders, deadBinders) ← Macro.splitLiveAndDeadBinders binders.getArgs
  let (deadBinders, deadBinderNames) ← Macro.mkFreshNamesForBinderHoles deadBinders

  let view := {
    ref             := decl
    shortDeclName   := name
    derivingClasses := classes
    declId, modifiers, declName, levelNames
    binders, type?, ctors,
    command, liveBinders, deadBinders, deadBinderNames,
    docString?
  }
  withQPFTraceNode "elaborated view …" <| do
    trace[QPF] m!"{view}"

  view.doSanityChecks
  return view
