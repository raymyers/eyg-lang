-- Root module for the EYG Lean formalization.
-- Re-exports the project's submodules so `import Eyg` pulls everything in.
import Eyg.Basic
import Eyg.Ir.Tree
import Eyg.Ir.Cid
import Eyg.Interpreter.Value
import Eyg.Interpreter.Break
import Eyg.Interpreter.Cast
import Eyg.Interpreter.Builtin
import Eyg.Interpreter.State
import Eyg.Spec.Harness
import Eyg.Semantics.Basic
import Eyg.Semantics.FunctionalBigStep
import Eyg.Semantics.Lts
import Eyg.Semantics.Reduction
import Eyg.Semantics.Correspondence
import Eyg.Semantics.Behavior
import Eyg.Semantics.Metatheory
import Eyg.Types.Ty
import Eyg.Types.TyEquivInv
import Eyg.Types.Scheme
import Eyg.Types.Typing
import Eyg.Types.Runtime
import Eyg.Types.Machine
