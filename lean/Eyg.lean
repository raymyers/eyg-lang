-- Root module for the EYG Lean formalization.
-- Re-exports the project's submodules so `import Eyg` pulls everything in.
import Eyg.Basic
import Eyg.Ir.Tree
import Eyg.Interpreter.Value
import Eyg.Interpreter.Break
import Eyg.Interpreter.Cast
import Eyg.Interpreter.Builtin
import Eyg.Interpreter.State
import Eyg.Spec.Harness
