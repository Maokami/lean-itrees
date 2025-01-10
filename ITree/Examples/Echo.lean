import ITree.ITree
import ITree.Eutt
import ITree.Effect

open ITree

inductive Ev : Type -> Type
| input  : Ev Int
| output : Int -> Ev Unit
deriving Repr

/-- Just echo once. -/
def echo1 : ITree Ev Unit :=
  .vis .input fun (answer : Int) =>
    .vis (.output answer) fun _ =>
      .ret ()
