import ITree.ITree
import ITree.Eutt
import ITree.Effect

open ITree

/-- Finds a `k`, such that `f k = K`, but only searches >=0. -/
def find (f : Nat -> Int) (K : Int) (a : Nat) : ITree None Nat :=
  ITree.corec (fun a =>
    if f a.down = K then .ret a
    else .tau (a+1)
  ) a
