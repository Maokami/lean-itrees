/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Max Nowak
-/

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
