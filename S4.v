(** S4 

    * File for S4 specific definitions   

***)

Require Import List.
Require Import Forest.
Require Import String.
Import ListNotations.

Definition pruning_S4_0 (a : nat) : bool := Nat.eqb a 2.
Definition pruning_S4_1 (a : nat) : bool := Nat.eqb a 2.
Definition pruning_S4_2 (a : nat) : bool := Nat.eqb a 1.

(**
   ** Language specific definitions 
**)

Inductive LF :=
| Atom : string -> LF
| Neg : LF -> LF
| Box : LF -> LF
| Impl : LF -> LF -> LF.

Notation "! A" := (Atom A) (at level 10).
Notation "~ A" := (Neg A).
Notation "[] A" := (Box A) (at level 80).
Notation "A ~> B" := (Impl A B) (at level 90).
Notation "A /\ B" := (~(A ~> ~B)).
Notation "A \/ B" := ((~A) ~> B).

Definition P := Atom "P".
Definition Q := Atom "Q".
Definition R := Atom "R".
Definition U := Atom "U".

Fixpoint eqb_lf (A : LF) (B : LF) :=
  match A with
  | Atom P => match B with
              | Atom Q => if (String.eqb P Q) then true
                          else false
              | _ => false
              end
  | ~ P => match B with
           | ~ Q => eqb_lf P Q
           | _ => false
           end
  | [] P => match B with
           | [] Q => eqb_lf P Q
           | _ => false
            end
  | P ~> Q => match B with
              | R ~> T => andb (eqb_lf P R) (eqb_lf Q T)
              | _ => false
              end
  end.

Fixpoint length_lf (A : LF) :=
  match A with
  | Atom P => 0
  | ~ P => 1 + length_lf P
  | [] P => 1 + length_lf P
  | P ~> Q => 1 + length_lf P + length_lf Q
  end.

Definition leb_lf (A : LF) (B : LF) :=
  Nat.leb (length_lf A) (length_lf B).

Fixpoint GetAllSubformulas (L : LF) :=
  match L with
  | Atom A => (Atom A)::nil
  | ~ A => (~ A)::(GetAllSubformulas A)
  | [] A => ([] A)::(GetAllSubformulas A)
  | A ~> B => (A ~> B)::((GetAllSubformulas A)++(GetAllSubformulas B))
  end.

(*********)

(* Auxiliary functions *)

Fixpoint unary_op
  (A B : LF)
  (partialV : btree LF)
  (vB : nat)
  (V : LF -> nat -> btree LF)
  : btree LF
  :=
  match partialV with
  | Leaf _ _ =>
      V A vB
  | Alpha _ n t =>
      match n with
      | Node _ i D =>
          if (eqb_lf B D) then
            Alpha _ n (unary_op A B t i V)
          else Alpha _ n (unary_op A B t vB V)
      end
  | Beta _ t1 t2 =>
      Beta _
        (unary_op A B t1 vB V)
        (unary_op A B t2 vB V)
  end.

Fixpoint bin_op
  (A B C : LF)
  (partialV : btree LF)
  (vB vC : nat)
  (V : LF -> nat -> nat -> btree LF)
  : btree LF
  :=
  match partialV with
  | Leaf _ _ =>
      V A vB vC
  | Alpha _ n t =>
      match n with
      | Node _ i D =>
          if (eqb_lf B D) then
            if (eqb_lf C D) then
              Alpha _ n (bin_op A B C t i i V)
            else
              Alpha _ n (bin_op A B C t i vC V)
          else
            if (eqb_lf C D) then
              Alpha _ n (bin_op A B C t vB i V)
            else Alpha _ n (bin_op A B C t vB vC V)
      end
  | Beta _ t1 t2 =>
      Beta _
        (bin_op A B C t1 vB vC V)
        (bin_op A B C t2 vB vC V)
  end.

(* Truth-table definitions *)

(* Implication *)

Definition S4_impl_def
  (* [vA] -> [vB] *)
  (A : LF)
  (vB vC : nat)
  : btree LF
  :=
  match vB with
  | 0 =>
      Beta _
        (Alpha _ (Node _ 1 A) (Leaf _ true))
        (Alpha _ (Node _ 2 A) (Leaf _ true))
  | 1 =>
      match vC with
      | 0 =>
          Alpha _ (Node _ 0 A) (Leaf _ true)
      | _ =>
          Beta _
            (Alpha _ (Node _ 1 A) (Leaf _ true))
            (Alpha _ (Node _ 2 A) (Leaf _ true))
      end
  | 2 =>
      match vC with
      | 0 =>
          Alpha _ (Node _ 0 A) (Leaf _ true)
      | 1 =>
          Alpha _ (Node _ 1 A) (Leaf _ true)
      | _ =>
          Beta _
            (Alpha _ (Node _ 1 A) (Leaf _ true))
            (Alpha _ (Node _ 2 A) (Leaf _ true))
      end
  | _ => Leaf _ true
  end.

(* Optimal implication . 

By applying the filter over A ~> B we observe that we can immmediately make the following 
simplification of the nmatrix for implication.
*)

Definition S4_impl_optimal_def
  (* [vA] -> [vB] *)
  (A : LF)
  (vB vC : nat)
  : btree LF
  :=
  match vB with
  | 0 =>
      match vC with
      | 2 =>
          Alpha _ (Node _ 2 A) (Leaf _ true)
      | _ =>
          Beta _
            (Alpha _ (Node _ 1 A) (Leaf _ true))
            (Alpha _ (Node _ 2 A) (Leaf _ true))
      end
  | 1 =>
      match vC with
      | 0 =>
          Alpha _ (Node _ 0 A) (Leaf _ true)
      | 2 =>
          Alpha _ (Node _ 2 A) (Leaf _ true)
      | _ =>
          Beta _
            (Alpha _ (Node _ 1 A) (Leaf _ true))
            (Alpha _ (Node _ 2 A) (Leaf _ true))
      end
  | 2 =>
      match vC with
      | 0 =>
          Alpha _ (Node _ 0 A) (Leaf _ true)
      | 1 =>
          Alpha _ (Node _ 1 A) (Leaf _ true)
      | _ =>
          Alpha _ (Node _ 2 A) (Leaf _ true)
      end
  | _ => Leaf _ true
  end.

(* Box *)

Definition S4_box_def
  (* ~ [vA] *)
  (A : LF)
  (vB : nat)
  : btree LF
  :=
  match vB with
  | 0 =>
      Alpha _ (Node _ 0 A) (Leaf _ true)
  | 1 =>
      Alpha _ (Node _ 0 A) (Leaf _ true)
  | 2 =>
      Alpha _ (Node _ 2 A) (Leaf _ true)
  | _ => Leaf _ true
  end.

(* Negation *)

Definition S4_neg_def
  (* ~ [vA] *)
  (A : LF)
  (vB : nat)
  : btree LF
  :=
  match vB with
  | 0 =>
      Beta _
        (Alpha _ (Node _ 1 A) (Leaf _ true))
        (Alpha _ (Node _ 2 A) (Leaf _ true))
  | 1 =>
      Alpha _ (Node _ 0 A) (Leaf _ true)
  | 2 =>
      Alpha _ (Node _ 0 A) (Leaf _ true)
  | _ => Leaf _ true
  end.

(** S4 **)

Definition S4
  (A : LF)
  (partialV : btree LF)
  : btree LF
  :=
  match A with
  | Atom B => Leaf _ true
  | Neg B =>
      unary_op A B partialV 0 S4_neg_def
  | Box B =>
      unary_op A B partialV 0 S4_box_def
  | Impl B C =>
      bin_op A B C partialV 0 0 S4_impl_def
  end.

(*************************************)

(* 

   Testes
 
*)

(*************************************)

Notation "<> A" := (Neg (Box (Neg A))) (at level 50).

Definition AK := ([](P ~> Q) ~> ([]P ~> []Q)).
Definition AB := P ~> []<>P.
Definition AM := []P ~> P.
Definition A4 := []P ~> [][]P.
Definition AD := []P ~> <>P.
Definition A5 := <>P ~> []<>P.

(* Nessa lógica, valem AK, AD, AM e A4. *)

Compute
  nodeToNat (
  MakeWithPrune
    eqb_lf
    leb_lf
    length_lf
    GetAllSubformulas
    S4
    [pruning_S4_0;pruning_S4_1;pruning_S4_2]
    P
    ([] (P ~> P))
    [0;1;2]
    )
.
