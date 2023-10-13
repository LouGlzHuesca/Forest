(* Intuitionistic language, with several examples of formulas. *)

Require Import List.
Import ListNotations.

Inductive iLF :=
| iAtom : nat -> iLF
| iNeg : iLF -> iLF
| iDisj : iLF -> iLF -> iLF
| iConj : iLF -> iLF -> iLF
| iImpl : iLF -> iLF -> iLF.

Notation "! A" := (iAtom A) (at level 10).
Notation "~ A" := (iNeg A).
Notation "A ~> B" := (iImpl A B) (at level 90).
Notation "A \/ B" := (iDisj A B).
Notation "A /\ B" := (iConj A B).
Notation "A <~> B" := ((A ~> B) /\ (B ~> A)) (at level 90).

Fixpoint eqb_ilf (A : iLF) (B : iLF) :=
  match A with
  | ! P => match B with
           | iAtom Q =>
               if (Nat.eqb P Q) then true
               else false
              | _ => false
              end
  | ~ P => match B with
           | ~ Q => eqb_ilf P Q
           | _ => false
           end
  | P \/ Q => match B with
              | R \/ T => andb (eqb_ilf P R) (eqb_ilf Q T)
              | _ => false
              end
  | P /\ Q => match B with
              | R /\ T => andb (eqb_ilf P R) (eqb_ilf Q T)
              | _ => false
              end
  | P ~> Q => match B with
              | R ~> T => andb (eqb_ilf P R) (eqb_ilf Q T)
              | _ => false
              end
  end.

Fixpoint length_ilf (A : iLF) :=
  match A with
  | ! P => 0
  | ~ P => 1 + length_ilf P
  | P \/ Q => 1 + length_ilf P + length_ilf Q
  | P /\ Q => 1 + length_ilf P + length_ilf Q     
  | P ~> Q => 1 + length_ilf P + length_ilf Q
  end.

Definition leb_ilf (A : iLF) (B : iLF) :=
  Nat.leb (length_ilf A) (length_ilf B).

Definition geb_ilf (A : iLF) (B : iLF) :=
  negb (Nat.leb (length_ilf A) (length_ilf B)).

Fixpoint GetAllSub_iLF (L : iLF) :=
  match L with
  | ! A => (! A)::nil
  | ~ A => (~ A)::(GetAllSub_iLF A)
  | A \/ B => (A \/ B)::((GetAllSub_iLF A)++(GetAllSub_iLF B))
  | A /\ B => (A /\ B)::((GetAllSub_iLF A)++(GetAllSub_iLF B))
  | A ~> B => (A ~> B)::((GetAllSub_iLF A)++(GetAllSub_iLF B))
  end.

Definition P := iAtom 23.
Definition Q := iAtom 24.
Definition R := iAtom 25.
Definition T := iAtom 26.

(* Van Dalen, p. 15. *)

Definition p1 := P ~> (~ (~ P)).
Definition p2 := (~ P) ~> (~ (~ (~ P))).
Definition p3 := ~ ( P /\ (~ P)).
Definition p4 := (~ (~ (P \/ (~ P)))).
Definition p5 := (~ (P \/ (Q)) <~> ((~ P) /\ (~ ( Q)))).
Definition p5_ida := (~ (P \/ (Q)) ~> ((~ P) /\ (~ ( Q)))).
Definition p6 := (P \/ (~ P)) ~> (~ (~ P) ~> P).
Definition p7 := (P ~> ( Q)) ~> (~ (P /\ (~ ( Q)))).
Definition p8 := (P ~> (~ ( Q))) <~> (~ (P /\ ( Q))).
Definition p8_ida := (P ~> (~ ( Q))) ~> (~ (P /\ ( Q))). 
Definition p9 := ((~ (~ P)) /\ (~ (~ ( Q)))) <~> (~ (~ (P /\ ( Q)))).
Definition p9_ida := ((~ (~ P)) /\ (~ (~ ( Q)))) ~> (~ (~ (P /\ ( Q)))).
Definition p10 := ((~ (~ P)) ~> (~ (~ ( Q)))) <~> (~ (~ (P ~> ( Q)))).
Definition p10_ida := ((~ (~ P)) ~> (~ (~ ( Q)))) ~> (~ (~ (P ~> ( Q)))).
Definition p11 := ((~ (~ P)) ~> ( Q)) ~> ((~ ( Q)) ~> (~ P)). 

(* OTHERS *)

(* An example of a classical but not intuitionistic 
tautology from a conversation with Rodolfo Ertola in 2020. *)
Definition p12 := (~ P ~> (Q \/ R)) ~> ((~P ~> Q) \/ (~ P ~> R)).

(***********************************)
(* Examples from Rodolfo's notes. *)
(* Propriedades do condicional  *)

Definition p13_l := Q.
Definition p13_r := P ~> Q.
Definition p13 := p13_l ~> p13_r.

Definition p14 := P ~> P. 

Definition p15_l := P.
Definition p15_r := (P ~> Q) ~> Q.
Definition p15 := p15_l ~> p15_r.

Definition p16_l := (P ~> Q) ~> P.
Definition p16_r := (P ~> Q) ~> Q.
Definition p16 := p16_l ~> p16_r.

Definition p17_l := P ~> (Q ~> R).
Definition p17_r := (P ~> Q) ~> (P ~> R).
Definition p17 := p17_l <~> p17_r.

Definition p18_l1 := (P ~> Q).
Definition p18_l2 := (Q ~> R).
Definition p18_r := (P ~> R).
Definition p18 := (p18_l1 /\ p18_l2) ~> p18_r.

Definition p19_l := P ~> (P ~> Q).
Definition p19_r := P ~> Q.
Definition p19 := p19_l <~> p19_r.

Definition p20_l := P ~> (Q ~> R).
Definition p20_r := Q ~> (P ~> R).
Definition p20 := p20_l <~> p20_r.

Definition p21_l := ((P ~> Q) ~> P) ~> ((Q ~> P) ~> Q).
Definition p21_r1 := ((P ~> Q) ~> Q) ~> Q.
Definition p21_r2 := ((P ~> Q) ~> P) ~> Q.
Definition p21_r3 := (Q ~> P) ~> (P ~> Q).
Definition p21_r4 := P ~> Q.
Definition p21 := p21_l <~> (p21_r1 /\ p21_r2 /\ p21_r3 /\ p21_r4).

Definition p22 := ((P ~> P) ~> P) ~> P.

Definition p23_c := ((P ~> Q) ~> P) ~> P. (* Lei de Peirce *)

Definition p024 := ((((P ~> Q) ~> P) ~> P) ~> Q) ~> Q. (* Lei de Wajsberg *)

Definition p24_l := (P ~> Q) ~> Q.
Definition p24_r := (Q ~> P) ~> P.
Definition p24_c := p24_l <~> p24_r.

Definition p25_l := P.
Definition p25_r := (P ~> Q) ~> P.
Definition p25_c := p25_r ~> p25_l.
Definition p25_i := p25_l ~> p25_r.

Definition p26_l := ((P ~> Q) ~> R) ~> R.
Definition p26_r := ((P ~> R) ~> R) ~> ((Q ~> R) ~> R).
Definition p26_c := p26_r ~> p26_l.
Definition p26_i := p26_l ~> p26_r.

Definition prop_Cond :=
  [
    p13;
    p14;
    p15;
    p16;
    p17;
    p18;
    p19;
    p20;
    p21;
    p22;
    p23_c;
    p024;
    p24_c;
    p25_c;
    p25_i;
    p26_c;
    p26_i
  ].

(* Propriedades conjuntas da conjunção e condicional *)

Definition p27_l := P ~> (Q /\ R).
Definition p27_r := (P ~> Q) /\ (P ~> R).
Definition p27 := p27_l <~> p27_r. (* Distributividade de ~> com respeito a /\ *)

Definition p28_l := (P /\ Q) ~> R.
Definition p28_r := P ~> (Q ~> R).
Definition p28 := p28_l <~> p28_r. (* Adjunção *)

Definition p29_l1 := P ~> R.
Definition p29_l2 := Q ~> T.
Definition p29_r := (P /\ Q) ~> (R /\ T).
Definition p29 := (p29_l1 /\ p29_l2) ~> p29_r.
                                     
Definition p30_l := P /\ (P ~> Q).
Definition p30_r:= P /\ Q.
Definition p30 := p30_l <~> p30_r.

Definition prop_ConjCond :=
  [
    p27;
    p28;
    p29;
    p30
  ].

(* Propriedades conjuntas da disjunção e o condicional *)

Definition p31_l := P ~> (Q \/ R).
Definition p31_r := (P ~> Q) \/ (P ~> R).
Definition p31_c := p31_l ~> p31_r.
Definition p31_i := p31_r ~> p31_l.

Definition p32_l := P \/ Q.
Definition p32_r := (P ~> Q) ~> Q.
Definition p32_c := p32_r ~> p32_l.
Definition p32_i := p32_l ~> p32_r.

Definition p33 := ((P \/ (P ~> Q)) ~> Q) ~> Q.

Definition p34_c := P \/ (P ~> Q).

Definition p35_c := (P ~> Q) \/ (Q ~> P).

Definition p36_l1 := P ~> Q.
Definition p36_l2 := R ~> T.
Definition p36_r := (P \/ R) ~> (Q \/ T).
Definition p36 := (p36_l1 /\ p36_l2) ~> p36_r.

Definition p37_l := (P \/ R) ~> (Q \/ T).
Definition p37_r := (P ~> Q) \/ (R ~> T).
Definition p37_c := p37_l ~> p37_r.

Definition p38_l := P \/ (P ~> Q).
Definition p38_r := ((P ~> Q) ~> P) ~> P.
Definition p38 := p38_l ~> p38_r.

Definition prop_DisjCond :=
  [
    p31_c;
    p31_i;
    p32_c;
    p32_i;
    p33;
    p34_c;
    p35_c;
    p36;
    p37_c;
    p38
  ].
  

(* Propriedades da conjunção, a disjunção e o condicional *)

Definition p39_l := (P /\ Q) ~> R.
Definition p39_r := (P ~> R) \/ (Q ~> R).
Definition p39_c := p39_l ~> p39_r.
Definition p39_i := p39_r ~> p39_l.

Definition p40_l := (P \/ Q) ~> R.
Definition p40_r := (P ~> R) /\ (Q ~> R).
Definition p40 := p40_l <~> p40_r.

Definition p41_l := (P ~> Q) /\ (Q ~> P).
Definition p41_r := (P \/ Q) ~> (P /\ Q).
Definition p41 := p41_l <~> p41_r.

Definition p42_l := (P \/ Q) /\ (P ~> Q).
Definition p42_r := Q.
Definition p42 := p42_l <~> p42_r.

Definition prop_ConjDisjCond :=
  [
    p39_c;
    p39_i;
    p40;
    p41;
    p42
  ].

(********)

(* Propriedades da conjunção *)

Definition p43_l := P /\ Q.
Definition p43_r := Q /\ P.
Definition p43 := p43_l <~> p43_r.
(* <->r *)
(* Comutatividade *)

Definition p44_l := P /\ (Q /\ R).
Definition p44_r := (P /\ Q) /\ R.
Definition p44 := p44_l <~> p44_r. 
(* <->r *)
(* Associatividade *)

Definition p45_l := P /\ P.
Definition p45_r := P.
Definition p45 := p45_l <~> p45_r. 
(* <->r *)
(* Idempotência *)

Definition p46_l := P /\ (P \/ Q).
Definition p46_r := P.
Definition p46 := p46_l ~> p46_r.
(* ->r *)
(* Semiabsorção *)

Definition prop_Conj :=
  [
    p43;
    p44;
    p45;
    p46
  ].

(* Propriedades da disjunção *)

Definition p47_l := P \/ Q.
Definition p47_r := Q \/ P.
Definition p47 := p47_l <~> p47_r.
(* <->r *)
(* Comutatividade *)

Definition p48_l := P \/ (Q \/ R).
Definition p48_r := (P \/ Q) \/ R.
Definition p48 := p48_l <~> p48_r. 
(* <->r *)
(* Associatividade *)

Definition p49_l := P \/ P.
Definition p49_r := P.
Definition p49 := p49_l <~> p49_r. 
(* <->r *)
(* Idempotência *)

Definition p50_l := P \/ (P /\ Q).
Definition p50_r := P.
Definition p50 := p50_r ~> p50_l. 
(* <-r *)
(* Semiabsorção *)

Definition prop_Disj :=
  [
    p47;
    p48;
    p49;
    p50
  ].

(* Propriedades conjuntas da conjunção e a disjunção *)

Definition p51_l := P /\ (P \/ Q).
Definition p51_r := P.
Definition p51 := p51_l <~> p51_r. 
(* <->r *)
(* Absorção 1 *)

Definition p52_l := P \/ (P /\ Q).
Definition p52_r := P.
Definition p52 := p52_r ~> p52_l.
(* <-r *)
(* Absorção 2 *)

Definition p53_l := P /\ (Q \/ R).
Definition p53_r := (P /\ Q) \/ (P /\ R).
Definition p53 := p53_r ~> p53_l.
(* <-r *)
(* Implicação distributiva 1 *)

Definition p54_l := P \/ (Q /\ R).
Definition p54_r := (P \/ Q) /\ (P \/ R).
Definition p54 := p54_l ~> p54_r. 
(* ->r *)
(* Implicação distributiva 2 *)

Definition p55_l := (P /\ Q) \/ (Q /\ R) \/ (R /\ P).
Definition p55_r := (P \/ Q) /\ (Q \/ R) /\ (R \/ P).
Definition p55 := p55_l ~> p55_r.
(* ->r *)
(* verificar parentesis *)
(* Implicação distributiva 3 *)

Definition p56_l := P /\ Q.
Definition p56_r := P \/ Q.
Definition p56 := p56_l ~> p56_r.
(* ->r *)

Definition prop_ConjDisj :=
  [
    p51;
    p52;
    p53;
    p54;
    p55;
    p56
  ].

(* Com distributividade *)

Definition p57_l := P /\ (Q \/ R).
Definition p57_r := (P /\ Q) \/ (P /\ R).
Definition p57_d := p57_l ~> p57_r.
Definition p57 := p57_r ~> p57_l.
(* <-r *)
(* ->d *)
(* Distributividade 1 *)

Definition p58_l := P \/ (Q /\ R).
Definition p58_r := (P \/ Q) /\ (P \/ R).
Definition p58_d := p58_r ~> p58_l.
Definition p58 := p58_l ~> p58_r. 
(* <-d *)
(* ->r *)
(* Distributividade 2 *)

Definition p59_l := (P /\ Q) \/ (Q /\ R) \/ (R /\ P).
Definition p59_r := (P \/ Q) /\ (Q \/ R) /\ (R \/ P).
Definition p59_d := p59_r ~> p59_l.
Definition p59 := p59_l ~> p59_r. 
(* <-d *)
(* ->r *)
(* Distributividade 3 *)

Definition p60_l := P /\ (Q \/ R).
Definition p60_r := (P /\ Q) \/ R.
Definition p60_d := p60_l ~> p60_r.
(* ->d *)
(* Distributividade 4 *)

Definition p61_l := (P \/ Q) /\ (R \/ T).
Definition p61_r := (P /\ R) \/ (Q \/ T).
Definition p61 := p61_l ~> p61_r.
(* ->d *)
(* Distributividade 5 *)

Definition prop_Distrib :=
  [
    p57_d;
    p57;
    p58_d;
    p58;
    p59_d;
    p59;
    p60_d;
    p61
  ].

Definition allClassicalTauto :=
  [
p23_c;
p24_c;
p25_c;
p26_c;
p31_c;
p32_c;
p34_c;
p35_c;
p37_c;
p39_c
  ].

Definition intuiTautos :=
  [
p25_i;
p25_i;
p31_i;
p32_i;
p39_i
  ].

Definition vanDalen :=
  [
p1;p2;p3;p4;p5;p6;p7;p8;p9;p10;p11
  ].
