(** * Fundamental set theory
Original file by Carlos Simpson (CNRS/UNSA)

Copyright INRIA (2009-2013 2018) Apics-Marelle Team (Jose Grimm).
*)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** ** Axioms *)
Module Axioms.

(** Some definitions *)

Definition fterm:= Set -> Set. 
Definition fterm2:= Set -> Set -> Set. 
Definition property := Set -> Prop.
Definition relation := Set -> Set -> Prop.
Definition reflexive_r (R: relation) := forall x, R x x.
Definition symmetric_r (R: relation) := forall x y, R x y -> R y x.
Definition transitive_r (R: relation) := forall y x z, R x y -> R y z -> R x z.
Definition antisymmetric_r (R: relation) := forall x y, R x y -> R y x -> x = y.
Definition singl_val (p: property):=
   forall x y, p x -> p y -> x = y.
Definition singl_val2 (p q: property):=
   forall x y, p x -> q x -> p y -> q y -> x = y.

Definition singl_val_fp (p: property) (f: fterm) :=
  forall x y, p x -> p y -> f x = f y.

Definition exactly_one (P Q: Prop) := (P \/ Q) /\ ~(P /\ Q).

Definition op_associative (op:fterm2) x y z := op x (op y z) = op (op x y) z.
Definition op_commutative (op:fterm2) x y := op x y = op y x.

(** This destructures a conjunction *)

Lemma proj31 A B C: [/\ A, B & C] -> A.
Proof. by destruct 1. Qed.
Lemma proj32 A B C: [/\ A, B & C] -> B.
Proof. by destruct 1. Qed.
Lemma proj33 A B C: [/\ A, B & C] -> C.
Proof. by destruct 1. Qed. 

Lemma proj31_1 A B C D : [/\ A, B & C] /\ D -> A. 
Proof. by move/proj1 /proj31. Qed.
Lemma proj32_1 A B C D : [/\ A, B & C] /\ D -> B. 
Proof. by move/proj1/proj32. Qed.


Lemma proj41 A B C D: [/\ A, B, C & D] -> A.
Proof. by destruct 1.  Qed.
Lemma proj42 A B C D: [/\ A, B, C & D] -> B.
Proof. by destruct 1.  Qed.
Lemma proj43 A B C D: [/\ A, B, C & D] -> C.
Proof. by destruct 1.  Qed.
Lemma proj44 A B C D: [/\ A, B, C & D] -> D.
Proof. by destruct 1.  Qed.

Lemma iff_sym (P Q: Prop): (P <-> Q) -> (Q <-> P).
Proof. exact: Logic.iff_sym. Qed.

Lemma iff_trans (P Q R: Prop): (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof. exact: Logic.iff_trans.  Qed.

Lemma iff_neg (P Q: Prop): (P <-> Q) -> ( ~ P <->  ~ Q).
Proof. by move => h; split => np q; case: np; apply/h. Qed.


(** Realisation: if [x] is a set, [Ro] maps an object of type [x] to a set *)

Parameter Ro : forall x : Set, x -> Set.
(** Injectivity of [Ro] *)

Axiom R_inj : forall (x : Set), injective (@Ro x).

(** Defines [inc] as "is element of" and [sub] as "is subset of" *)

Definition inc (x y : Set) := exists a : y, Ro a = x.
Definition sub (x y : Set) := forall z : Set, inc z x -> inc z y.
Definition ssub (x y : Set) :=  (sub x y) /\ (x <> y).
(** Extensionality for sets *)

Axiom extensionality : antisymmetric_r sub.


(** Axiom of choice: let [t] be a nonempty type, [p] a predicate on [t].
 If [p] is true for some object it is for  [(chooseT p ne)]. *)

Section Choose.
Variable (t : Type).
Implicit Type (p : t -> Prop)  (q:inhabited t).

Parameter chooseT : forall p q,  t.
Axiom chooseT_pr : forall p q, ex p -> p (chooseT p q).

End Choose.

(** Image: if [f:x -> Set] is an abstraction, then [IM f] is a set,
   it contains [y] if and only if [y] is [(f z)] for some [z:x]. *)

Parameter IM : forall (x : Set) (f : x -> Set), Set.

Axiom IM_P :  forall (x : Set) (f : x -> Set) (y : Set),
          inc y (IM f) <-> exists a : x, y = f a.

(** Excluded middle and consequences. *)

Axiom p_or_not_p: forall P:Prop,  P \/ ~ P.

Lemma ixm (P: Prop): P + (~P).
Proof.
apply: (chooseT (fun _ => True)).
by case: (p_or_not_p P) => H;constructor; [ left | right ].
Qed.

Ltac ex_middle u := match goal with
  | |- ?p => case: (p_or_not_p p) ; [ done | move => u ]
end.

Lemma excluded_middle (p:Prop): ~ ~ p -> p.
Proof. move => nnp; ex_middle np;case: (nnp np). Qed.

Lemma equal_or_not (x y: Set) :  x = y \/ x <> y.
Proof. apply: p_or_not_p. Qed.

Ltac alt_tac v:= match goal with 
 | |- ?a = ?b \/ _ 
     => case: (equal_or_not a b); [by left | move=> v; right ]
 end.


Lemma inc_or_not (x y:Set): inc x y \/ ~ (inc x y).
Proof. apply: p_or_not_p.  Qed.

Ltac dneg u := match goal with 
  H : ~ _ |- ~ _ => move => u; apply:H
end.

Ltac in_TP4:= solve [by constructor 1 | by constructor 2 |
   by constructor 3 |  by constructor 4]. 

End Axioms.
Export Axioms.

(** ** Tactics *)
Module Tactics1.


(** Tatics like [aw] use autorewite and trivial;
  tactics like [fprops] use auto  *)
Ltac fprops := auto with fprops.

Ltac aw := autorewrite with aw.
Ltac aww := aw; fprops.
Ltac saw := split; aw; trivial.
Ltac bw := autorewrite with  bw.


Ltac set_extens v:= apply: extensionality=> v.

Ltac ue := 
  match goal with
    | H:?a = ?b |- _ => solve [ rewrite  H ; fprops | rewrite - H ; fprops] 
end.

End Tactics1.
Export Tactics1.

(** ** Constructions *)

Module Constructions.

Lemma sub_trans: transitive_r sub.
Proof. move => b a c sab sbc t ta; apply: sbc; exact: sab. Qed.

Lemma sub_refl: reflexive_r sub.
Proof. by move => x y. Qed. 

Lemma ssub_trans1 b a c: ssub a b -> sub b c -> ssub a c.
Proof.
move => [sab nab] sbc; split; first by apply: (sub_trans sab).
by dneg ac;apply: (extensionality sab); rewrite ac.
Qed.

Lemma ssub_trans2 b a c: sub a b -> ssub b c -> ssub a c.
Proof. 
move => sab [sbc nbc]; split; first by apply: (sub_trans sab).
by dneg ac;apply: (extensionality sbc); rewrite -ac.
Qed.

(** [emptyset] is a type without constructor; [empty] is classical. *)

Definition empty (x : Set) := forall y : Set, ~ inc y x. 
Definition nonempty (x: Set) := exists y: Set, inc y x.
CoInductive emptyset : Set :=. 

(** Basic property of [Ro]. *)

Lemma R_inc (x : Set) (a : x): inc (Ro a) x.
Proof. by exists a. Qed.

(** Equivalence between [nonempty] and [~ empty]. *)


Lemma in_set0 x: ~ inc x emptyset.
Proof. move=> [[]]. Qed.

Lemma set0_P x: empty x <-> x = emptyset.
Proof.
split; last by move => -> y /in_set0.
by move => Iyx; set_extens t => Ht; [ case: (Iyx t) | case: (in_set0 Ht) ].  
Qed.

Lemma emptyset_dichot x: x = emptyset \/ nonempty x.
Proof. 
case: (p_or_not_p (nonempty x)); [ by right | move => nex; left].
by apply /set0_P => t tx; case: nex; exists t.
Qed.

Lemma nonemptyP x: nonempty x <-> (x <> emptyset).
Proof.
split => xne; last by case: (emptyset_dichot x) => // ->.
move => xe; case: xne; rewrite xe; exact:in_set0.
Qed.

Lemma sub0_set x : sub emptyset x.
Proof. by move=> t /in_set0. Qed.

Hint Resolve sub0_set sub_refl : fprops.

Lemma sub_set0 x: sub x emptyset <-> (x = emptyset).
Proof.  
split;move => h; [ by apply/set0_P => t /h/in_set0 | ue].
Qed.

(** Axiom of choice applied to [(inc x y)], and the property [(P a)]
 that says realisation of [a] is [x]: This gives a partial inverse of [Ro]. *)

Definition Bo (x y : Set) (Hxy : inc x y) :=
 chooseT (fun a : y => Ro a = x)
    (match Hxy with | ex_intro w _ => inhabits w end).

Lemma B_eq x y (Hxy : inc x y): Ro (Bo Hxy) = x.
Proof. apply: chooseT_pr Hxy. Qed.

Lemma B_back  (x:Set) (y:x) (hyp : inc (Ro y) x): Bo hyp = y.
Proof. by apply: R_inj; apply: B_eq. Qed.

(** Genereralised axiom of choice. [choose p] is satisfied by [p]
   if somebody satisfies [p] *)

Definition choose (p: property) := chooseT p (inhabits emptyset).

Lemma choose_pr (p: property): ex p -> p (choose p).
Proof. by apply: chooseT_pr. Qed.

(** Axiom of choice applied to [inc]. If [x] not empty, [rep x] is in [x]. *)

Definition rep (x : Set) := choose (fun y : Set => inc y x). 

Lemma rep_i x: nonempty x -> inc (rep x) x. 
Proof. by move => [y iyx]; apply: (choose_pr (p:= inc ^~ x)); exists y. Qed.

(** Given a function [f], [Zorec] remembers [a] and [f a] *)

CoInductive Zorec (x : Set) (f : x -> Prop) : Set :=
  Zorec_c :forall (a: x), f a -> Zorec f.

Definition Zo (x:Set) (p:property) :=
  IM (fun  (z : Zorec (fun (a : x) => p (Ro a))) => let (a, _) := z in Ro a).

Lemma Zo_i x (p:property) y: inc y x -> p y -> inc y (Zo x p).
Proof. 
rewrite /Zo => -[a Roa]; rewrite -{1} Roa => py.
by apply/ IM_P; exists (Zorec_c (f:= (fun a : x => p (Ro a))) py).  
Qed.

Lemma Zo_hi x (p: property) y: inc y (Zo x p) -> p y.
Proof. by case /IM_P => v ->; case:v.  Qed.

Lemma Zo_S x (p: property): sub (Zo x p) x.
Proof. move=> y /IM_P [v ->];case:v => z _; apply: R_inc. Qed.

Lemma Zo_P x (p: property) y: inc y (Zo x p) <-> (inc y x /\ p y).
Proof.
split=> [H | [u v]]; last by apply: Zo_i.
split; [ exact: (Zo_S H) | exact: (Zo_hi H) ].
Qed.

Lemma Zo_exten1 (X : Set) (p q: property):
   (forall x, inc x X -> (p x <-> q x)) -> Zo X p = Zo X q.
Proof.
by move => h; set_extens t => /Zo_P [pa /(h _ pa) pb];apply: Zo_i. 
Qed.

Lemma Zo_exten2 (X Y: Set) (p q: property):
   (forall x, (inc x X /\ p x <-> inc x Y /\ q x)) -> Zo X p = Zo Y q.
Proof.
by move => h; set_extens t => /Zo_P pa; apply/Zo_P /h.
Qed.


Lemma all_exists_dichot1 (p: property) X:
  (forall x, inc x X -> p x) \/ (exists2 x, inc x X & ~p x).
Proof.
case: (emptyset_dichot (Zo X (fun z => ~ p z))).
  move => ze;left => x xX; ex_middle bad; case:(@in_set0 x).
  by rewrite - ze; apply: Zo_i.
by move => [x /Zo_P[ga gb]]; right; exists x.
Qed.

Lemma all_exists_dichot2 (p: property) X:
  (forall x, inc x X -> ~ p x) \/ (exists2 x, inc x X & p x).
Proof.
case: (all_exists_dichot1 (fun z => ~ p z) X); [by left | move => h; right].
by case: h => x xE px; exists x => //; apply: excluded_middle.
Qed.

End Constructions.

Export Constructions.

(** ** Little*)
Module Little.

Definition doubleton (x y : Set) :=
  IM (fun z:bool => if z then x else y).

Lemma set2_1 x y: inc x (doubleton x y).
Proof. by apply /IM_P; exists true. Qed.

Lemma set2_2 x y : inc y (doubleton x y).
Proof. by apply /IM_P; exists false. Qed.

Lemma set2_hi z x y: inc z (doubleton x y) -> z = x \/ z = y.
Proof. by move/IM_P => [][]; [left | right]. Qed.

Hint Resolve set2_1 set2_2: fprops.

Lemma set2_P z x y : inc z (doubleton x y) <-> (z = x \/ z = y).
Proof. split; [apply: set2_hi | by case => ->; fprops]. Qed.

Lemma doubleton_inj  x y z w:
  doubleton x y = doubleton z w -> (x = z /\ y = w) \/ (x = w /\ y = z). 
Proof.
move=> eql. 
have x_zw: inc x (doubleton z w) by rewrite -eql; fprops.
have y_zw: inc y (doubleton z w) by rewrite -eql; fprops.
have w_xy: inc w (doubleton x y) by rewrite eql; fprops.
have z_xy: inc z (doubleton x y) by rewrite eql; fprops.
case: (set2_hi x_zw) => xs.
  left; split => //; case: (set2_hi w_xy) => //.
  by case: (set2_hi y_zw); move: xs => -> ->.
case: (set2_hi y_zw);first by right.
by case: (set2_hi z_xy); move => -> ->; left.
Qed.

Lemma set2_ne x y: nonempty (doubleton x y).
Proof. by exists x; fprops. Qed.

Lemma sub_set2 x y z: inc x z -> inc y z -> sub (doubleton x y) z.
Proof. by move=> xz yz t /set2_P [] ->. Qed.

Lemma set2_C : commutative doubleton.
Proof. 
move => a b; apply:extensionality; apply/sub_set2 /set2_P;fprops.
Qed.

Lemma set2_pr a b X:
  inc a X -> inc b X ->
  (forall z, inc z X -> z = a \/ z = b) ->
  X = doubleton a b.
Proof.
move => ax bx h; set_extens t; first by move => ta; apply /set2_P /h.
by case /set2_P => ->.
Qed.


(** [singleton x] is a set with one element *)

Definition singleton (x : Set) := doubleton x x.

Lemma set1_eq x y: inc y (singleton x) -> y = x.
Proof. by case/set2_P. Qed.

Lemma set1_1 x: inc x (singleton x).
Proof. by apply/set2_P;left. Qed.

Hint Resolve set1_1: fprops.

Lemma set1_P y x: inc y (singleton x) <-> (y = x).
Proof. by split; [ apply:set1_eq| move => ->; fprops ]. Qed.

Lemma set1_inj: injective singleton. 
Proof. by move => x y eq; apply: set1_eq; rewrite -eq; fprops. Qed.

Lemma set1_ne x: nonempty (singleton x).
Proof. by apply: set2_ne. Qed.

Lemma set1_sub x X: inc x X -> sub (singleton x) X.
Proof. by move=> ixy; apply: sub_set2. Qed.

Hint Resolve set1_ne: fprops.

Definition C0 := emptyset.
Definition C1 := singleton C0.
Definition C2 := doubleton C0 C1. 

Lemma C1_P x:  inc x C1 <-> x = C0.
Proof. exact: set1_P. Qed.

Lemma C1_ne_C0: C1 <> C0.
Proof. by apply /nonemptyP; exists C0; apply: set1_1. Qed.

Lemma C0_ne_C1: C0 <> C1.
Proof. exact: nesym C1_ne_C0. Qed.

Lemma C2_P x: inc x C2 <-> (x = C0 \/ x = C1).
Proof. exact: set2_P. Qed.

Lemma inc_C0_C2: inc C0 C2.
Proof. exact: set2_1. Qed. 

Lemma inc_C1_C2: inc C1 C2.
Proof. exact: set2_2. Qed.

Hint Resolve C0_ne_C1 C1_ne_C0: fprops.
Hint Resolve inc_C0_C2 inc_C1_C2: fprops.


Definition alls (X: Set)(P: property) := forall a, inc a X -> P a.

(** A set is small if it has zero or one elements *)
(** [singletonp x]  says [x] has the form [singleton y] *)
Definition small_set (x:Set) := singl_val (inc ^~x).
Definition singletonp (x:Set) := exists u, x = singleton u.
Definition doubletonp (x:Set) := exists a b, a <> b /\ x = doubleton a b.

Lemma small0: small_set emptyset.
Proof. by move=> u v /= /in_set0. Qed.

Lemma small1 x: small_set (singleton x).
Proof. by move=> u v /set1_P -> /set1_P ->. Qed.

Lemma set1_pr x X: inc x X -> alls X (eq^~ x) -> X = singleton x.
Proof. 
move=> xX zy; set_extens t; first by move => ty;apply/set1_P;apply: zy.
by move /set1_P ->. 
Qed.

Lemma set1_pr1 x X: nonempty X ->  alls X (eq^~ x) -> X = singleton x.
Proof.
by move=> [y yx] p; apply: set1_pr => //; rewrite - (p _ yx).
Qed.

Lemma singletonP x: singletonp x <-> (nonempty x /\ small_set x).
Proof. 
split; first by move=> [z ->]; split;[fprops | apply: small1].
by move=> [[y yx] sx]; exists y; apply: (set1_pr yx) => z zx; apply: sx.
Qed.

Lemma small_set_pr x: small_set x -> x = emptyset \/ singletonp x.
Proof. 
move=> sx; case: (emptyset_dichot x); first by left.
by move=> ne; right; apply/singletonP.
Qed.

Lemma subset1P X x : sub X (singleton x) <-> (X = emptyset \/ X = singleton x).
Proof.
split; last by case => ->; fprops. 
move => xsx; case: (emptyset_dichot X); first by left.
by move => nea; right; apply: set1_pr1 => // z /xsx /set1_P.
Qed.
 
Lemma sub1setP X x : sub (singleton x) X <-> inc x X.
Proof. by split; [ apply; fprops | move => xX t /set1_P ->]. Qed.

End Little.

Export Little. 


(** ** Image *)
Module Image. 

(** Image of a set by a function *)

Definition fun_image (x : Set) (f : fterm) := IM (fun a : x => f (Ro a)). 

Lemma funI_i x f y: inc y x -> inc (f y) (fun_image x f).
Proof. by move => yx; apply/IM_P; exists (Bo yx); rewrite (B_eq yx). Qed.

Lemma funI_P f x y:
  inc y (fun_image x f) <-> exists2 z, inc z x & y = f z.
Proof. 
split; last by move=> [a ax ->]; apply:funI_i.
case/IM_P => a ->; exists (Ro a) => //; apply: R_inc.
Qed.

End Image.
Export Image.

(** ** Complement *)
Module Complement. 

(** Set of all elements in a not in b *)

Definition complement (A B : Set) := Zo A (fun x : Set => ~ inc x B).
Notation "a -s b" := (complement a b) (at level 50).

Lemma setC_P A B x: inc x (A -s B) <-> (inc x A /\ ~ inc x B).
Proof. exact: Zo_P. Qed.

Lemma setC_i x A B: inc x A -> ~ inc x B -> inc x (A -s B).
Proof. by move => xa xb; apply /setC_P. Qed.

Hint Resolve  setC_i: fprops.

Lemma nin_setC x A B: inc x A -> ~ inc x (A -s B) -> inc x B.
Proof. move=> xa nx_cab; ex_middle h; case: nx_cab; fprops. Qed.

Lemma empty_setC A B: A -s B = emptyset -> sub A B.
Proof.  
move=> eql t ta; apply:(nin_setC ta); rewrite eql; apply: in_set0.
Qed. 

Lemma setC_T A B: sub A B -> A -s B = emptyset.
Proof. 
by move => sab; apply /set0_P => x /setC_P [xa] []; apply: sab.
Qed.

Lemma sub_setC A B: sub (A -s B) A.
Proof. by move => t;case /setC_P. Qed. 

Lemma setC_ne A B: ssub A B -> nonempty (B -s A).
Proof. 
move=> [s neq]; apply /nonemptyP;dneg ceq; move: (empty_setC ceq).
by apply: extensionality.
Qed. 

Lemma setC_K A B: sub A B -> B -s (B -s A) = A.
Proof. 
move=> sax; set_extens t.
  by move /setC_P => [tx /setC_P notp];ex_middle h; case: notp.
move =>ta; apply/setC_P; split; [apply: (sax _ ta) | by apply/setC_P; case ].
Qed.

Lemma setC_v A: A -s A = emptyset.
Proof. by apply:setC_T. Qed. 

Lemma setC_0 A: A -s emptyset = A.
Proof. 
apply: extensionality; first by apply:sub_setC.
move => y yA; apply/setC_P; split => //;apply /in_set0.
Qed.

Lemma set_SC A B C : sub A B -> sub (A -s C) (B -s C).
Proof.
by move => sab x /setC_P [xa xnc]; apply /setC_P;split =>//; apply: sab.
Qed.

Lemma set_CS A B C : sub A B -> sub (C -s B) (C -s A).
Proof.
move => sac t/setC_P [tc ntb]; apply /setC_P.
by split => //;dneg ta; apply: sac.
Qed.

Lemma set_CSS A B C D : sub A C -> sub D B -> sub (A -s B)(C -s D).
Proof. move => sAC sDB; apply: (sub_trans (set_CS sDB) (set_SC sAC)). Qed.

Lemma set_CSm A B X:
  sub A X -> sub B X -> (sub A B <-> sub (X -s B) (X -s A)).
Proof.
move=> ax bx; split; first by apply: set_CS.
by move => h; rewrite -(setC_K ax) -(setC_K bx); apply: set_CS.
Qed.

Lemma subsetC_P A B E : sub A E -> sub B E ->
  (sub A (E -s B) <-> sub B (E -s A)).
Proof.
move => aE bE;split => i1 t ts;apply/setC_P; split.
- by apply bE.
- by move /i1 => /setC_P; case.
- by apply aE.
- by move /i1 => /setC_P; case.
Qed.

Lemma subCset_P A B E: sub A E -> sub B E ->
  (sub (E -s A) B <-> sub (E -s B) A).
Proof. 
move => ae be; rewrite -{2} (setC_K ae) -{1} (setC_K be).
apply: subsetC_P; apply: sub_setC.
Qed.

(** [a -s1 b] contains all elements of [a] but [b] *)

Notation "a -s1 b" := (a -s (singleton b))  (at level 50). 

Lemma setC1_P x A b: inc x (A -s1 b) <-> (inc x A /\ x <> b).
Proof. 
split; first by case /setC_P => xa /set1_P xb. 
by move => [xA xb]; apply /setC_P; split => //;apply /set1_P.
Qed.

Lemma setC1_1 x A: ~ (inc x (A -s1 x)).
Proof. by apply /setC_P=> [[_]] /set1_P. Qed.

Lemma setC1_proper A x : inc x A -> ssub (A -s1 x) A.
Proof.
move => xa; split; first by apply: sub_setC.
move => eq1; move: xa; rewrite -eq1; exact: setC1_1.
Qed.

Lemma setC1_eq A x: ~(inc x A) -> A -s1 x = A.
Proof.
move=> h.
set_extens t; first by move => /setC1_P [].
by move => tA; apply /setC1_P; split => // tx; case: h; rewrite - tx.
Qed.


End Complement.
Export Complement.

(** ** Union *)
Module Union. 

(** Uaux: like Zo_rec, but f has a different type. *)

Section UnionDef.
Variable (I:Set)(f : I->Set).

CoInductive Uaux : Set := Uaux_c : forall a:I, f a -> Uaux.

Definition uniont := 
   IM (fun a : Uaux  => (let:  Uaux_c u v := a in @Ro (f u) v)). 
End UnionDef.

Lemma setUt_P (I:Set) (f:I->Set) x:
  inc x (uniont f) <-> exists z, inc x (f z).
Proof. 
split; first by move/IM_P=>[a ->]; case: a => b fb; exists b; apply: R_inc.
by move => [z xf]; apply /IM_P;exists (Uaux_c (Bo xf)); rewrite B_eq. 
Qed.

Definition union (X: Set) := uniont (@Ro X). 

Lemma setU_P z x:
  inc x (union z) <-> exists2 y, inc x y & inc y z.
Proof. 
split; first by move/setUt_P => [y xr]; exists (Ro y); [ | apply: R_inc].
by move => [y xy yz]; apply/setUt_P; exists (Bo yz); rewrite (B_eq yz).
Qed. 

Lemma setU_i x y z: inc x y -> inc y z -> inc x (union z).
Proof. by move => xy yz; apply/setU_P; exists y. Qed.

Lemma setU_hi x z: inc x (union z) -> exists2 y, inc x y & inc y z.
Proof. by case /setU_P => t pt; exists t. Qed.

Lemma setU_s1 y z: inc y z -> sub y (union z).
Proof. by move=> yz x xy ; apply: setU_i yz. Qed.

Lemma setU_s2 x z: (forall y, inc y z -> sub y x) -> sub (union z) x.
Proof. by move=> H t /setU_P [a ta /H]; apply. Qed. 

Lemma setU_0: union emptyset = emptyset.
Proof. by apply /set0_P => x /setU_P [y _ /in_set0]. Qed.

(** Union of two sets *)

Definition union2 (x y : Set) := union (doubleton x y).

Notation "a \cup b" := (union2 a b) (at level 50).

Lemma setU2_hi x A B: inc x (A \cup B) -> inc x A \/ inc x B.
Proof. by case /setU_P => t tab /set2_P [] <-; [left | right]. Qed.

Lemma setU2_1 x A B: inc x A -> inc x (A \cup B).
Proof. move => xa; apply (setU_i xa); fprops. Qed.

Lemma setU2_2 x A B: inc x B -> inc x (A \cup B).
Proof. move => xb;apply: (setU_i xb); fprops. Qed.

Hint Resolve setU2_1 setU2_2: fprops.

Lemma setU2_P x A B: inc x (A \cup B) <-> (inc x A \/ inc x B).
Proof. by split; [apply: setU2_hi | case; fprops ]. Qed. 

Lemma subsetU2l A B: sub A (A \cup B).
Proof. move => x; fprops. Qed.

Lemma subsetU2r A B: sub B (A \cup B).
Proof. move => x; fprops. Qed.

Lemma setU2_C: commutative union2.
Proof. 
move => x y; set_extens t; case/setU2_P => ts; apply /setU2_P; fprops.
Qed.

Lemma setU2_id: idempotent union2.
Proof. move => x;set_extens t; [ by case /setU2_P | fprops]. Qed.

Lemma setU2_A: associative union2.
Proof.
move => a b c; rewrite setU2_C.
set_extens t; case /setU2_P; (try case /setU2_P); move => tx;
   apply/setU2_P;fprops; left; apply/setU2_P;fprops. 
Qed.

Lemma setU2_CA : left_commutative union2.
Proof. by move =>A B C; rewrite !setU2_A (setU2_C B). Qed.

Lemma setU2_AC : right_commutative union2.
Proof. by move => A B C;rewrite -!setU2_A (setU2_C B). Qed.


Lemma setU2_ACA: interchange union2 union2.
Proof. by move => A B C D; rewrite -! setU2_A (setU2_CA B). Qed.
  
Lemma set2_UUl : left_distributive union2 union2.
Proof.
by move => A B C; rewrite setU2_A !(setU2_AC _ C) -(setU2_A _ C) setU2_id.
Qed.

Lemma set2_UUr : right_distributive union2 union2.
Proof. move => a b c; rewrite !(setU2_C a); exact: set2_UUl. Qed.

Lemma setU2_S1 A B C : sub A B -> sub (C \cup A) (C \cup B).
Proof. move=> sAB t; case /setU2_P => ts; apply/setU2_P; fprops. Qed.

Lemma setU2_S2 A B C : sub A B -> sub (A \cup C) (B \cup C).
Proof. by move=> sAB; rewrite -!(setU2_C C); exact: setU2_S1. Qed.

Lemma setU2_SS A B C D : sub A C -> sub B D -> sub (A \cup B) (C \cup D).
Proof.  
move => s1 s2; apply: sub_trans (setU2_S1 (C:=C) s2); apply: (setU2_S2 s1).
Qed.

Lemma setU2_12S A B C: sub A C -> sub B C -> sub (A \cup B) C.
Proof. rewrite -{3}(setU2_id C); exact:setU2_SS. Qed.

Lemma subU2_setP A B C : (sub (B\cup C) A) <-> (sub B A /\ sub C A).
Proof. 
split. 
  move => h;split; apply: (sub_trans _ h);[apply: subsetU2l |apply: subsetU2r].
by move => [h1 h2];apply: setU2_12S.
Qed.

Lemma sub_setU2 A B C : (sub A B) \/ (sub A C) -> sub A (B \cup C).
Proof. 
case => h; apply: (sub_trans h);[apply: subsetU2l |apply: subsetU2r].
Qed.

Lemma setU2id_Pl A T: sub A T <-> A \cup T = T.
Proof. 
split; last by move => <-;apply: subsetU2l.
move => sat; apply: extensionality; last by apply: subsetU2r.
by rewrite - {2}(setU2_id T); apply:setU2_S2.  
Qed.

Lemma setU2id_Pr A T: sub A T <-> T \cup A = T.
Proof. rewrite setU2_C; exact: setU2id_Pl. Qed.

Lemma setU2_0 A : A \cup emptyset  = A.
Proof. apply/setU2id_Pr; fprops. Qed.

Lemma set0_U2 A : emptyset \cup A = A.
Proof. rewrite setU2_C; exact: setU2_0. Qed.

Lemma setU_1 x: union (singleton x) = x.
Proof. apply: setU2_id. Qed.

Lemma setU2_11 x y: (singleton x) \cup (singleton y) = doubleton x y.
Proof. apply:set2_pr; fprops => z /setU2_P [] /set1_P ->; fprops. Qed.

Lemma subCset_P2 A B C : sub (A -s B) C <-> sub A (B \cup C).
Proof.
split => h t.
  move => ta; apply/setU2_P; case: (inc_or_not t B) => ax; [by left | right].
  by apply:h; apply/setC_P.
by case /setC_P => ta tb; case/setU2_P: (h _ ta). 
Qed.

Lemma setU2_eq0P A B : (A \cup B = emptyset) <-> (A = emptyset /\ B = emptyset).
Proof. 
split; [move => sube | by  move => [-> ->]; rewrite setU2_id ].
split;  apply /set0_P => t ta;case: (in_set0 (x:= t));
  rewrite - sube; apply /setU2_P;fprops.
Qed.

Lemma setU2Cr1 A B:  A \cup (A -s B) = A.
Proof. apply /setU2id_Pr; apply: sub_setC. Qed.

Lemma setU2Cr2 A B:  A \cup (B -s A) = A \cup B.
Proof. 
set_extens t; case /setU2_P => t1; apply/setU2_P; fprops. 
  by right;case /setC_P:t1.
case: (inc_or_not t A)=> ta; fprops.
Qed.

Lemma setU2_Cr A T: sub A T -> A \cup (T -s A) = T.
Proof. by move => sat; rewrite setU2Cr2; apply /setU2id_Pl. Qed.


(** Union of [x] and a single element [y] *)

Notation "A +s1 b" := (A \cup (singleton b)) (at level 50).  

Lemma setU1_P A b z: inc z (A +s1 b) <-> inc z A \/ z = b.
Proof. 
split; first by case /setU2_P; [left | move /set1_P; right].
by case =>h; apply/setU2_P; [by left | right; apply/set1_P].
Qed.

Lemma setU1_1 A b: inc b (A +s1 b).
Proof. by apply/setU1_P; right. Qed.

Lemma sub_setU1 A b: sub A (A +s1 b).
Proof. by move=> x xA; apply/setU1_P; left. Qed.

Lemma setU1_r A b x: inc x A -> inc x (A +s1 b).
Proof. apply: sub_setU1. Qed.

Hint Resolve setU1_1 setU1_r sub_setU1: fprops.

Lemma setU1_eq A b: inc b A -> A +s1 b = A.
Proof. 
move=> ba; apply: extensionality; last by fprops.
by move => t /setU1_P [] // ->.
Qed.

Lemma setU1_sub A b x: sub A x -> inc b x -> sub (A +s1 b) x.
Proof. by move=> Ax bx t /setU1_P []; [ apply: Ax | move=> -> ]. Qed.

Lemma setCU_K A B: sub B A <-> (A -s B) \cup B = A.
Proof.
split; last by move => h t tb; rewrite -h; apply/setU2_P; right.  
move => BA; set_extens t; first by case /setU2_P; [ by case/setC_P| apply: BA].
move => tA; apply/setU2_P; case: (inc_or_not t B) => ty;fprops. 
Qed.

Lemma setU1_K A b: ~(inc b A) -> (A +s1 b) -s1 b = A.
Proof.
move => nba; set_extens t;first by case /setC1_P; case /setU1_P.
move => tA; apply/setC1_P; split; [fprops | dneg ta;ue ].
Qed.

Lemma setC1_K A b: inc b A -> (A -s1 b) +s1 b = A.
Proof. by move => bA; apply/setCU_K => t /set1_P ->. Qed.

Lemma setU1_inj x A B: ~(inc x A) -> ~(inc x B) ->
  A +s1 x = B +s1 x -> A = B.
Proof. by move => /setU1_K -{2} <- /setU1_K -{2} <- ->. Qed.

Lemma setC1_inj x A B: inc x A -> inc x B -> A -s1 x = B -s1 x -> A = B.
Proof. by move => /setC1_K - {2} <- /setC1_K -{2} <- ->. Qed.

Definition tripleton a b c := (doubleton a b) +s1 c. 

Lemma set3_P a b c x:
   inc x (tripleton a b c) <-> [\/ x = a , x = b | x = c].
Proof.
split; last by rewrite /tripleton;case => ->; fprops.
case /setU1_P; [case /set2_P | ]; in_TP4.
Qed.


Definition C3 := C2 +s1 C2.
Definition C4 := C3 +s1 C3.

Lemma C3_P x: inc x C3 <-> [\/ x = C0, x = C1 | x = C2].
Proof. exact:set3_P. Qed.

Lemma C4_P x: inc x C4 <-> [\/ x = C0, x = C1, x = C2 | x = C3].
Proof.
split.
  case /setU1_P; last (by constructor 4); by case /C3_P; in_TP4.
case => ->; apply/setU1_P; last (by right); left; apply /C3_P; in_TP4.
Qed.

Lemma C2_ne_C01: C2 <> C0 /\ C2 <> C1.
Proof.
split => h; first by move: inc_C0_C2; rewrite h /C0; case; case.
move: inc_C1_C2; rewrite h; move /set1_P; fprops.
Qed.

Lemma C3_ne_C012: [/\ C3 <> C0, C3 <> C1 & C3 <> C2].
Proof.
have pa: inc C0 C3 by apply/C3_P; constructor 1.
have pb: inc C1 C3 by apply/C3_P; constructor 2.
have pc: inc C2 C3 by apply/C3_P; constructor 3.
move:C2_ne_C01 => [pd pe].
split => h; first by move: pa ; rewrite h; case; case.
  by move: pb ; rewrite h; move/set1_P; fprops.
move: pc; rewrite h; case/set2_P; fprops.
Qed.


Lemma funI_set0 f: fun_image emptyset f = emptyset.
Proof. by apply /set0_P => t /funI_P [z /in_set0]. Qed.

Lemma funI_setne1 f x: fun_image x f = emptyset -> x = emptyset.
Proof.
by move => dr;apply /set0_P => t /(funI_i f); rewrite dr => /in_set0.
Qed.

Lemma funI_setne f x: nonempty x ->  nonempty (fun_image x f).
Proof. by move/nonemptyP => xE; apply/nonemptyP=> /funI_setne1. Qed.

Lemma funI_set2 f a b: fun_image (doubleton a b) f = doubleton (f a) (f b).
Proof. 
set_extens t; first by move/funI_P => [z] /set2_P;case => -> <-; fprops.
move /set2_P; case => ->; apply: funI_i; fprops.
Qed.

Lemma funI_set1 f x: fun_image  (singleton x) f = singleton (f x).
Proof. apply:funI_set2. Qed.

Lemma funI_setU f X: 
   fun_image (union X) f = union (fun_image X (fun_image^~ f)).
Proof.
set_extens t.
  move /funI_P => [y /setU_P[x yx xz] ->].
  by apply/setU_P; exists (fun_image x f); apply:funI_i.
move/setU_P => [x tx /funI_P [y yz dy]].
move:tx; rewrite dy; move/funI_P => [u ua ->]; apply: funI_i.
apply (setU_i ua yz).
Qed.

Lemma funI_setU2 f: {morph (fun_image ^~ f): x y / x \cup y}.
Proof. by move => x y;rewrite /union2 funI_setU funI_set2. Qed.

Lemma funI_setU1 g X a:
   fun_image (X +s1 a) g = fun_image X g +s1 (g a).
Proof. by rewrite funI_setU2 funI_set1. Qed.

Lemma funI_S f a b: sub a b -> sub (fun_image a f) (fun_image b f).
Proof. by move => h t /funI_P [z za ->]; apply: funI_i; apply: h. Qed.

(** If a set [E] contains a unique [x] satisfying [p], then [select p E] is this element 
*)
Definition select (p: property) (E: Set) := union (Zo E p).


Lemma select_uniq (p: property) E: 
  (singl_val2 (inc ^~ E) p) ->
  forall x, inc x E -> p x -> x = (select p E).
Proof.
move => h x xE px; rewrite /select.
suff: (Zo E p) = singleton x by move => ->; rewrite setU_1.
by apply: set1_pr; [ apply: Zo_i | move => z; case/Zo_P => ze pz; apply: h].
Qed.

Lemma select_pr (p : property) E:
  (exists2 x, inc x E & p x) -> (singl_val2 (inc ^~ E) p) ->
  (p (select p E) /\ inc (select p E) E).
Proof. by move => [z ze pz] pc; rewrite -(select_uniq pc ze pz). Qed.

Lemma select_pr1 (p : property) E:
  (exists2 x, inc x E & p x) -> (singl_val2 (inc ^~ E) p) ->
  p (select p E).
Proof. move => ha hb; exact: (proj1 (select_pr ha hb)). Qed.

(** New definition of Yo *)

Definition Yo_def (P : Prop) (x y : Set) :=
  select  (fun z  => (P /\ z = x) \/ (~P /\ z = y)) (doubleton x y).
Definition Yo := locked Yo_def.

Lemma Y_true (P:Prop) (hyp :P) x y: Yo P x y = x.
Proof. 
rewrite /Yo -lock /Yo_def.
symmetry; apply: (select_uniq _ (set2_1 x y)); last by left.
by move => u v _; case; case => // _ -> _; case; case => // _.
Qed.

Lemma Y_false (P:Prop) (hyp : ~P) x y: Yo P x y = y.
Proof.
rewrite /Yo -lock /Yo_def.
symmetry; apply: (select_uniq _ (set2_2 x y)); last by right.
by move => u v _; case; case => // _ -> _; case; case => // _.
Qed.

Lemma Y_same (P: Prop) x : Yo P x x = x.
Proof.
by case: (p_or_not_p P) => pp; [rewrite Y_true | rewrite Y_false].
Qed.


Ltac Ytac eq:= 
  match goal with
  | |- context  [Yo ?p _ _ ] =>
      case: (p_or_not_p p) => eq; 
   [rewrite (Y_true eq) | rewrite (Y_false eq) ]
end.

Ltac Ytac0 := match goal with
  | h: ?p |- context  [Yo ?p  _ _ ] => rewrite (Y_true h)
  | h: (~ ?p) |- context  [Yo ?p  _ _ ] => rewrite (Y_false h)
  | h: ?j <> ?i |- context  [Yo (?i = ?j) _ _ ] 
     => rewrite (Y_false (nesym h))
  | |- context  [Yo (?i = ?i) _ _ ] => rewrite (Y_true (refl_equal i))
  | |- context  [Yo (C0 = C1) _ _ ] => rewrite (Y_false C0_ne_C1)
  | |- context  [Yo (C1 = C0) _ _ ] => rewrite (Y_false C1_ne_C0)
  | |- context  [Yo ?p  ?x ?x ] => rewrite (Y_same p x)
end.




(* Definition select (p: property) (E: Set) := union (Zo E p). *)


End Union. 

Export Union. 

(** ** Powerset *)
Module Powerset. 

(** Forall all [p:X-> 2], we consider the inverse image of [0]. 
The set of all these quantities is the set of subsets of [X] *)

Definition powerset (x : Set) := 
 IM (fun p : x -> C2 =>
    Zo x (fun y : Set => forall hyp : inc y x, Ro (p (Bo hyp)) = C0)).

Notation "\Po E" :=   (powerset E) (at level 30).

Lemma setP_i y x : sub y x -> inc y (\Po x). 
Proof. 
have fp: forall a:x, inc (Yo (inc (Ro a) y) C0 C1) C2.
  by move => a; Ytac h; fprops.
move => sxy; apply/IM_P; exists (fun  a => Bo (fp a)); set_extens t.
  by move => ty; apply:(Zo_i (sxy _ ty)) => hyp; rewrite B_eq B_eq; Ytac0.
move /Zo_P => [tz h]; move: (h tz); rewrite B_eq. 
by Ytac w; [ move: w; rewrite B_eq | move: C1_ne_C0 ].
Qed.

Lemma setP_hi x y: inc x (\Po y) -> sub x y.
Proof. by case /IM_P => t ->; apply: Zo_S. Qed.

Lemma setP_P x y : inc x (\Po y) <-> sub x y.
Proof. split; [ apply: setP_hi | apply: setP_i]. Qed. 

Lemma setP_Ti x: inc x (\Po x).
Proof. by apply/setP_P. Qed.

Lemma setP_0i x: inc emptyset (\Po x).
Proof. apply/setP_P; fprops. Qed.

Lemma setP_S a b: sub a b <-> sub (\Po a) (\Po b).
Proof. 
split => sab.
  move=> x /setP_P sxa; apply /setP_P; apply: (sub_trans sxa sab).
by apply /setP_P;apply: sab; apply /setP_P.
Qed.

Lemma setP_0: \Po emptyset = singleton emptyset.
Proof. 
set_extens t; first by move /setP_P /sub_set0 ->; fprops.
move /set1_P ->; apply: setP_0i.
Qed.

Lemma setP_1 x: \Po (singleton x) = doubleton emptyset (singleton x).
Proof. 
set_extens t.
  by move /setP_P /subset1P => [] ->; apply/set2_P; [left | right].
case /set2_P => ->; fprops; apply /setP_P; fprops.
Qed.

Lemma setP_00 : \Po (\Po emptyset) = C2.
Proof. rewrite setP_0 setP_1 //. Qed.


Lemma Zop_i E (p:property) x: sub x E -> p x -> inc x (Zo (\Po E) p).
Proof. by move => /setP_P ha hb; apply: Zo_i. Qed.


Lemma Zop_S E (p:property) x: inc x (Zo (\Po E) p) -> sub x E.
Proof. by move => /Zo_S /setP_P.  Qed.


End Powerset. 
Export Powerset.


(** ** Intersection *)
Module Intersection. 


(** Intersection: set of all [z] in some element of [x], 
  that are in all elements of [x]
*) 

Definition intersection (x : Set) :=
  Zo (union x) (fun y : Set => forall z : Set, inc z x -> inc y z). 

Lemma setI_0: intersection emptyset = emptyset.
Proof. apply /set0_P => t /Zo_S;rewrite setU_0; apply /in_set0. Qed.

Lemma setI_i x a:
  nonempty x -> (forall y, inc y x -> inc a y) -> inc a (intersection x). 
Proof. 
move => [y yx] all_ayx; apply: Zo_i=> //.  
move: (all_ayx _ yx) (yx); apply: setU_i.
Qed.

Lemma setI_hi x a y: inc a (intersection x) -> inc y x -> inc a y.
Proof. move/Zo_hi; apply. Qed.

Lemma setI_s1 x y: inc y x -> sub (intersection x) y.
Proof. by move=> yx t ti; move: ti yx; apply: setI_hi. Qed.

Lemma setI_s2 x y: nonempty y ->
  (forall i, inc i y -> sub x i) ->  sub x (intersection y).
Proof. by move=> ne hyp t tx; apply:(setI_i ne) => v /hyp; apply. Qed.

Lemma setI_sub2 x y: (forall i, inc i y -> sub i x) -> sub (intersection y) x.
Proof. 
move=> hyp.
case: (emptyset_dichot y) => ie; first by  rewrite ie setI_0; fprops.
case: ie => i iy; exact:(sub_trans (setI_s1 iy) (hyp _ iy)).
Qed.


(** Intersection of two sets *)

Definition intersection2 x y := intersection (doubleton x y).

Notation "a \cap b" := (intersection2 a b) (at level 50).

Lemma setI2_i x A B: inc x A -> inc x B -> inc x (A \cap B).
Proof. 
move => xa xb.
by apply: setI_i; [ apply: set2_ne | move=> t /set2_P [] -> ].
Qed.

Hint Resolve setI2_i : fprops.

Lemma setI2_1 A B: sub (A \cap B) A.
Proof. move => x xi; apply: (setI_hi xi); fprops. Qed.

Lemma setI2_2 A B: sub(A \cap B)  B.
Proof. move => x xi; apply: (setI_hi xi); fprops. Qed.

Lemma setI2_P x A B: inc x (A \cap B) <-> (inc x A /\ inc x B).
Proof. 
split => [xi | [xa xb]]; last by fprops.
by split; [apply: (setI2_1 xi) | apply:(setI2_2 xi)].
Qed.

Lemma subsetI2l A B: sub (A \cap B) A.
Proof. move => x;apply: setI2_1. Qed.

Lemma subsetI2r A B: sub (A \cap B) B.
Proof. move => x;apply: setI2_2. Qed.

Lemma setI2_id: idempotent intersection2.
Proof.  
by move => A;set_extens t; [case/setI2_P | move=> tA; apply/setI2_P; split].
Qed.

Lemma setI_1 x: intersection (singleton x) = x.
Proof. apply: setI2_id. Qed.

Lemma setI2_C: commutative intersection2.
Proof. move => A B; set_extens t; move /setI2_P => [pa pb]; fprops. Qed.

Lemma setI2_A: associative intersection2.
Proof. 
move => A B C; rewrite setI2_C.
set_extens t; case /setI2_P; case /setI2_P=> tx ty tz; apply/setI2_P;fprops.
Qed.

Lemma setI2_CA : left_commutative intersection2.
Proof. by move =>A B C; rewrite !setI2_A (setI2_C B). Qed.

Lemma setI2_AC : right_commutative intersection2.
Proof. by move => A B C;rewrite -!setI2_A (setI2_C B). Qed.

Lemma setI2_ACA: interchange intersection2 intersection2.
Proof. by move => A B C D; rewrite -! setI2_A (setI2_CA B). Qed.
  
Lemma set2_IIl : left_distributive intersection2 intersection2.
Proof.
by move => A B C; rewrite setI2_A !(setI2_AC _ C) -(setI2_A _ C) setI2_id.
Qed.

Lemma set2_IIr : right_distributive intersection2 intersection2.
Proof. move => A B C; rewrite !(setI2_C A); exact: set2_IIl. Qed.

Lemma setI2_S1 A B C : sub A B -> sub (C \cap A) (C \cap B).
Proof. move=> sAB t; case /setI2_P => ta tc; fprops. Qed.

Lemma setI2_S2 A B C : sub A B -> sub (A \cap C) (B \cap C).
Proof. by move=> sAB; rewrite -!(setI2_C C); exact: setI2_S1. Qed.

Lemma setI2_SS A B C D : sub A C -> sub B D -> sub (A \cap B) (C \cap D).
Proof.  
move => s1 s2; apply: sub_trans (setI2_S1 (C:=C) s2); apply: (setI2_S2 s1).
Qed.

Lemma setI2_12S A B C: sub C A -> sub C B -> sub C (A \cap B).
Proof. rewrite -{3}(setI2_id C); exact:setI2_SS. Qed.

Lemma subsetI2_P A B C : sub C (A\cap B)  <-> (sub C A /\ sub C B).
Proof. 
split; last by move => [h1 h2]; apply: setI2_12S.
move => h;split; apply: (sub_trans  h); [apply: subsetI2l |apply: subsetI2r].
Qed.

Lemma subI2_set A B C : (sub A C) \/ (sub B C) -> sub (A \cap B) C.
Proof. 
case => h; apply: (sub_trans _ h);[apply: subsetI2l |apply: subsetI2r].
Qed.

Lemma setIC2 A B C:  A \cap (B -s C) =  A \cap B -s  (A \cap C).
Proof.
set_extens t.
  move => /setI2_P [tA /setC_P [tb ntc]]; apply /setC_P; split; fprops.
  by move /setI2_P => [].
move => /setC_P [/setI2_P [ha hb] /setI2_P hc]; apply/setI2_P; split => //.
by apply/setC_P; split => //; dneg hd.
Qed.

Lemma setI2id_Pl A T: sub A T <-> A \cap T = A.
Proof. 
split; last by move => <-;apply: subsetI2r.
move => sat; apply: extensionality; first by apply: subsetI2l.
by rewrite - {1}(setI2_id A); apply:setI2_S1.  
Qed.

Lemma setI2id_Pr A T: sub A T <-> T \cap A = A.
Proof. rewrite setI2_C; apply: setI2id_Pl. Qed.

Lemma setPI : morphism_2 powerset intersection2  intersection2.
Proof. 
move => A B; set_extens t.
  move/setP_P /subsetI2_P => [ta tb];apply/setI2_P.
  by split; apply/setP_P.
by move /setI2_P=> [ta tb]; apply/setP_P; apply: setI2_12S;apply/setP_P.
Qed.

Lemma set_UI2l: left_distributive union2 intersection2.
Proof.
move => A B C; set_extens t.
  case /setU2_P. 
    by case /setI2_P => ta tb;apply/setI2_P; split; apply/setU2_P; left.
  by move => tc;apply/setI2_P; split; apply/setU2_P; right.
case/setI2_P;case /setU2_P=> tac; case /setU2_P => tbc;apply/setU2_P; fprops.
Qed.

Lemma set_UI2r: right_distributive union2 intersection2.
Proof. move => a b c; rewrite !(setU2_C a); apply: set_UI2l. Qed.

Lemma set_IU2l: left_distributive intersection2 union2.
Proof.
move => A B C; set_extens t.
  case /setI2_P; case /setU2_P=> tab tc; apply/setU2_P; fprops.
case/setU2_P; case/setI2_P => tab tc; apply/setI2_i => //; apply/setU2_P;fprops.
Qed.

Lemma set_IU2r: right_distributive intersection2 union2.
Proof. move => a b c; rewrite !(setI2_C a); apply: set_IU2l. Qed.

Lemma set_U2K A B: (A \cup B) \cap A = A.
Proof.
apply: extensionality; first by apply:subsetI2r.
apply/subsetI2_P;split; [ apply:subsetU2l | fprops].
Qed.

Lemma set_K2U A B: A \cap (B \cup A) = A.
Proof. rewrite setU2_C setI2_C; exact: set_U2K. Qed.

Lemma set_I2K A B: (A \cap B) \cup A = A.
Proof.
apply: extensionality; last by apply:subsetU2r.
apply/subU2_setP;split; [ apply:subsetI2l | fprops].
Qed.

Lemma set_K2I A B: A \cup (B \cap A) = A.
Proof. rewrite setU2_C setI2_C; exact: set_I2K. Qed.

Lemma setU2_ni x A B: ~inc x (A\cup B) -> (~ inc x A  /\ ~ inc x B).
Proof. by move => h; split;dneg xab; apply/setU2_P; [left | right]. Qed.

Lemma setI2_ni x A B: ~inc x (A\cap B) -> (~ inc x A \/ ~ inc x B).
Proof. 
move => h; case: (inc_or_not x A); fprops => xa; right => xB; case: h; fprops.
Qed.

Lemma setC_ni x A B: ~inc x (A -s B) -> (~ inc x A \/ inc x B).
Proof. 
move => h; case: (inc_or_not x B) => nxb; [by right  |  left].
move => xa; case: h; fprops.
Qed.

Lemma set_CU2 A B X: X -s (A\cup B) = (X -s A) \cap (X -s B).
Proof.
set_extens t.
  case/setC_P => tX tu; apply/setI2_P; move: (setU2_ni tu) => [ta tb].
  split; fprops.
case /setI2_P => /setC_P [tx ta] /setC_P [_] tb.
by apply/setC_P;split; [ | case/setU2_P].
Qed.

Lemma set_CI2 A B X: X -s (A\cap B) = (X -s A) \cup (X -s B).
Proof.
set_extens t.
  case/setC_P => tX tu; apply/setU2_P; case: (setI2_ni tu) => ti; fprops.
by case /setU2_P => /setC_P [ta tab]; apply/setC_P;split => //; case/setI2_P.
Qed.

Lemma setCI2_pr1 A B E: sub A E -> A -s  B = A \cap (E -s B).
Proof.
move => ae; set_extens t.
  case /setC_P => ta tb; apply/setI2_P; split; first by exact. 
  by apply/setC_P; split; [ apply: ae |].
case /setI2_P => ta /setC_P [_] tb; fprops.
Qed.

Lemma set_CC A B E: sub B E -> (E -s (A -s B)) = (E -s A) \cup B.
Proof.
move => be; set_extens t.
  case/setC_P => te td; apply/setU2_P. 
  case: (setC_ni td)=> ta; [left | right]; fprops.
move => h; apply /setC_P;case /setU2_P :h.
  by case /setC_P => te ta;split => //;case/setC_P.
by move => tB;split; [ apply: be |case/setC_P ].
Qed.

Lemma setI2_Cr A B : (A \cap B) \cup (A -s B) = A.
Proof. by rewrite set_UI2l  setU2Cr1  setU2Cr2 set_K2U. Qed.

Lemma setCU2_l A B C : (A \cup B) -s C = (A -s C) \cup (B -s C).
Proof. 
set_extens t. 
  case/setC_P => /setU2_P [] tab tc; apply/setU2_P; fprops.
case/setU2_P => /setC_P [tab tc];apply/setC_P; split; fprops. 
Qed.

Lemma setCU2_r A B C : A -s (B \cup C) = (A -s B) \cap (A -s C).
Proof. 
set_extens t. 
  case/setC_P => ta /setU2_ni [tb tc]; apply/setI2_P; fprops. 
case/setI2_P => /setC_P [ta tb] /setC_P [_] tc.
by apply/setC_P;split; [ |  case /setU2_P].
Qed.

Lemma setCI2_l A B C : (A \cap B) -s C = (A -s C) \cap (B -s C).
Proof.
set_extens t. 
  by case/setC_P;case/setI2_P => ta tb tc; apply/setI2_P;split; apply/setC_P.
case/setI2_P => /setC_P [ta tc] /setC_P  [tb _]; apply/setC_P; fprops. 
Qed.

Lemma setCI2_r A B C : A -s (B \cap C) = (A -s B) \cup (A -s C).
Proof. 
set_extens t. 
  case/setC_P => ta tbc; apply/setU2_P; case:(setI2_ni tbc)=> tb; fprops.
by case/setU2_P; case/setC_P => ta tc; apply/setC_P; split => //; case /setI2_P.
Qed.

Lemma setCC_l A B C : (A -s B) -s C = A -s (B \cup C).
Proof. 
set_extens t; case /setC_P.
  by case /setC_P => ta tb tc; apply/setC_P; split; [ | case/setU2_P ].
move => ta /setU2_ni [tb tc]; apply/setC_P;fprops.
Qed.

Lemma setCC_r A B C : A -s (B -s C) = (A -s B) \cup (A \cap C).
Proof. 
set_extens t. 
  case /setC_P => ta tbc; apply/setU2_P;case: (setC_ni tbc) => tbc'; fprops.
by case /setU2_P; [case /setC_P => ta tb | case /setI2_P => ta tc];
    apply/setC_P;split => // ;case /setC_P.
Qed.

(** Two sets are disjoint if the intersection is empty *)

Definition disjoint (x y: Set) := x \cap y = emptyset.
Definition disjointVeq (x y: Set) := x = y \/ disjoint x y.

Ltac empty_tac1 u :=
  case: (in_set0 (x:= u));
  match goal with 
      H: ?x = emptyset |- _ => rewrite - H 
    | H: emptyset = ?x |- _ =>  rewrite H 
    | H: disjoint _ _ |- _ => rewrite - H; apply /setI2_P; split end;
   fprops. 

Lemma setI2_0 A : disjoint A emptyset.
Proof. apply/setI2id_Pr;fprops. Qed.

Lemma set0_I2 A : disjoint emptyset A.
Proof. rewrite /disjoint setI2_C; exact: setI2_0. Qed.

Lemma disjoint_pr A B:
  (forall x, inc x A -> inc x B -> False) -> disjoint A B.
Proof. move=> p; apply /set0_P => u; case/setI2_P; apply: p. Qed.

Lemma set_IC1r A B:  A \cap (A -s B) =  A -s B.
Proof. apply/ setI2id_Pr; apply: sub_setC. Qed.

Lemma set_I2Cr A B: disjoint B (A -s B).
Proof. by apply: disjoint_pr => u uy; case /setC_P. Qed.


Ltac mdi_tac v:= match goal with 
 | |- ?a = ?b \/ _ 
     => case: (equal_or_not a b); first (by left); move=> v; 
        right; apply: disjoint_pr
 | |- disjointVeq ?a ?b 
    => case: (equal_or_not a b); first (by left); move=> v; 
     right; apply: disjoint_pr
 end.

Lemma subsets_disjoint_P A B E: sub A E ->
  (sub A B <-> disjoint A (E -s B)).
Proof.
move => ae;split.
  by move => ab; apply: disjoint_pr => u ua; case /setC_P; move: (ab _ ua). 
move => dae t ta; ex_middle tb; empty_tac1 t; apply/setC_P; split; fprops.
Qed.

Lemma disjoint_subsets_P A E: sub A E -> forall B, 
  (disjoint A B <-> sub A (E -s B)).
Proof.
move => sae B; split.
  move => dab t ta; apply/setC_P; split; first by apply: sae. 
  move => tb;empty_tac1 t.
by move => sd; apply: disjoint_pr => u ua; move: (sd _ ua); case /setC_P.
Qed.

Lemma setCId_Pl A B: A -s B = A <->  disjoint A B.
Proof.
split => eq1. 
  apply/(disjoint_subsets_P (@sub_refl A)); rewrite eq1; fprops.
apply:extensionality; first by apply:sub_setC.
move => t tA; apply/setC_P;split => // tB; empty_tac1 t.
Qed.

Lemma subCset_P3 A B C : sub A (B -s C) <-> (sub A B /\ disjoint A C).
Proof. 
split => [h | [sab dac t ta]].
  by split; [move => t ta | apply: disjoint_pr => t ta]; case /setC_P: (h _ ta).
apply/setC_P; split; [by apply: sab | move => tC; empty_tac1 t].
Qed.

Lemma nondisjoint x A B: inc x A -> inc x B -> ~ disjoint A B.
Proof. by move=> xa xb dg; empty_tac1 x. Qed.

Lemma disjointVeq_pr x y z: disjointVeq x y -> inc z x -> inc z y -> x = y.
Proof. by move => H zx zy; case: H => //; move: (nondisjoint zx zy). Qed.

Lemma disjoint_S: symmetric_r disjoint.
Proof. by move => x y;rewrite /disjoint setI2_C. Qed.

Lemma disjoint_setU1 A b : ~ (inc b A) -> disjoint A (singleton b).
Proof.
by move => pa; apply:disjoint_S; apply/set0_P=> u; case/setI2_P => /set1_P->.
Qed.


Lemma subsetC1_P A B x: (sub A (B -s1 x)) <-> (sub A B /\ ~inc x A).
Proof.
split; first by case/subCset_P3=> [pa pb]; split => // xa; empty_tac1 x; fprops.
move => [pa pb] t ta; apply/setC1_P; split; fprops; dneg tx; ue.
Qed.

Lemma properI2_r A B : ~(sub B A) <-> ssub (A \cap B) B.
Proof.
split; first by move => nba; split;[ apply:subsetI2r | move /setI2id_Pr].
by move =>[_ hb] /setI2id_Pr.
Qed.

Lemma properI2_l A B : ~(sub A B) <-> ssub (A \cap B) A.
Proof. by rewrite setI2_C; apply: properI2_r.  Qed.

Lemma properU2_r A B : ~(sub A B) <-> ssub B (A \cup B).
Proof.  
split.
move => nba; split; [ apply:subsetU2r | dneg hh ;by apply /setU2id_Pl].
by move => [_ hb] /setU2id_Pl h; case: hb.
Qed.

Lemma properU2_l A B : ~(sub B A) <-> ssub A (A \cup B).
Proof. rewrite setU2_C; apply: properU2_r. Qed.

Lemma properI2_set A B C : (ssub B A) \/ (ssub C A) -> (ssub (B \cap C) A).
Proof. by case; apply: ssub_trans2 => t; case/setI2_P. Qed.

Lemma properI2 A B C : ssub A (B \cap C) -> (ssub A B /\ ssub A C).
Proof.
by move=> ta; split; apply: (ssub_trans1 ta) => t; case/setI2_P.
Qed.

Lemma properU2 A B C : ssub (B \cup C) A -> ssub B A /\ ssub C A.
Proof. move=> ta; split; apply: ssub_trans2 ta => t tb; fprops.  Qed.

Lemma properD A B C : ssub A (B -s C) -> ssub A B /\ disjoint A C.
Proof.
move => [pa pb]; move/subCset_P3: pa => [pc pd]; split => //; split => //.
by dneg ab; rewrite -ab; symmetry; apply/setCId_Pl. 
Qed.

End Intersection.

Export Intersection. 


(** ** Ordered Pair *)

Module Pair.

(** The object [(J x y)] is a set from which [x] and [y] can be recovered. 
   Bourbaki (English edition) uses an  axiom; he uses a doubleton in the French
   version;  we use here another doubleton and an axiom. *)

Definition kpair_def x y := doubleton (singleton x) (doubleton x y).
Definition kpr1_def x := union (intersection x).
Definition kpr2_def x := 
   union (Zo (union x) (fun z => (doubleton (kpr1_def x) z) = (union x))).

Definition kpair := locked kpair_def.
Definition kpr1 := locked kpr1_def.
Definition kpr2 := locked kpr2_def.


Lemma kpairE x y: kpair x y = kpair_def x y.
Proof. by rewrite  /kpair -lock . Qed.
Lemma kpr1E x: kpr1 x = kpr1_def x.
Proof. by rewrite  /kpr1 -lock. Qed.
Lemma kpr2E x: kpr2 x = kpr2_def x.
Proof. by rewrite  /kpr2 - lock. Qed.



Notation J := kpair.
Notation P := kpr1.
Notation Q := kpr2.


Lemma pr1_pair x y: P (J x y) = x.
Proof.
rewrite kpr1E kpairE -{2} (setU_1 x); congr union.
have sx_k: inc (singleton x) (kpair_def x y) by apply: set2_1.
apply: set1_pr.
  apply: setI_i;first by exists (singleton x).
  move => z /set2_P [] ->; fprops.
move=> z zi; apply/set1_P; apply: (setI_hi zi sx_k).
Qed.


Lemma pr2_pair x y: Q (J x y) = y.
Proof.
rewrite kpr2E -{2}(setU_1 y); congr (union _).
have ->: (union (J x y) = doubleton x y).
  rewrite kpairE /kpair_def ; set_extens t =>ts.
    case /setU2_P: ts => // /set1_P ->; fprops.
  by apply: (setU_i ts); fprops.
have -> : (kpr1_def (J x y)) = x by rewrite - kpr1E pr1_pair.
apply: set1_pr; first by apply: Zo_i; fprops.
move => z /Zo_P [] /set2_P [] // -> sd.
by move: (set2_2 x y); rewrite - sd ; move/set1_P.
Qed.

Hint Rewrite pr1_pair pr2_pair : aw. 

Lemma pr1_def a b c d: J a b = J c d -> a = c.
Proof. by move/(congr1 P); aw. Qed.

Lemma pr2_def a b c d: J a b = J c d -> b = d.
Proof. by move/(congr1 Q); aw. Qed.


Lemma pr12_def a b c d : J a b = J c d -> a = c /\ b = d.
Proof. by move => h; rewrite (pr1_def h)(pr2_def h). Qed.


Definition pairp (x : Set) := (J (P x) (Q x) = x).

Lemma pair_is_pair x y: pairp (J x y). 
Proof. by rewrite /pairp; aw. Qed.

Hint Resolve pair_is_pair: fprops.

Lemma pair_exten x y:
  pairp x -> pairp y -> P x = P y -> Q x = Q y -> x = y.
Proof. by move => {3} <- {3} <- -> ->. Qed.

End Pair.

Export Pair.


(** ** Cartesian products of two sets *)

(**  This is the set of all pairs [J x y] with x in A, y in B *)

Module Cartesian.

Definition product (A B : Set) :=
  union (fun_image A (fun x => (fun_image B (J x)))).

Definition coarse A := product A A.

Notation "A \times B" := (product A B) (at level 40).  

Lemma setX_P x A B:
  inc x (A \times B) <-> [/\ pairp x, inc (P x) A & inc (Q x) B].
Proof.
split. 
  move/setU_P => [a xa /funI_P [t ty ft]].
  move: xa; rewrite ft; move/funI_P => [u uz ->]; aw; split; fprops.
move => [px Px Qx];apply/setU_P; exists  (fun_image B (J (P x)));
  apply/funI_P; [ exists (Q x); fprops; aw | by exists (P x) ]. 
Qed.

Lemma setX_pair x A B: inc x (A \times B) -> pairp x.
Proof. by case/setX_P. Qed.

Lemma setX_i x A B:
  pairp x -> inc (P x) A -> inc (Q x) B -> inc x (A \times B).
Proof. by move => pa pb pc; apply/setX_P. Qed.

Lemma setXp_i x y A B:
  inc x A -> inc y B -> inc (J x y) (A \times B).
Proof. move => pa pb; apply setX_i; aww. Qed.

Lemma setXp_P x y A B:
  inc (J x y) (A \times B) <-> (inc x A /\ inc y B).
Proof. 
by split; [move/setX_P=> [_]; aw | move=> [xa ya]; apply: setXp_i].
Qed.

Hint Resolve setXp_i: fprops.


(** A product is empty if and only one factor is empty *)

Lemma setX_0l B: emptyset \times B = emptyset.
Proof. by apply /set0_P => x /setX_P [_ /in_set0]. Qed.
  
Lemma setX_0r A: A \times emptyset = emptyset.
Proof. by apply /set0_P => y /setX_P [_ _ /in_set0]. Qed.
  
Lemma setX_0 A B:
  A \times B = emptyset -> (A = emptyset \/ B = emptyset).
Proof. 
move=> pe; case: (emptyset_dichot A);first by left.
by case => t tx; right; apply /set0_P => u up; empty_tac1 (J t u).
Qed.

Hint Rewrite setX_0r setX_0l : aw.

(** The product [A \times B] is increasing in A and B, 
strictly if the other argument is non empty. *)

Lemma setX_Sl x x' y: sub x x' -> sub (x \times y) (x' \times y).
Proof. move => xx' t /setX_P [pt pa pb]; apply/setX_P; split;fprops. Qed.

Lemma setX_Sr x y y': sub y y' -> sub  (x \times y) (x \times y').
Proof. move => xx' t /setX_P [pt pa pb]; apply/setX_P;split;fprops. Qed.

Lemma setX_Slr x x' y y':
  sub x x' -> sub y y' -> sub (x \times y) (x' \times y').
Proof. 
move=> xx' yy'; apply: (@sub_trans  (x \times y')); first by apply:setX_Sr. 
by apply: setX_Sl.
Qed.

Lemma setX_Sll x y:  sub x y -> sub (coarse x) (coarse y).
Proof. by move => s; apply: setX_Slr. Qed.

Lemma setX_lS x x' y: nonempty y ->
  sub (x \times y) (x' \times y) -> sub x x'. 
Proof. 
by move=> [t ty] s z zx; move: (s _ (setXp_i zx ty)); case/setXp_P.  
Qed.

Lemma setX_rS x y y': nonempty x ->
  sub (x \times y) (x \times y') -> sub y y'. 
Proof. 
by move=> [t tx] s z zy; move: (s _ (setXp_i tx zy)); case/setXp_P.  
Qed.

Lemma set2_UXr: right_distributive product union2.
Proof. 
move => a b c;set_extens x.
  move /setX_P => [pa pb] /setU2_P.
  by case => pc; apply /setU2_P; [left | right]; apply:setX_i.
case /setU2_P => /setX_P [pa pb pc]; apply/setX_i => //; fprops.
Qed.

Lemma set2_UXl: left_distributive product union2.
Proof. 
move => a b c; set_extens x.
  move /setX_P => [pa /setU2_P pb pc].
  by case:pb => pb; apply /setU2_P; [left | right]; apply:setX_i.
case /setU2_P => /setX_P [pa pb pc]; apply/setX_i => //; fprops.
Qed.


Lemma set2_IXr: right_distributive product intersection2.
Proof. 
move => a b c;set_extens x. 
 by move/setX_P => [Px xa /setI2_P [pa pb]]; apply/setI2_P;split;apply/setX_P.
move /setI2_P => [] /setX_P [Px px qx1 /setX_P [_ _ qx2]].
apply/setX_P; split; fprops.
Qed.



Lemma set2_IXl: left_distributive product intersection2.
Proof. 
move => a b c;set_extens x.
 by move/setX_P => [Px  /setI2_P [pa pb] xa]; apply/setI2_P;split;apply/setX_P.
move /setI2_P => [] /setX_P [Px px qx1 /setX_P [_ qx2 _]].
apply/setX_P; split; fprops.
Qed.



Definition indexed (x i: Set) := x \times singleton i.
Definition indexedr (i x: Set) := singleton i \times x.
Notation "a *s1 b" := (indexed a b) (at level 50).  

Lemma indexed_pi x i y: inc y x -> inc (J y i) (x *s1 i).
Proof. move => pa; apply: setXp_i => //; fprops. Qed.

Lemma indexed_P x i y: 
  inc y (x *s1 i) <-> [/\ pairp y, inc (P y) x & Q y = i].
Proof.
split; first by  move /setX_P => [pa pb /set1_P].
move =>[pa pb <-]; apply: setX_i; fprops.
Qed.

Lemma indexedrP a b c: 
  inc a (indexedr b c) <-> [/\ pairp a, P a = b & inc (Q a) c].
Proof.
split; first by move/setX_P => [pa /set1_P pb pc].
move =>[pa pb pc]; apply/setX_P;split => //; rewrite pb;fprops.
Qed.

End Cartesian.

Export Cartesian.

(** ** Functional graphs *)

Definition prop_inc1 (X : Set) (P: property) 
   & (phantom Prop (forall x0 : Set, P x0)) :=
   forall x, inc x X -> P x.

Definition prop_inc11 X Y (P: relation) 
  & (phantom Prop (forall x y: Set, P x y)) := 
   forall x y, inc x X -> inc y Y -> P x y.
Definition prop_inc2 X (P: relation)
  & (phantom Prop (forall x y: Set, P x y)) :=
   forall x y, inc x X -> inc y X -> P x y.

Notation "{ 'inc' d , P }" :=
  (prop_inc1 d (inPhantom P))
  (at level 0, format "{ 'inc'  d ,  P }") : type_scope.

Notation "{ 'inc' d1 & d2 , P }" :=
  (prop_inc11 d1 d2 (inPhantom P))
  (at level 0, format "{ 'inc'  d1  &  d2 ,  P }") : type_scope.

Notation "{ 'inc' d & , P }" :=
  (prop_inc2 d (inPhantom P))
  (at level 0, format "{ 'inc'  d  & ,  P }") : type_scope.


Definition prop_when1 (X : property) (P: property) 
   & (phantom Prop (forall x : Set, P x)) :=
   forall x, X x -> P x.

Definition prop_when11 (X Y: property) (P: relation) 
  & (phantom Prop (forall x y: Set, P x y)) := 
   forall x y, X x -> Y y -> P x y.
Definition prop_when2 (X: property) (P: relation)
  & (phantom Prop (forall x y: Set, P x y)) :=
   forall x y, X x -> X y -> P x y.


Definition prop_when22 (X:relation) (P: relation)
  & (phantom Prop (forall x y: Set, P x y)) :=
   forall x y, X x y -> P x y.

Notation "{ 'when' d , P }" :=
  (prop_when1 d (inPhantom P))
  (at level 0, format "{ 'when'  d ,  P }") : type_scope.


Notation "{ 'when' d1 & d2 , P }" :=
  (prop_when11 d1 d2 (inPhantom P))
  (at level 0, format "{ 'when'  d1  &  d2 ,  P }") : type_scope.

Notation "{ 'when' d & , P }" :=
  (prop_when2 d (inPhantom P))
  (at level 0, format "{ 'when'  d   & ,  P }") : type_scope.


Notation "{ 'when' : d , P }" :=
  (prop_when22 d (inPhantom P))
  (at level 0, format "{ 'when' :  d ,  P }") : type_scope.

Definition commutes_at (f g: Set -> Set) x:= f (g x) = g (f x).
Definition commutes f g := forall x, commutes_at f g x.

Definition compatible_1 f (p q: property) := 
    forall x, (p x) -> q (f x).
Definition compatible_2 f (p q:relation)  := 
    forall x y, (p x y) -> q (f x) (f y).
Definition compatible_3 f (p q:property)  := 
    forall x y, (p x) -> (p y) -> q (f x y).

Notation "{ 'compat' f : x / p >-> q }" :=
  (compatible_1 f  (fun x => p) (fun x => q))
  (at level 0,  f at level 99, x ident, 
     format "{ 'compat'  f  : x  /  p  >->  q }") : type_scope.

Notation "{ 'compat' f : x / p }" :=
  (compatible_1 f  (fun x => p) (fun x => p))
  (at level 0,  f at level 99, x ident, 
    format "{ 'compat'  f  : x  /  p }") : type_scope.

Notation "{ 'compat' f : x y / p >-> q }" :=
  (compatible_2 f  (fun x y => p) (fun x y => q))
  (at level 0,  f at level 99, x ident, y ident,
    format "{ 'compat'  f  : x  y  /  p  >->  q }") : type_scope.
Notation "{ 'compat' f : x y / p }" :=
  (compatible_2 f  (fun x y => p) (fun x y => p))
  (at level 0,  f at level 99, x ident, y ident,
    format "{ 'compat'  f  : x  y  /  p }") : type_scope.

Notation "{ 'compat' f : x & / p >-> q }" :=
  (compatible_3 f  (fun x => p) (fun x => q))
  (at level 0,  f at level 99, x ident,
     format "{ 'compat'  f  : x  &  /  p  >->  q }") : type_scope.

Notation "{ 'compat' f : x & / p }" :=
  (compatible_3 f  (fun x => p) (fun x => p))
  (at level 0,  f at level 99, x ident, 
     format "{ 'compat'  f  : x  &  /  p }") : type_scope.

Module Function.

(** A graph is a set of pair; the set of first projections is the domain, 
the set of second projections is the range*)

Definition sgraph r := alls r pairp.
Definition domain f := fun_image f P.
Definition range f := fun_image f Q.

(** A functional graph is one for which [P] is injective *)

Definition fgraph f := sgraph f /\ {inc f &, injective P}.
Definition related r x y := inc (J x y) r.

Lemma fgraph_sg f: fgraph f -> sgraph f.
Proof. by case. Qed.


Lemma fgraph_pr f x y y':
  fgraph f -> inc (J x y) f -> inc (J x y') f -> y = y'.
Proof. 
move=> [_ fg] ia ib.
move: (fg _ _ ia ib); aw => h; exact: (pr2_def (h (erefl x))).
Qed. 

Hint Resolve fgraph_sg : fprops.

(** We give here some properties of the domain and range *)


Lemma domain_i1 f x: inc x f -> inc (P x) (domain f). 
Proof. by apply: funI_i. Qed. 

Lemma range_i2 f x: inc x f -> inc (Q x) (range f). 
Proof. by apply: funI_i. Qed.

Hint Resolve domain_i1 range_i2: fprops.

Lemma domain_i f x y: inc (J x y) f -> inc x (domain f). 
Proof. by move/domain_i1; aw. Qed.

Lemma range_i f x y: inc (J x y) f -> inc y (range f). 
Proof. by move/range_i2; aw. Qed.

Lemma domainP r: sgraph r -> forall x,
  (inc x (domain r) <-> (exists y, inc (J x y) r)).
Proof.
move=> gr; split; last by move=> [y ]; apply domain_i.
by case/funI_P => y yr ->; exists (Q y); rewrite (gr _ yr).
Qed.

Lemma rangeP r : sgraph r ->  forall y,
   (inc y (range r) <->  (exists x, inc (J x y) r)).
Proof.
move=> gr y; split;last by move=> [x]; apply range_i.
by case/funI_P => x xr ->; exists (P x); rewrite (gr _ xr).
Qed.

Ltac ex_tac:=
  match goal with
   | H:inc (J ?x ?y) ?z |- exists x, inc (J x ?y) ?z
     => exists x ; assumption
   | H:inc (J ?x ?y) ?z |- exists y, inc (J ?x y) ?z
     => exists y ; assumption
   | H:inc (J ?x ?y) ?z |- ex2 _  (fun t => inc (J t ?y) ?z)
     => exists x ; trivial
   | H:inc (J ?x ?y) ?z |- ex2 _ (fun t => inc (J ?x t) ?z)
     => exists y ; trivial
   | H:inc (J ?x ?y) ?z |- ex2 (fun t => inc (J t ?y) ?z) _
     => exists x ; trivial
   | H:inc (J ?x ?y) ?z |- ex2 (fun t => inc (J ?x t) ?z) _
     => exists y ; trivial
   | H:inc ?x ?y |- ex2 (fun t=> inc t ?y) _
     => exists x ; fprops
   | H:inc ?x ?y |- ex2 _ (fun t => inc t ?y)
     => exists x ; fprops
   | H:inc ?x ?y |- exists x, inc x ?y /\ _  
     => exists x; split => //
   | H:inc ?x ?y |- exists x, [/\ inc x ?y, _ & _ ] 
     => exists x; split => //
   |  |- ex2 (fun t => inc t (singleton ?y)) _
     => exists y ; fprops
    | H : inc (J ?x ?y) ?g |-  inc ?x (domain ?g)
       => exact: (domain_i H)
    |  H : inc (J ?x ?y) ?g |-  inc ?y (range ?g)
       => exact: (range_i H)
    | H : inc ?x ?y |-  nonempty ?y 
       => exists x;assumption
   | |- exists y, inc (J (P ?x) y) _ 
     => exists (Q x) ; aw
   | |- exists y, inc (J y (Q ?x)) _ 
     => exists (P x) ; aw
end.

Lemma funI_exten f1 f2 X:
   {inc X, f1 =1 f2} -> fun_image X f1 = fun_image X f2.
Proof.
by move => hyp; set_extens t ; move => /funI_P [y ya ->];
   apply/funI_P; ex_tac; symmetry;apply: hyp.
Qed.

Lemma sgraph_exten r r':
  sgraph r -> sgraph r' ->
  (forall u v, (related r u v <-> related r' u v)) -> r = r'.
Proof. 
rewrite /related => gr gr' p.
by set_extens t => tr;  [move: (gr _ tr)=> pt | move: (gr' _ tr)=> pt]; 
  rewrite - pt; apply /p; rewrite pt.
Qed.

Lemma setI2_graph1 x y: sgraph x ->  sgraph (x \cap y).
Proof. by move=> gx t /setI2_P [tx _]; apply: gx. Qed.

Lemma setI2_graph2 x y: sgraph y -> sgraph (x \cap y).
Proof. by move=> gx t /setI2_P [_ tx ]; apply: gx. Qed.

Lemma setU2_graph: {compat union2 : x & / sgraph x}.  
Proof. by move=> x y gx gy t /setU2_P [] tx; [apply: gx | apply: gy]. Qed.

Lemma range_set0: range emptyset = emptyset.
Proof. apply: funI_set0. Qed.

Lemma domain_set0: domain emptyset = emptyset.
Proof. apply: funI_set0. Qed.

Lemma domain_set0_P r: (domain r = emptyset <-> r = emptyset).
Proof. split; [apply :funI_setne1 | by move ->; exact domain_set0 ]. Qed.

Lemma range_set0_P r:  (range r = emptyset <-> r = emptyset).
Proof. split; [apply :funI_setne1 | by move ->; exact range_set0 ]. Qed.

Lemma domain_set0P x: nonempty (domain x) <-> nonempty x.
Proof. 
split; last by move => h; apply:funI_setne.
by move/nonemptyP => h; apply /nonemptyP; dneg xx; apply/domain_set0_P.
Qed.

Lemma domain_set1 x y: domain (singleton (J x y)) = singleton x.
Proof. by rewrite /domain funI_set1; aw. Qed.

Lemma range_set1 x y: range (singleton (J x y)) = singleton y.
Proof. by rewrite /range funI_set1; aw. Qed.

Lemma range_setU2: {morph range: x y /  x \cup y}.
Proof. apply:funI_setU2. Qed.

Lemma domain_setU2: {morph domain: x y /  x \cup y}.
Proof. apply:funI_setU2. Qed.

Lemma domain_setU z: domain (union z) = union (fun_image z domain).
Proof. apply: funI_setU. Qed.

Lemma range_setU z: range (union z) = union (fun_image z range).
Proof. apply: funI_setU. Qed.

Lemma range_setU1 f x y: range (f +s1 (J x y)) = (range f) +s1 y.
Proof. by rewrite range_setU2 range_set1. Qed.

Lemma domain_setU1 f x y: domain (f +s1 (J x y)) = (domain f) +s1 x.
Proof. by rewrite domain_setU2 domain_set1. Qed. 

Lemma sgraph_set0: sgraph emptyset.
Proof. by move=> t [][]. Qed. 

Hint Resolve sgraph_set0 : fprops.
Hint Rewrite range_set0 domain_set0 : aw.

Lemma fgraph_set0: fgraph emptyset.
Proof. by split; [fprops | move=> x y; case; case]. Qed.

Lemma fgraph_set1 a b (f := singleton (J a b)):
  [/\ fgraph f, domain f = singleton a & range f = singleton b ].
Proof.
rewrite /f domain_set1 range_set1; split => //; split.
  move => i /set1_P ->; fprops.
by move => i j /set1_P -> /set1_P ->.
Qed.  

Lemma fgraph_setU2 a b: fgraph a -> fgraph b ->
  disjoint (domain a) (domain b) ->
  fgraph (a \cup b).
Proof. 
move=> [fg fgg] [sg gfg] ei; split.
   move=> t; case/setU2_P; fprops.
move=> x y; case/setU2_P => xab; case /setU2_P=> yab;
  first (by apply: fgg); last (by apply: gfg);
move=> sp;empty_tac1 (P y); apply/funI_P; ex_tac.
Qed.


Lemma fgraph_setU1 f x y:
  fgraph f -> ~ inc x (domain f) -> fgraph (f +s1 (J x y)).
Proof.
move => sa sb; move:(fgraph_set1 x y) => [ha hb hc].
apply:fgraph_setU2 => //; rewrite hb; apply: disjoint_pr => t td /set1_P tx.
by case: sb; rewrite - tx. 
Qed. 


(** [Vg f x] is the value of [x] by a graph [f]; if there is a [z] such that 
    [J x z] is in [f], then [V] chooses one. *)

Definition action_prop (f g: Set -> Set -> Set) :=
   forall a b x, f (g a b) x = (f a (f b x)).

Definition Vg (f x: Set) := select (fun y : Set => inc (J x y) f) (range f).

Definition same_Vg  f g:= Vg f =1 Vg g .

Definition allf (g: Set) (p: property) :=
   forall x, inc x (domain g) -> (p (Vg g x)).

Notation "f1 =1g f2" := (same_Vg f1 f2)
  (at level 70, no associativity) : fun_scope.

(** The function [V] is well-defined for functional graphs. 
Here are some properties  *)

Section Vprops.
Variable f: Set.
Hypothesis fgf: fgraph f.

Lemma fdomain_pr1 x:  inc x (domain f) -> inc (J x (Vg f x)) f.
Proof.
move: fgf => [p1 p2] /funI_P [z zf ->].
have q1: exists2 y, inc y (range f) & inc (J (P z) y) f.
  exists (Q z); [ apply /funI_P; ex_tac | by rewrite (p1 _ zf)].
apply:(select_pr1 q1) => a b pa ar pb br. 
have aux: (P (J (P z) a) = P (J (P z) b)) by aw.
by move: (pr2_def (p2 _ _ ar br aux)).
Qed.

Lemma in_graph_V x: inc x f -> x = J (P x) (Vg f (P x)).
Proof. 
move => xf; apply: (proj2 fgf _ _ xf); aww.
by apply:fdomain_pr1=> //; apply: domain_i1.
Qed.

Lemma pr2_V x: inc x f -> Q x = Vg f (P x).
Proof. by move=> xf; rewrite (in_graph_V xf); aw. Qed.

Lemma range_gP y:
  (inc y (range f) <-> (exists2 x, inc x (domain f) & y = Vg f x)).
Proof. 
move: (fgf) => [sg _]; split.
  case/(rangeP sg)=> x Px; exists x; first by ex_tac.
  by move:(in_graph_V Px); aw; apply: pr2_def.
by move => [x xdf ->]; apply/(rangeP sg); exists x; apply: fdomain_pr1.  
Qed.

Lemma inc_V_range x: inc x (domain f) -> inc (Vg f x) (range f).
Proof. move=> xd; apply/range_gP; ex_tac. Qed.

End Vprops.
Hint Resolve inc_V_range: fprops.


Lemma simple_fct a b A B (f := singleton (J a b)):
  inc a A -> inc b B ->
  [/\ fgraph f, domain f = singleton a, range f = singleton b, 
   sub (domain f) A & (sub (range f) B /\ Vg f a = b) ].
Proof.
move => aA bB. 
move: (fgraph_set1 a b) => [ha hb hc]; rewrite hb hc; split => //.
+ by move => t /set1_P ->.
+ split; [by move => t /set1_P -> | symmetry ].
  by move:(pr2_V ha (set1_1 (J a b))); aw.
Qed.

(** Two functional graphs are equal if they have the same domain and evaluation *)

Lemma fgraph_exten f g:
  fgraph f -> fgraph g -> domain f = domain g ->
  {inc (domain f), f =1g g} -> f = g.
Proof. 
move=> ff fg sd hyp; set_extens t =>  tf.
  have pa:= (domain_i1 tf).
  rewrite (in_graph_V ff tf) (hyp _ pa); apply: fdomain_pr1 => //; ue.
move: (domain_i1 tf); rewrite - sd => pa.
by rewrite (in_graph_V fg tf) - (hyp _ pa); apply: fdomain_pr1.
Qed.


(** Graph associated to a function restricted to some set as domain. *)

Definition Lg (x : Set) (p : fterm) :=
  fun_image x (fun y => J y (p y)).

Definition Lgcomp g (f: fterm) :=
  Lg (domain g) (fun  z => f (Vg g z)).
       

Lemma Lg_i x y p : inc x y ->  inc (J x (p x)) (Lg y p).
Proof. move => xy; apply/funI_P; ex_tac.  Qed.

Lemma Lg_fgraph p x: fgraph (Lg x p).
Proof.
split; first by move =>t /funI_P [z _ ->]; fprops.
by move=> a b /funI_P [z1 _ ->] /funI_P [z2 _ ->]; aw => ->.
Qed.

Lemma Lgd x p: domain (Lg x p) = x.
Proof.
set_extens t.
  by case/funI_P => [e /funI_P [z zx ->] ->]; aw.
by move => tw;apply/funI_P; exists (J t (p t)); aw => //;apply:Lg_i.
Qed.

Lemma Lgcomp_domain g f : domain (Lgcomp g f) = domain g.
Proof.
by rewrite Lgd.
Qed.

Hint Rewrite Lgd Lgcomp_domain : aw. 
Hint Resolve Lg_fgraph: fprops.

Lemma LgV x p y: inc y x -> Vg (Lg x p) y = p y. 
Proof. 
by move=> yx; move: (pr2_V (Lg_fgraph p x) (Lg_i p yx)); aw.
Qed.

Arguments LgV [x p y].

Lemma LgcV g f y: inc y (domain g) -> Vg (Lgcomp g f) y = f (Vg g y). 
Proof. 
by move => h; rewrite (LgV h).
Qed.

Hint Rewrite LgV LgcV : bw. 

Lemma Lg_exten a f g: {inc a, f =1 g} -> Lg a f = Lg a g.
Proof. 
move=> eqv; apply: fgraph_exten; aww.
by move => x xa ; bw => //; apply: eqv.
Qed.

Lemma Lg_range p x: range (Lg x p) = fun_image x p.
Proof. 
set_extens z.
  by move/funI_P=> [a /funI_P [b ib ->] ->]; aw; apply:funI_i.
move/funI_P => [b ba ->];apply/funI_P.
by exists (J b (p b));aw => //; apply: Lg_i.
Qed.

Lemma Lg_range_P sf f a:
  inc a (range (Lg sf f))  <-> exists2 b, inc b sf & a = f b.
Proof. rewrite Lg_range; apply/funI_P. Qed.

Lemma Lg_recovers f: fgraph f -> Lg (domain f) (Vg f) = f.
Proof.
by move=> fg; apply: fgraph_exten; aww => x xf; apply: LgV.
Qed.

Lemma simple_fct2 a b (f := singleton (J a b)):
  [/\ fgraph f, domain f = singleton a, range f = singleton b,
   Vg f a = b & f = Lg (singleton a) (fun _ => b)].
Proof.
move: (fgraph_set1 a b) => [ha hb hc]; rewrite hb hc.
move:(pr2_V ha (set1_1 (J a b))); aw => bv.
split => //; apply: fgraph_exten => //; aww; rewrite hb => x /set1_P ->.
rewrite LgV //; apply: set1_1.
Qed.

(** Graph of the identity function. *)

Definition identity_g (x : Set) := Lg x id.

Lemma identity_fgraph x: fgraph (identity_g x). 
Proof. rewrite/identity_g; fprops. Qed. 

Lemma identity_sgraph x: sgraph (identity_g x).
Proof. by case: (identity_fgraph x). Qed. 

Lemma identity_d x: domain (identity_g x) = x.
Proof. by rewrite/identity_g; aw. Qed. 

Lemma identity_r x: range (identity_g x) = x.
Proof.  
set_extens t; first by move/Lg_range_P => [y yi ->]. 
by move => tx; apply/Lg_range_P; exists t.
Qed. 

Lemma identity_ev x a: inc x a -> Vg (identity_g a) x = x.
Proof. by rewrite/identity_g => /(LgV (p := id)). Qed.

Hint Resolve identity_sgraph : fprops.
Hint Rewrite  identity_ev : bw.

Definition cst_graph x y:= Lg x (fun _ => y).

Lemma cst_graph_pr x y: cst_graph x y = x *s1 y.
Proof.
set_extens t.
  by move/funI_P => [z zx ->]; apply: indexed_pi.
move /indexed_P => [pt Pt Qt];apply/funI_P; ex_tac; rewrite - Qt //.
Qed.

Lemma cst_graph_ev x y t : inc t x -> Vg (cst_graph x y) t = y.
Proof.  by move => tw; rewrite LgV. Qed.

Lemma cst_graph_d x y : domain (cst_graph x y) = x.
Proof. by rewrite /cst_graph; aw. Qed.

Lemma cst_graph_fgraph a b: fgraph (cst_graph a b).
Proof. rewrite /cst_graph; fprops. Qed.

Hint Rewrite cst_graph_d : aw.
Hint Resolve cst_graph_fgraph: fprops.

Lemma setU1_V_out f x y:
  fgraph f -> ~ (inc x (domain f)) ->  Vg (f +s1 (J x y)) x = y.
Proof. 
move=>ff /(fgraph_setU1 y ff) fg.
have h1: inc (J x y) (f +s1 (J x y)) by fprops.
by move: (pr2_V fg h1); aw.
Qed.

Lemma setU1_V_in f x y u:
  fgraph f -> ~ (inc x (domain f)) -> inc u (domain f) ->
  Vg (f +s1 (J x y)) u = Vg f u.
Proof.
move=> ff /(fgraph_setU1 y ff) fg /(fdomain_pr1 ff) aux. 
have h1: inc (J u (Vg f u)) (f +s1 (J x y)) by fprops.
by move: (pr2_V fg h1); aw.
Qed.

(** Case of a subgraph *)

Lemma sub_fgraph f g: fgraph g -> sub f g -> fgraph f.
Proof.
move=> [fg ffg] s; split.
  by move=> t tf; apply: (fg _ (s _ tf)). 
by move=> x y xf yf; apply: ffg; apply: s.
Qed.

Lemma domain_S f g: sub f g -> sub (domain f) (domain g).
Proof. apply: funI_S. Qed.

Lemma range_S f g: sub f g -> sub (range f) (range g).
Proof. apply: funI_S. Qed.

Lemma sub_graph_ev f g:
  fgraph g -> sub f g -> {inc (domain f), f =1g g}.
Proof.
move=> fg sfg x xdf.
set ipg:=(sfg _ (fdomain_pr1 (sub_fgraph fg sfg) xdf)).
by move: (in_graph_V fg ipg); aw; apply: pr2_def.
Qed.


(** restriction of a graph to a set *)

Definition restr f x := Lg x (Vg f).

Lemma restr_d f x: domain (restr f x) = x.
Proof. by rewrite /restr; aw. Qed.

Lemma restr_fgraph f x: fgraph (restr f x).
Proof. rewrite /restr; fprops. Qed.

Lemma restr_ev f x i: inc i x -> Vg (restr f x) i = Vg f i.
Proof. by move=>  ix; rewrite LgV.  Qed.

Hint Rewrite restr_d: aw.
Hint Rewrite restr_ev: bw.
Hint Resolve restr_fgraph : fprops.

Lemma double_restr f a b: sub a b -> (restr (restr f b) a) = (restr f a).
Proof.  
by move => sb; apply: Lg_exten => t ta; bw =>//; apply: sb.
Qed.

Lemma restr_Lg a b f: sub b a -> restr (Lg a f) b = Lg b f.
Proof.
move => sba; apply:fgraph_exten; aww.
by move => t tb; bw => //; apply: sba.
Qed.

Lemma restr_to_domain f g: fgraph f -> sub g f -> restr f (domain g) = g.
Proof.
move => h1 h2; move: (sub_fgraph  h1 h2) => fgg.
apply:fgraph_exten; aw; fprops.
by move => t tx; rewrite (LgV tx); symmetry; apply: sub_graph_ev.
Qed.

Lemma restr_range1 f x: fgraph f -> sub x (domain f) -> 
  sub (range (restr f x)) (range f).
Proof.
move=> pa pb  t/funI_P [u /funI_P [z zx -> ->]]; aw.
exact: (inc_V_range pa (pb _ zx)).
Qed.

Lemma restr_exten x f g:   {inc x, f =1g g} ->  restr f x = restr g x.
Proof.
move => Ha;  apply:fgraph_exten; try apply: restr_fgraph; rewrite !restr_d //.
by move => t tx /=; rewrite !restr_ev // Ha.
Qed.

(** Composition of two graphs. If the graphs are composable, 
  we can simplify the definition*)

Definition composablef (f g : Set) :=
  [/\ fgraph f, fgraph g & sub (range g) (domain f)]. 

Definition composef f g := Lg (domain g)  (fun y => Vg f (Vg g y)).

Notation "x \cf y" := (composef x y) (at level 50).
Notation "x \cfP y" := (composablef x y) (at level 50).

Lemma composef_ev x f g: 
  inc x (domain g) -> Vg (f \cf g) x = Vg f (Vg g x).
Proof. by move => pa; rewrite LgV. Qed. 

Lemma composef_fgraph f g: fgraph (f \cf g).
Proof. rewrite /composef; fprops. Qed. 

Lemma composef_domain f g: domain (f \cf g) = domain g.
Proof. by rewrite /composef; aw.  Qed. 

Lemma composef_range f g:  f \cfP g ->
  sub (range (f \cf g)) (range f).
Proof.
move => [pa pb pc] t; move /(range_gP (composef_fgraph f g)) => [x].
rewrite composef_domain => xdg; rewrite (composef_ev _ xdg) => ->.
apply /(range_gP pa); exists (Vg g x) => //. 
apply: pc; apply /(range_gP pb); ex_tac.
Qed.


Hint Resolve composef_fgraph: fprops.


End Function.
Export Function.
