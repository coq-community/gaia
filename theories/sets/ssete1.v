(** ** Bourbaki Sets 1 Exercises
 Copyright INRIA (2009-2012) Apics/Marelle Team (Jose Grimm).
*)
(* $Id: ssete1.v,v 1.5 2018/09/04 07:58:00 grimm Exp $ *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From gaia Require Export sset4.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Baxioms.

Definition collectivizing (R:property) := exists T, forall z, inc z T <-> R z.

Lemma AS1 (A: Prop): A \/ A -> A.
Proof. by case. Qed.
 
Lemma AS2 (A B: Prop): A -> A \/ B.
Proof. by move => h; left. Qed.

Lemma AS3 (A B: Prop): A \/ B -> B \/ A.
Proof. by case => h; [right | left]. Qed.

Lemma AS4 (A B C: Prop): (A -> B) -> (C \/ A -> C \/ B).
Proof. move => h; case; [ by left | by  move => pA; right; apply: h]. Qed.

Lemma AS5 (T:Set) (R: property): R T -> exists x, R x.
Proof. by move => h; exists T. Qed.

Lemma AS6 (T U: Set) (R: property):  T = U -> R T <-> R U.
Proof.
move => h.
have rr:  R U <-> R U by done.
exact: (eq_ind_r (fun t => R t <-> R U) rr h).
Qed.

Lemma AS6_alt (T U: Set) (R: property):  T = U -> R T <-> R U.
Proof. by move ->. Qed.


Definition AS8_def := 
 forall (R : relation),
  (forall y, exists X, forall x, R x y-> inc x X) ->
  (forall Y, collectivizing (fun x => exists2 y, inc y Y & R x y)).
  

Lemma AS8 : AS8_def.
Proof.
move => R hyp Y.
pose p y := (fun X => forall x : Set, R x y -> inc x X).
pose XX y := choose (p y).
have h x y : R x y ->  inc  x (XX y).
  move => rxy; move: (hyp y) => ee; exact: (choose_pr ee x rxy).
exists (Zo (unionf Y XX) (fun x => (exists2 y, inc y Y & R x y))) => t; split.
   by move/Zo_hi.
move => hx; apply: Zo_i => //.
by move: hx  => [y ya yb]; apply/setUf_P; exists y => //; apply: h.
Qed.

Lemma A1 x y: sub x y /\ sub y x -> x = y.
Proof. by move => [ha hb]; apply: extensionality. Qed.

Lemma A2 x y: collectivizing (fun z => z = x \/ z = y).
Proof.  exists (doubleton x y) => z; exact: set2_P. Qed.

Lemma A3 x x' y y': J x y = J x' y' -> (x=x' /\ y = y').
Proof. exact:  pr12_def. Qed.
  
Lemma A4 X: collectivizing (fun Y => sub Y X).
Proof. exists (\Po X) => z; exact : setP_P. Qed.
  


Lemma Zo_exists E (p: property): AS8_def ->
  exists F, forall x, inc x F <-> inc x E /\ p x. 
Proof.
move => ax.
pose R (x y: Set) :=  inc x E /\ p  x.
have hyp: forall y, exists Y, forall x, R x y-> inc x Y.
  by move => y; exists E => x [].
move: (ax R hyp E) => [T tp]; exists T => y; split.
  by move/tp => [Y _]. 
by move => [qa qb]; apply/tp; exists y.
Qed.


Lemma fun_image_exists E (f: fterm): AS8_def ->
  exists F, forall x, inc x F <->  exists2 y, inc y E & x = f y. 
Proof.
move => ax.
pose R x y:=  x  = f y /\ inc y E.
have hyp: forall y, exists Y, forall x, R x y-> inc x Y.
  move => y.  exists (singleton (f y)); move => x [-> _]; fprops. 
move: (ax R hyp E) => [T tp]; exists T => y; split.
  move/tp =>[u ua [ub ucØ]]; ex_tac.
by move => [i ia ib]; apply/tp; ex_tac.
Qed.
  
Lemma union_exists X: AS8_def ->
  exists T, forall t, inc t T <-> exists2 i, inc i X & inc t i.
Proof.
move => ax.
pose R x y:= inc y X /\ inc x y.
have hyp: forall y, exists Y, forall x, R x y-> inc x Y.
  by move => y; exists y; move => x []. 
move: (ax R hyp X) => [T tp]; exists T => y.
split; first by  move/tp =>[u ua [ub ucØ]]; ex_tac.
by move => [i ia ib]; apply/tp; ex_tac. 
Qed.
  

Lemma unionf_exists I (f: fterm): AS8_def ->
  exists T, forall t, inc t T <->
    (exists2 y, inc y I & inc t (f y)).
Proof.
move => ax.
pose R x y:= inc y I /\ inc x (f y).
have hyp: forall y, exists Y, forall x, R x y-> inc x Y.
  by move => y; exists (f y); move => x []. 
move: (ax R hyp I) => [T tp]; exists T => y.
split; first by   move/tp =>[u ua [ub ucØ]]; ex_tac.
by move => [i ia ib]; apply/tp; ex_tac. 
Qed.

Lemma empty_alt (x := IM (fun z: False => bool)) :
  x = emptyset.
Proof.
have H t: ~ (inc t x) by  move /IM_P => [y]; case: y.
set_extens t; [ case/H | case; case ].
Qed.

End Baxioms.


Module Exercise1.
Lemma rel_False: emptyset = False.
Proof. by symmetry;apply /set0_P => t; case; case. Qed.

Lemma rel_True: singleton (Ro I) = True.
Proof.
apply: extensionality.  
  move => t /set1_P ->; apply: R_inc.
move => t [a <-]; apply /set1_P. 
have -> //: a = I by case:a.
Qed.


(** [\not\in] is not collectivizing *)
Lemma not_collectivizing_notin: 
  ~ (exists z, forall y, inc y z <-> not (inc y y)).
Proof. 
case=> x hx; move: (hx x) => [p p'].
pose H:= (fun h : inc x x => (p h h));exact (H (p' H)).
Qed.

(** There is a set containing no set, and no set containg all sets *) 
Lemma collectivizing_special :
  (exists x, forall y, ~ (inc y x)) /\  ~ (exists x, forall y, inc y x).
Proof. 
split; first by exists emptyset; apply: in_set0.
move=> [x Px]; apply: not_collectivizing_notin.
exists (Zo x (fun z => ~ (inc z z))) => z.
by split;[ case /Zo_P | move => zz; apply:Zo_i].
Qed. 

(** Any property [p] is true for the elements of the empty set *)
Lemma emptyset_pra x (p: property):
  inc x emptyset -> (p x).
Proof. case; case. Qed.

(** ** Section 1 *)

(** Exercise 1.1: reverted extensionality  *)
Section exercise1_1.
Variable x y:Set.

Lemma exercise1_1: (x=y) <-> (forall X, inc x X -> inc y X).
Proof.
split; first by move=> ->.
move=> spec_sub; symmetry; apply: set1_eq; apply: spec_sub; fprops.
Qed.

End exercise1_1.

(** Exercise 1.2: [emptyset <> singleton x] and there are at least two different sets  *)

Lemma exercise1_2: exists x y:Set, x <> y.
Proof. 
have theorem:forall x, emptyset <> singleton x. 
  by move=> x esx; empty_tac1 x.
by exists emptyset; exists (singleton emptyset); apply: theorem.
Qed.

(** Exercise 1.3: [sub] and [complement] *)
Lemma exercise1_3 X A B (compl := fun z => X -s z) :
  sub A X -> sub B X ->
  ((sub (compl B) A <-> sub (compl A) B)   /\ 
   (sub B (compl A) <-> sub A (compl B))).
Proof. 
have aux1: forall a b, sub a X -> sub b X ->
   (sub (compl a) b <-> a \cup b = X).
  move => a b aX bX; split.
    move => s1; set_extens t; first by case /setU2_P => ts; fprops.
    rewrite - (setU2_Cr aX); case /setU2_P => ts; fprops.
  by rewrite /compl => <- t /setC_P [/setU2_P] [].
have aux2: forall a b, sub a X -> sub b X ->
   (sub b (compl a)  <-> a \cap b = emptyset).
  move => a b aX bX; split.
    move => s1; apply /set0_P =>t /setI2_P [ta tb].
    by move /setC_P: (s1 _ tb) => [].
  move => abe t tb; apply /setC_P; split; fprops.
  move => ta; empty_tac1 t.
move => ax bx; split.
   apply: (iff_trans (aux1 _ _ bx ax)); rewrite setU2_C.
   by apply: iff_sym; apply/aux1.
apply: (iff_trans (aux2 _ _ ax bx)); rewrite setI2_C.
by apply: iff_sym; apply/aux2.
Qed.

(** Exercise 1.4: subsets of a singleton *)
Lemma exercise1_4 X x:
  sub X (singleton x) <-> (X = singleton x \/ X = emptyset).
Proof. 
split; last by case => ->; fprops. 
move => asx; case: (emptyset_dichot X); first by right.
by move => nea; left; apply: set1_pr1 => // z /asx /set1_P.
Qed.


(** Exercise 1.5: Alternate definition of emptyset *)

Lemma exercise1_5:
  emptyset = choose (fun X => ~ (inc (rep X) X)).
Proof.
pose p := fun z => ~  inc (rep z) z.
have pe: p emptyset by exact: in_set0.
move:(choose_pr (ex_intro p emptyset pe)) => pcp.
case:(emptyset_dichot (choose p)) => // ney; by move: (rep_i ney).
Qed.


(** Exercise 1.6: Variant of the axiom of extent. *)
(** We need an axiom that says [choose p = choose q] for equivalent propositions *)

Section Ex1_6.
Hypothesis choose_equiv: forall (p q: property),
  (forall x, p x <-> q x) -> choose p = choose q.

Lemma exercise1_6:
  (forall y, y = choose (fun x => (forall z, (inc z x) <-> (inc z y)))) 
  -> (forall a b : Set, sub a b -> sub b a -> a = b).
Proof. 
move=> hyp a b; rewrite /sub => sab sba. 
rewrite (hyp a) (hyp b).
apply: choose_equiv; move=> x.
split; move=> aux z; rewrite aux; split; auto.
Qed.

End Ex1_6.

(** ** Section 2 *)
(** Exercise 2.1: binary to unary relations. *)

Lemma exercise2_1 (R: relation) :
  ((exists x, exists y, R x y) <-> (exists z, pairp z /\ R(P z) (Q z))) /\
  ((forall x, forall y, R x y) <-> (forall z, pairp z -> R(P z) (Q z))).
Proof.
split;split.
- move=> [x] [y] Rxy; exists (J x y); aw;fprops.
- by move => [z [zp Rz]]; exists (P z); exists (Q z). 
- move=> hyp z _; apply: hyp.
- by move => hyp x y; move: (hyp _ (pair_is_pair x y)); aw.
Qed.

(** Exercise 2.2: the axiom of the pair. *)

Definition xpair (x y : Set) :=
  doubleton (singleton x) (doubleton x (singleton y)).

Lemma exercise2_2 x y z w:
  (xpair x y = xpair z w) <-> (x = z /\ y = w).
Proof.
split; last by move=> [] -> ->.
move => eq.
have fp2: inc (singleton x) (xpair z w) by rewrite -eq /xpair; fprops. 
have sp2: inc (doubleton x (singleton y)) (xpair z w).
  by rewrite -eq /xpair; fprops.
have xz: x=z.
   case /set2_P: fp2; first by apply: set1_inj. 
   by move=> sd; symmetry; apply: set1_eq; ue. 
split=>//.
rewrite xz in sp2.
case /set2_P: sp2 => hyp.  
  symmetry.
  have syz: (singleton y = z) by apply: set1_eq; ue.
  have: (inc (doubleton z (singleton w)) (xpair x y)). 
    by rewrite eq /xpair; fprops. 
  rewrite xz /xpair hyp; move/set1_P => zwz.
  have: (singleton w = z) by apply: set1_eq; ue.
  by rewrite - syz; apply: set1_inj.
apply: set1_inj.
have sp3: (inc (singleton w) (doubleton z (singleton y))) by  ue.
case /set2_P: sp3 => sp4; last by symmetry.
have sp5: (inc (singleton y) (doubleton z (singleton w))) by ue.
by case /set2_P: sp5; try ue.
Qed.

(** ** Section 3 *)
(** Exercise 3.1: Some equivalences without graph *)
Definition has_no_graph (r:relation):=
 ~(exists G, forall x y, r x y -> inc (J x y) G).
Definition is_universal (r:relation):=
  forall x, exists y, r x y \/ r y x.

Lemma is_universal_pr r:  is_universal r -> has_no_graph r.
Proof. 
move=> u [X h].
case:(proj2 collectivizing_special). 
exists ((domain X) \cup (range X)) => y.
move: (u y) => [x [] /h jg]; apply /setU2_P; [left | right];ex_tac.
Qed.

Lemma exercise3_1:
  [/\  has_no_graph (fun x y => inc x y),
       has_no_graph (fun x y => sub x y) &
       has_no_graph (fun x y => x = singleton y) ].
Proof. 
split; apply: is_universal_pr; move=> x;
  [ exists (singleton x) | exists x |  exists (singleton x) ] ; fprops.
Qed.

(** Exercise 3.2: Some properties of a graph *)
Lemma exercise3_2 G X: sgraph G ->
  ( sub X (domain G) <->
    sub X (direct_image (inverse_graph G) (direct_image G X))).
Proof. 
move=> gG.
split; move=> hyp t ts; move: (hyp _ ts).
  move/(domainP gG)=> [y Jg]; apply/dirim_P;exists y.
    apply/dirim_P; ex_tac.
  by apply/igraph_pP.
move/dirim_P => [x _] /igraph_pP h; ex_tac.
Qed. 

(** Exercise 3.3: Some properties of a graph *)

Lemma exercise3_3a G H: sgraph G -> sgraph H ->
  ( sub (domain H) (domain G) <->
    sub H (H \cg ((inverse_graph G) \cg G))).
Proof. 
move=> gG gH.
split => h t ts.
  move: (gH _ ts) => Jt; rewrite - Jt  in ts.
  have: (inc (P t) (domain G)) by apply: h; ex_tac.
  move /(domainP gG)=> [y JG]; apply /compg_P; split => //; ex_tac.
  by apply /compg_pP; ex_tac; apply/igraph_pP.
move /(domainP gH): ts => [y JH]. 
move: (h _ JH) => /compg_pP [z /compg_pP [u q _] _]; ex_tac.
Qed.

Lemma exercise3_3b G: sgraph G ->
  sub G (G \cg ((inverse_graph G) \cg G)).
Proof. move=> gG; apply /(exercise3_3a gG gG); fprops. Qed.

(** Exercise 3.4: Some properties of the empty graph *)

Lemma exercise3_4a G:
  ( emptyset \cg G = emptyset
  /\ G \cg emptyset = emptyset).
Proof. 
split; apply /set0_P => x /compg_P [_]. 
  by move => [y _ /in_set0].
by move => [y  /in_set0].
Qed.


Lemma exercise3_4b G: sgraph G ->
  ((inverse_graph G) \cg G = emptyset <-> G = emptyset).
Proof.
move=> gG; split => h; last by rewrite h; apply: (proj2 (exercise3_4a _)).
apply /set0_P => x xG; empty_tac1 (J (P x) (P x)).
move:(eq_ind_r (inc^~ G) xG (gG x xG)) => px.
by apply/compg_pP; exists (Q x) => //; apply /igraph_pP.
Qed.

(** Exercise 3.5: graphs and products *)

Lemma exercise3_5 G A B:
  ((A \times B) \cg G = (inverse_image G A) \times B /\
   G \cg (A \times B)  = A \times (direct_image G B)).
Proof. 
split; set_extens x.
- move /compg_P => [px [y yG /setXp_P [pa pb]]].
  apply/setX_P;split => //; apply/iim_graph_P; ex_tac.
- move /setX_P => [px /iim_graph_P [y uA JG] QB].
  apply /compg_P; split => //; ex_tac; fprops.
- move /compg_P => [px [y /setXp_P [pa pb pc]]].
  apply /setX_P;split => //; apply/dirim_P; ex_tac.
- move  /setX_P => [px pxa /dirim_P [y ya yb]].
  apply/compg_P; split => //; ex_tac; fprops.
Qed.

(** Exercise 3.6: complements of a graph *)
Definition complement_graph G :=
  ((domain G) \times (range G)) -s G.

Lemma complement_graph_g G: sgraph (complement_graph G).
Proof. by move => t /setC_P [] /setX_P [ok _] _. Qed.

Lemma exercise3_6a G: sgraph G -> commutes_at complement_graph inverse_graph G.
Proof. 
move => gG.
have gc: sgraph (complement_graph G) by apply: complement_graph_g.
rewrite /commutes_at/complement_graph (igraph_range gG)(igraph_domain gG).
set_extens t.
  move /setC_P => [/setX_P [pt pa pb] pc].
  apply /igraphP; split => //; apply/ setC_P;split; first by fprops. 
  by move /igraph_pP; rewrite pt.
move /igraphP => [px /setC_P [/setXp_P [pa pb] pc]].
apply/setC_P; rewrite - px; split; [ fprops | by move /igraph_pP].
Qed. 

Lemma exercise3_6b G B: sgraph G -> sub (range G) B ->
  sub (G \cg (complement_graph (inverse_graph G)))
      (complement_graph (diagonal B)).
Proof.
move=> gG srB; rewrite exercise3_6a // => t.
move /compg_P => [pt [y /igraph_pP /setC_P [/setXp_P [pa pb] pc] pd]].
apply/setC_P; split; last by move /diagonal_i_P => [_ _ eq]; case: pc; ue.
move:(@identity_sgraph B); rewrite - diagonal_is_identity => aux.
apply /setX_i => //.
  apply/(domainP aux); exists(P t); apply /diagonal_pi_P; fprops.
apply/(rangeP aux);  exists(Q t);apply /diagonal_pi_P. 
split => //; apply: srB; ex_tac.
Qed.

Lemma exercise3_6c A G: sgraph G -> sub (domain G) A ->
  sub ((complement_graph (inverse_graph G)) \cg G)
      (complement_graph (diagonal A)).
Proof.
move=> gG sd. 
rewrite (exercise3_6a gG) => t.
move /compg_P => [pt [y pa /igraph_pP /setC_P [/setXp_P [pb pc] pd]]].
apply/setC_P; split; last by move /diagonal_i_P => [_ _ eq];case: pd; ue.
move:(@identity_sgraph A); rewrite - diagonal_is_identity => aux.
apply /setX_i => //.
   apply/(domainP aux); exists(P t); apply /diagonal_pi_P. 
  split => //; apply: sd; ex_tac.
apply/(rangeP aux);  exists(Q t); apply /diagonal_pi_P; fprops.
Qed.


Lemma exercise3_6d G: sgraph G ->
  ( G = (domain G) \times (range G) <->
   G \cg ((complement_graph (inverse_graph G)) \cg G)
    = emptyset ).
Proof. 
move=> gG; rewrite (exercise3_6a gG). 
transitivity (complement_graph G = emptyset).
  rewrite /complement_graph; split;first by move => <-; apply: setC_v.
  move => h; move:(empty_setC h) => aux; apply: extensionality => //.
  apply: (sub_graph_setX gG).
split.
  move=> ->; rewrite igraph0.
  by move: (exercise3_4a G) => [-> ->].
move=> ce; apply /set0_P => x xK. 
move: (xK); move /setC_P => [] /setX_P [pa] 
     /(domainP gG) [u J1G] /(rangeP gG) [v J2G] _.
empty_tac1 (J v u); apply /compg_pP; ex_tac; apply /compg_pP; ex_tac.
by apply/igraph_pP; rewrite pa.
Qed.

(** Exercise 3.7: Functional graphs *)
Lemma exercise3_7 G: sgraph G ->
  (fgraph G <-> forall X, sub (direct_image G (inverse_image G X)) X).
Proof.
move=>gG; split. 
  move=> fgG X x /dirim_P [y /iim_graph_P [u ux pug] pxg].
  by rewrite (fgraph_pr fgG pxg pug).
move=> hyp; split =>// x y xG yG sP.
move:(gG _ xG) (gG _ yG)=> px py.
apply: pair_exten=>//; apply: set1_eq.
apply: (hyp (singleton (Q y))). 
apply/dirim_P; exists (P x); last by rewrite px.
by apply /iim_graph_P; exists (Q y); fprops; rewrite sP py.
Qed.

(** Exercise 3.8: Characterisation of an inverse via images of singletons *)

Lemma exercise3_8 G G': correspondence G -> correspondence G' ->
  source G = target G' -> source G' = target G ->
  (forall x, inc x (source G) -> Vfs G' (Vfs G (singleton x))
    = singleton x) ->
  (forall x, inc x (source G') -> Vfs G (Vfs G' (singleton x))
    = singleton x) ->
  [/\ bijection G, bijection G' & G = inverse_fun G'].
Proof. 
rewrite /Vfs=>  cG cG' sG sG' G'Gx GG'x.
have gG: sgraph (graph G) by fprops. 
have gG': sgraph (graph G') by fprops. 
have sGdgG: source G = domain (graph G).
  apply: extensionality; last by fprops. 
  move=> x xs; move: (set1_1 x); rewrite - (G'Gx _ xs). 
  move /dirim_P => [y] /dirim_P [t /set1_P -> aa _]; ex_tac.
have sGdgG': source G' = domain (graph G').
  apply: extensionality; last by fprops. 
  move=> x xs; move: (set1_1 x); rewrite - (GG'x _ xs). 
  move /dirim_P => [y] /dirim_P [t /set1_P -> aa _]; ex_tac.
have JGG' x y z: inc (J x y)(graph G) -> inc (J y z)(graph G') -> x = z.
  move=>  Jxy Jyz.
  have xG: inc x (source G) by rewrite sGdgG; ex_tac.    
  symmetry; apply: set1_eq.
  rewrite - (G'Gx _ xG); apply /dirim_P; ex_tac;  apply /dirim_P; ex_tac.
  fprops.
have JG'G x y z: inc (J x y)(graph G') -> inc (J y z)(graph G) -> x = z.
  move=> Jxy Jyz.
  have xG: inc x (source G') by rewrite sGdgG'; ex_tac.    
  symmetry; apply: set1_eq.
  rewrite - (GG'x _ xG); apply /dirim_P; ex_tac;  apply /dirim_P; ex_tac.
  fprops.
have xGy x: inc x (source G) -> exists2 y,
    inc (J x y) (graph G) & inc (J y x) (graph G').
  move=> xsG; move: (set1_1 x).
  rewrite - (G'Gx _ xsG); move /dirim_P => [y /dirim_P [z /set1_P -> pb pc]].
  ex_tac.
have xG'y x: inc x (source G') -> exists2 y,
    inc (J x y) (graph G') & inc (J y x) (graph G).
  move=> xsG;  move: (set1_1 x).
  rewrite - (GG'x _ xsG); move /dirim_P => [y /dirim_P [z /set1_P -> pb pc]]. 
  ex_tac.
have fgG: fgraph (graph G).
  split=>//; move=> x y xG yG Pxy.
  have px: pairp x by apply: gG.
  have py: pairp y by apply: gG. 
  apply: pair_exten =>//.
  rewrite - px in xG.
  rewrite - py -Pxy in yG.
  have Pxs: inc (P x) (source G) by rewrite sGdgG;  ex_tac. 
  move: (xGy _ Pxs) => [z _ J2g].  
  by rewrite -  (JG'G _ _ _ J2g xG)  - (JG'G _ _ _ J2g yG).
have fgG': fgraph (graph G').
  split=>//; move=> x y xG yG Pxy.
  have px: pairp x by apply: gG'.
  have py: pairp y by apply: gG'. 
  apply: pair_exten =>//.
  rewrite  - px in xG.
  rewrite  - py -Pxy in yG.
  have Pxs: inc (P x) (source G') by rewrite sGdgG';  ex_tac. 
  move: (xG'y _ Pxs) => [z _ J2g].  
  by rewrite -  (JGG' _ _ _ J2g xG) - (JGG' _ _ _ J2g yG). 
have fg: function G by [].
have fg': function G' by [].
have GiG:  (graph G = inverse_graph(graph G')). 
  set_extens x => xs.
    have px: pairp x by apply: gG. 
    rewrite - px in xs |- *; apply/igraph_pP.
    have Ps: inc (P x) (source G) by rewrite sGdgG; ex_tac.
    move: (xGy _ Ps)=> [y J1 J2]. 
    by rewrite -(JG'G _ _ _ J2 xs).
  have gi: (sgraph (inverse_graph (graph G'))) by fprops. 
  have px: pairp x by apply: gi.
  move: xs; rewrite - px;move/igraph_pP => xs; rewrite -px.
  have Ps: inc (P x) (source G).
    rewrite  sG; apply: corresp_sub_range=>//; ex_tac. 
  move: (xGy _ Ps)=> [y J1 J2]. 
  by aw;rewrite (JG'G _ _ _  xs J1).
have GiG2: (G = inverse_fun G'). 
  rewrite /inverse_fun - sG sG' -GiG.
  by symmetry; apply: corresp_recov1.
have bG: bijection G.
  split.
    split=>// x y xs ys sW.
    move: (Vf_pr3 fg xs) => HGx. 
    move: (Vf_pr3 fg ys) => HGy; rewrite - sW in HGy.
    have Ws: inc (Vf G x) (source G') by rewrite sG';  fprops.
    move: (xG'y _ Ws) => [z J1 J2]. 
    by rewrite (JGG' _ _ _ HGx J1) (JGG' _ _ _ HGy J1).
  apply: surjective_pr5 =>// x. 
  rewrite - sG' => xs.  
  move: (xG'y _ xs) =>  [z J1 J2].
  rewrite /related; ex_tac; apply: (p1graph_source fg J2).
have GiG3: G' = inverse_fun G by rewrite GiG2 ifun_involutive. 
by split => //; rewrite GiG3; apply: inverse_bij_fb. 
Qed.

(** Exercise 3.9: property of bijections *)

Lemma exercise3_9 f g h:
  function f -> function g -> function h->
  source g = target f -> source h = target g ->
  bijection (g \co f) -> bijection (h \co g) ->
  [/\ bijection f, bijection g & bijection h].
Proof.
move=> ff fg fh sgtf shtg bgf bhg.
have cgf : g \coP f by [].
have chg : h \coP g by [].
have ig: injection g. 
  by move: bhg=>[ia sa]; apply: (right_compose_fi chg ia).
have sg: surjection g. 
  by move: bgf=>[ia sa]; apply: (left_compose_fs cgf sa).
have bg: bijection g by split. 
split => //.
  apply: (right_compose_fb cgf bgf bg). 
apply: (left_compose_fb chg  bhg bg). 
Qed.

(** Exercise 3.10: property of bijections *)
Lemma exercise3_10 f g h:
  function f -> function g -> function h->
  source g = target f -> source h = target g ->  source f = target h ->
  injection (h \co (g \co f)) ->
  surjection (g \co  (f \co h)) ->
  (injection (f \co (h \co g)) 
   \/ surjection (f \co (h \co g))) ->
  [/\ bijection f, bijection g & bijection h].
Proof. 
move=> ff fg fh sgtf shtg sfth ihgf sgfh is_fgh.
have cfh: f \coP h by [].
have chg: h \coP g by [].
have cgf: g \coP f by [].
rewrite  compfA // in ihgf.
have fhg: function (h \co g) by  fct_tac.
have chgf:  (h \co g) \coP f by hnf; aw.
move: (right_compose_fi chgf ihgf) => inf.
have ffh: function (f \co h) by fct_tac.
have cgfh: g \coP (f \co h) by hnf; aw.
move: (left_compose_fs  cgfh sgfh) => sg.
case is_fgh.
  rewrite compfA// => ifhg. 
  have cfhg: (f \co h) \coP g by hnf; aw. 
  move: (right_compose_fi cfhg ifhg) => ig.
  move: (left_compose_fs2 cgfh sgfh  ig)=> sfh. 
  move: (left_compose_fs cfh sfh) =>sf. 
  move: (left_compose_fi2 cfhg ifhg sg) => ifh. 
  have bfh: (bijection (f \co h)) by [].
  have bf: (bijection f)  by [].
  have bg: (bijection g)  by [].
  move: (right_compose_fb cfh bfh bf).
  done.
move=> sfhg.
have cfhg: (f \coP (h \co g)) by hnf; aw.
move: (left_compose_fs cfhg  sfhg) => sf.
have bf: (bijection f)  by [].
move: (left_compose_fs2 cfhg sfhg inf) => shg. 
move:(left_compose_fi2 chgf ihgf sf) => ihg.
move: (right_compose_fi chg ihg) => ig. 
have bg: (bijection g)  by [].
have bhg: (bijection (h \co g)) by [].
move: (left_compose_fb chg bhg bg).
done.
Qed.

(** Exercise 3.11: no associated code *)

(** ** Section 4 *)
(** Exercise 4.1:  functional graph and inverse image *)

Lemma exercise4_1a g: sgraph g  ->
  (functional_graph g <-> {morph inverse_image g : x y / x \cap y}).
Proof.
move=> gg.
have gig: sgraph (inverse_graph g) by  fprops. 
split.
  move=> fgg x y; set_extens t. 
    move /iim_graph_P => [u /setI2_P [ux uy] jg].
    apply /setI2_P;split;apply /iim_graph_P; ex_tac.
  move /setI2_P => [ /iim_graph_P [u ux ua] /iim_graph_P [v vx va]]. 
  rewrite -(fgg _ _ _ ua va) in vx.
  apply /iim_graph_P; exists u; fprops. 
move=> hyp x y y' gxy gxy'.
move: (hyp (singleton y)(singleton y')).  
set u:= _ \cap _ => hyp1.
have:inc x (inverse_image g u).
  rewrite /u hyp1;apply: setI2_i; apply /iim_graph_P.
    exists y; fprops.
    exists y'; fprops.
by move /iim_graph_P => [t /setI2_P [/set1_P  <- /set1_P  <-]].
Qed.

Lemma exercise4_1b g: sgraph g  ->
  (functional_graph g <-> (forall x y, disjoint x y ->
    disjoint (inverse_image g x) (inverse_image g y))).
Proof. 
rewrite /disjoint;move=> gg; split.
  move /(exercise4_1a gg) => h x y ie; rewrite /disjoint -h ie.
  by rewrite /inverse_image dirim_set0.
move=> hyp x y y' gxy gxy'.
have gig: sgraph (inverse_graph g) by fprops.
case: (emptyset_dichot ((singleton y) \cap (singleton y'))).
  move=>aux; move:(hyp _ _ aux).
  set v:=  _ \cap _ => ve.
  have: (inc x v) by rewrite /v; apply: setI2_i; apply /iim_graph_P; ex_tac.
  by rewrite ve => /in_set0.
by move=> [z /setI2_P [/set1_P -> /set1_P ->]].
Qed.

(** Exercise 4.2: Image and  interesection *)
Lemma exercise4_2a g x: 
  direct_image g x = range (g \cap (x \times (range g))).
Proof. 
set_extens y. 
  move /dirim_P => [a ax pg]; apply/funI_P;  exists (J a y); aw;trivial.
  apply /setI2_P; split => //; apply:setXp_i => //; ex_tac.
move /funI_P => [a  /setI2_P [pg /setX_P [pa pb pc]] ->].
by apply/dirim_P; ex_tac; rewrite pa.
Qed.

Lemma exercise4_2b g x: 
  direct_image g x = direct_image g (x \cap (domain g)).
Proof. 
set_extens t; move /dirim_P => [y ys Jg];  apply/dirim_P.
  ex_tac; apply /setI2_P; split=> //; ex_tac.
move /setI2_P: ys => [pa pb]; ex_tac. 
Qed.

(** Exercise 4.3: composition of product *)

Lemma exercise4_3a x y y' z: disjoint y y' ->
  (y' \times z) \cg (x \times y) = emptyset.
Proof. 
rewrite /disjoint => ie; apply /set0_P.
move=> t => /compg_P [_ [u /setXp_P [_ uy] /setXp_P [uy' _]]].
by empty_tac1 u. 
Qed.

Lemma exercise4_3b x y y' z: nonempty(y \cap y') ->
  (y' \times z) \cg (x \times y) = x \times z.
Proof. 
move=> [t /setI2_P [ty ty']].
set_extens u.
  move /compg_P => [pu [v /setXp_P [pa _] /setXp_P [_ pb]]]. 
  by apply:setX_i.
move => /setX_P [pu Px Qy]; apply/compg_P; split => //; exists t; fprops.
Qed.

(** Exercise 4.4: image of union or intersection  *)

Definition graph_morph op ui g := 
    op (ui g) = ui (Lg (domain g) (fun i => op (Vg g i))).

Lemma exercise4_4a g x: graph_morph (direct_image^~x) unionb g.
Proof.
set_extens y.
  move => /dirim_P [a ax /setUb_P [u ud Jv]].
  apply: (@setUb_i _ u); aw; trivial;rewrite LgV //; apply /dirim_P; ex_tac.
move /setUb_P => [z]; rewrite Lgd => zd; rewrite LgV//.
move /dirim_P => [u ux Jv]; apply /dirim_P; ex_tac; union_tac.
Qed.


Lemma exercise4_4b g x: singletonp x ->
  graph_morph (direct_image^~x) intersectionb g.
Proof.
move=> [y ->]; set_extens t.
  move => /dirim_P [a /set1_P ->].
  case: (emptyset_dichot g) => gne; first by rewrite gne setIb_0 => /in_set0.
  move => pi; apply: setIb_i.
     move /domain_set0P: gne => [u udg].
     pose ff i := direct_image (Vg g i) (singleton y).
     exists (J u (ff u)); apply /funI_P; ex_tac.
  aw; move => i idg; rewrite LgV//; apply/dirim_P; exists y; fprops.
  exact (setIb_hi pi idg). 
set f := Lg _ _.
have dfdf: domain f = domain g by rewrite /f; aw.
case: (emptyset_dichot g) => gne.
  by rewrite /f gne domain_set0 /Lg funI_set0 setIb_0 => /in_set0.
move => ti; apply /dirim_P; exists y; first by fprops.
apply/(setIb_P gne) => i idg; move: (idg); rewrite -dfdf=>  idf.
by move: (setIb_hi ti idf); rewrite LgV//; move /dirim_P => [u /set1_P ->].
Qed.

Lemma exercise4_4c: exists z,  not {morph (direct_image ^~z): x y / x \cap y}.
Proof.
exists C2.
set (G:= doubleton(J C0 C0)(J C1 C1)); set  (H:=  doubleton(J C0 C1)(J C1 C0)). 
move => h; move: {h} (h G H).
have ->: direct_image G C2 = C2. 
  set_extens u.
    move=> /dirim_P [v vz /set2_P] [] h; rewrite (pr2_def h); fprops.
  case /set2_P => h; apply /dirim_P; exists u; rewrite h /G; fprops.
have -> :direct_image H C2 = C2. 
  set_extens u. 
     move=> /dirim_P [v vz /set2_P] [] h; rewrite (pr2_def h); fprops.
  case /set2_P => ->; apply /dirim_P;  [ exists C1 | exists C0]; 
     rewrite /H;fprops.
rewrite setI2_id => bad.
move: inc_C0_C2; rewrite -bad; move/dirim_P => [t _ /setI2_P[pa]].
have : P (J t C0) = Q (J t C0) by case/set2_P: pa => ->; aw.
aw => ->; case/set2_P => h; [move: (pr2_def h) | move: (pr1_def h)]; fprops.
Qed.

(** Exercise 4.5: compose and union  *)

Lemma exercise4_5 G H:
   graph_morph (composeg ^~H) unionb G
   /\ graph_morph (composeg H) unionb G.
Proof.
split.
  set_extens x. 
    move /compg_P => [px [y ph/setUb_P [z zd JV]]]. 
    apply/setUb_P; aw; ex_tac.
      rewrite LgV//; apply /compg_P;split => //; ex_tac.
  move /setUb_P; aw; move => [y ydg]; rewrite LgV//.
  move /compg_P => [px [t pa pb]].
  apply /compg_P;split=> //;ex_tac; union_tac.
set_extens x.
  move /compg_P => [px [y /setUb_P [z zd JV] ph]].
  apply/setUb_P; aw; ex_tac; rewrite LgV//; apply /compg_P;split => //; ex_tac.
move /setUb_P; aw; move => [y ydg]; rewrite LgV//.
move /compg_P => [px [t pa pb]].
apply /compg_P;split => //;ex_tac; union_tac.
Qed.

(** Exercise 4.6: functional graph: compose and intersection  *)

Lemma exercise4_6 G: sgraph G ->
  (fgraph G <-> 
  {when sgraph &, {morph (composeg ^~G) : H H' / H \cap H'}}). 
Proof.
move => gG; split.
  move=> fG H H' _ _; set_extens x.
    move /compg_P => [px [y J1 /setI2_P [J2 J3]]].
    apply: setI2_i; apply /compg_P; split => //;ex_tac.
  move /setI2_P => [] /compg_P [px [y J1 J2 /compg_P [_ [y' J1' J2']]]].
  rewrite  (fgraph_pr fG J1 J1') in J2.
  apply/compg_P; split => //; ex_tac; fprops.
move=> hyp; split=>// x y xG yG Pxy.
set (H:= singleton(J (Q x) (P x))).
set (H':= singleton(J (Q y) (P y))). 
have gh: sgraph H by move=> t /set1_P ->; fprops.
have gh': sgraph H' by move=> t /set1_P->; fprops. 
move: (gG _ xG)(gG _ yG)=> xp yp. 
rewrite - xp in xG.
rewrite - yp in yG.
apply: pair_exten=>//.
have p1: inc (J (P x)(P x)) (H \cg G).
  apply /compg_P; split;fprops; aw;ex_tac; rewrite /H;  fprops.
have p2: inc (J (P y)(P y)) (H' \cg  G).
  apply /compg_P; split;fprops; aw;ex_tac; rewrite /H';  fprops.
have : (inc (J (P x)(P x)) ((H \cap H') \cg G)).
  by rewrite hyp//; apply: setI2_i => //;rewrite Pxy.
move/compg_P => [_ [z _]]; aw.
move /setI2_P => [] /set1_P r1 /set1_P r2.
by rewrite -(pr1_def r1) -(pr1_def r2).
Qed. 

Lemma exercise4_6bis G: sgraph G ->
  (fgraph G <-> {morph (composeg^~G) : H H' / H \cap H'}).
Proof.
move => gG; split.
  move=> fG H H'; set_extens x.
    move /compg_P => [px [y J1 /setI2_P [J2 J3]]]. 
    apply :setI2_i; apply /compg_P;split => //;ex_tac.
  move /setI2_P => [] /compg_P [px [y J1 J2 /compg_P [_ [y' J1' J2']]]].
  rewrite  (fgraph_pr fG J1 J1') in J2.
  apply/compg_P; split => //; ex_tac; fprops.
move=> hyp; split=>// x y xG yG Pxy.
set (H:= singleton(J (Q x) (P x))).
set (H':= singleton(J (Q y) (P y))). 
move: (gG _ xG)(gG _ yG)=> xp yp. 
rewrite - xp in xG.
rewrite - yp in yG.
apply: pair_exten=>//.
have p1: inc (J (P x)(P x)) (H \cg G).
  apply /compg_P; split;fprops; aw;ex_tac; rewrite /H;  fprops.
have p2: inc (J (P y)(P y)) (H' \cg  G).
  apply /compg_P; split;fprops; aw;ex_tac; rewrite /H';  fprops.
have: (inc (J (P x)(P x)) ((H \cap H') \cg G)).
  by rewrite hyp; apply: setI2_i => //;rewrite Pxy.
move/compg_P => [_ [z _]]; aw.
move /setI2_P => [] /set1_P r1 /set1_P r2.
by rewrite -(pr1_def r1) -(pr1_def r2).
Qed.

(** Exercise 4.7: properties of graphs  *)

Lemma exercise4_7 G H K:
  sub ((H \cg G) \cap K) 
     ((H \cap (K \cg (inverse_graph G))) 
      \cg  (G \cap ((inverse_graph H) \cg K))).
Proof.
move=> t /setI2_P [] /compg_P [tp [y JG JH]] tK.
apply /compg_P;split =>// ;rewrite - tp in tK.
by exists y; apply : setI2_i => //; apply/compg_P;
   split;fprops; aw; ex_tac; apply /igraph_pP.
Qed.


(** Exercise 4.8: A property of coarser coverings and two counter-examples *)
Lemma exercise4_8a r s x:
  covering r x -> covering s x ->
  partition_w_fam s x ->  coarser_cg s r ->
  nonempty_fam s ->
  forall k, inc k (domain s) -> 
      exists2 i, inc i(domain r) & sub (Vg r i) (Vg s k).
Proof. 
move=> [fgr co1] [fgs co2] [fgL md usx] [_ _ co] alne k kds.
move: (alne _ kds)=> [y ysk].
have yx: inc y x by rewrite -usx;apply: (@setUb_i _ k);aw. 
have yu: inc y (unionb r) by apply: co1.
move: (setUf_hi yu)=> [z zdr yrz]. 
move: (co _ zdr)=> [i ids rsi].
have yri: inc y (Vg s i) by apply: rsi.
move: md; rewrite /mutually_disjoint; aw=> aux; case: (aux _ _ kds ids).
  by move=> ->; ex_tac.
by move=> h; empty_tac1 y;aw; split.
Qed.

Hint Rewrite variant_d variant_V_a variant_V_b:  bw.


Lemma exercise4_8b 
  (r:= Lg (singleton C0) (fun _ => C2))
  (s:= variantL C0 C1 C2 (singleton C0)) :
    [/\ covering r C2, covering s C2,
      coarser_cg s r,
      nonempty_fam s &
      ~(forall k, inc k (domain s) -> 
             exists i, inc i (domain r) /\ sub (Vg r i) (Vg s k))].
Proof.
have ba := C1_ne_C0.
rewrite /r/s;split.
- split; fprops; move=> t tx; apply: (@setUb_i _ C0); fprops; aw; fprops.
  rewrite LgV; fprops.
- split; fprops; move=> y yx;apply: (@setUb_i _ C0); fprops; aw; fprops.
- split; fprops; aw => t /set1_P  ->; exists C0; first fprops.
  aw; rewrite  LgV;fprops.
- move=> k; aw => kd ;rewrite LgV //;case /set2_P:kd=> ->; aw;apply: set2_ne. 
  aw; move=> h; move: (h _ inc_C1_C2)=> [i [/set1_P ->]]; aw.
  rewrite LgV; fprops => xa.
  by move: (xa _ inc_C1_C2) => /set1_P.
Qed.


Lemma exercise4_8c
  (x:= C4) 
  (r:= (Lg C3
     (fun i=>  Yo (i = C0) (singleton C0)
      (Yo (i = C2) (singleton C1) (doubleton C2 C3)))))
  (s:= variantL C0 C1 (doubleton C0 C2) (doubleton C1 C3)):
  [/\ partition_w_fam s x,
      partition_w_fam r x,
     (forall k, inc k (domain s) ->
       exists2 i, inc i (domain r) & sub (Vg r i) (Vg s k)) &
     ~(coarser_cg s r)].
Proof.
move:C2_ne_C01 => [n1 n2].
move:C3_ne_C012 => [n3 n4 n5].
have nba: C1 <> C0 by fprops.
have sab:  (disjoint (Vg s C0) (Vg s C1)).
  rewrite /s; aw; apply: disjoint_pr=>u ud1 ud2.
  case /set2_P: ud1=> h; case /set2_P: ud2; rewrite h; auto.
have ra: inc C0 C3 by apply /C3_P; in_TP4.
have rb: inc C1 C3 by apply /C3_P; in_TP4.
have rc: inc C2 C3 by apply /C3_P; in_TP4.
have dab: disjoint (Vg r C0) (Vg r C1).
  rewrite !LgV//; Ytac0; Ytac0; Ytac0; Ytac0.
  apply: disjoint_pr=> u /set1_P -> /set2_P; case; auto.
have dac: disjoint (Vg r C0) (Vg r C2).
  rewrite !LgV//; Ytac0; Ytac0; Ytac0; Ytac0.
  apply: disjoint_pr=> u  /set1_P -> /set1_P; auto.
have dcb: disjoint (Vg r C2) (Vg r C1).
  rewrite !LgV//; Ytac0; Ytac0; Ytac0; Ytac0.
  apply: disjoint_pr=> u /set1_P -> /set2_P; case; auto.
split.
(* S partition *) 
  rewrite /s;split; fprops.
    rewrite /variantL;red; aw; move=> i j ids jds. 
    case /set2_P: ids => ->; case /set2_P: jds =>->; auto. 
    by right; apply:disjoint_S.
  set_extens y => ys.
    case (setUb_hi ys); aw; move=> z zd.
    case /set2_P: zd => ->; aw=> yd; case /set2_P: yd => ->; apply/C4_P;in_TP4.
   case /C4_P: ys; move => ->.
     by apply :(@setUb_i _ C0);aw; fprops.
     by apply :(@setUb_i _ C1);aw; fprops.
     by apply :(@setUb_i _ C0);aw; fprops.
     by apply :(@setUb_i _ C1);aw; fprops.
(* R partition *)
   split; first by rewrite /r; fprops.
    red; rewrite {1 2} /r;  aw; move=> i j idr jdr.
    case /C3_P:idr => ->;case /C3_P:jdr;try move => ->; auto; 
      try case => ->; auto;
      by right;apply: disjoint_S.
  set_extens t => ts.
    move: (setUb_hi ts); rewrite /r;aw; move => [y ydr]; rewrite LgV//.
    case /C3_P:ydr => ->; Ytac0; Ytac0; 
        try move /set1_P ->; try case/set2_P => ->; apply /C4_P;in_TP4.
  rewrite /r; case /C4_P: ts;
     [set v := C0 | set v := C2 | set v := C1 | set v := C1 ]; 
     move => ->; apply: (@setUb_i _ v); aw; trivial;
     rewrite LgV//; Ytac0; Ytac0; fprops.
(* property *)
  rewrite /s/r; aw; move => k kds; case /set2_P: kds =>->.
    exists C0 => //; aw;rewrite LgV//; Ytac0; Ytac0 => t /set1_P ->; fprops.
  exists C2 => //; aw; rewrite LgV//; Ytac0; Ytac0 => t /set1_P ->; fprops.
(* not refinement *)
move=> [_ _ ]; rewrite {1}/r;aw => cc.
move: (cc _ rb) => [i]; rewrite /s; aw=> ids.
rewrite LgV//; Ytac0; Ytac0.
case /set2_P: ids=> ->; aw => h.
   move: (h _ (set2_2 C2 C3)) => /set2_P; case; auto.
move: (h _ (set2_1 C2 C3)) => /set2_P; case; auto.
Qed.


(** ** Section 5 *)
(** Exercise 5.1: (french only)  monotonicity of setP  *)

Lemma powerset_mono A B: sub A B -> sub (powerset A)(powerset B).
Proof.
move=> sAB t /setP_P ta; apply/setP_P; apply:(sub_trans ta sAB).
Qed.

Lemma exercise5_f1 x y: sub (powerset x) (powerset y) -> sub x y.
Proof.
move=> sxy z zx.
have p2: sub (singleton z) y. 
 by apply /setP_P; apply: sxy; apply /setP_P => t /set1_P ->.
apply: (p2 z); fprops.
Qed.

(** Exercise 5.2 (french only): greatest and least fix-point  *)
 
Lemma exercise5_f2 f x v w:
  function f -> source f = (powerset x) -> target f = powerset x ->
  (forall a b, inc a (powerset x) -> inc b (powerset x) -> sub a b 
    -> sub (Vf f a) (Vf f b)) ->
  v = intersection(Zo (powerset x) (fun z=> sub (Vf f z) z)) ->
  w = union(Zo (powerset x) (fun z=> sub z (Vf f z))) ->
  [/\ Vf f v = v, Vf f w = w & (forall z, sub z x -> Vf f z = z ->
    (sub v z /\ sub z w))].
Proof.
move=> ff sf tf fprop vd wd.
set (q:= (Zo (powerset x) (fun z => sub (Vf f z) z))).
have xpx: inc x (powerset x) by apply :setP_Ti.
have xiq: inc x q.
  apply: Zo_i=>//.
  by apply /setP_P; rewrite -tf; apply: Vf_target =>//; rewrite sf.
have neq:nonempty q by exists x.
set (p:= (Zo (powerset x) (fun z  => sub z (Vf f z)))).
have fzv:forall z, sub z x -> Vf f z = z -> sub v z. 
  move => z zx Wz.
  have zq:inc z q by apply: Zo_i; [by apply /setP_P | rewrite  Wz; fprops].
  by rewrite vd; apply: setI_s1.
have fzw:forall z, sub z x -> Vf f z = z -> sub z w.
  move => z zx Wz.
  have zp: inc z p by  apply: Zo_i; [by apply /setP_P | rewrite  Wz; fprops].
  by rewrite wd; apply: setU_s1.
have qW: forall z, inc z q -> inc (Vf f z) q. 
   move=> z /Zo_P [] /setP_P zx Wzz.
   have aux := sub_trans Wzz zx.
   by apply: Zo_i; [ apply/setP_P | apply: fprop => //; apply/setP_P].
have pW: forall z, inc z p -> inc (Vf f z) p.
   move=> z /Zo_P [] /setP_P zx Wzz.
   have aux: inc (Vf f z)  (powerset x).
     by rewrite -tf; apply: Vf_target=>//;rewrite sf; apply /setP_P.
   by apply: Zo_i => //; apply: fprop => //; apply/setP_P.
have vp: inc v (powerset x) by  apply /setP_P; rewrite vd; apply: setI_s1. 
have wp: inc w (powerset x). 
   by apply /setP_P; rewrite wd; apply: setU_s2 => y /Zo_P []/setP_P.
have pv:sub (Vf f v) v. 
  move=> t tW; rewrite vd; apply: setI_i=>// y /Zo_P [yp sW]. 
  have vy: sub v y by rewrite vd; apply: setI_s1; apply: Zo_i=>//.
  by apply: sW;apply: (fprop _ _ vp yp vy).
have pw:sub w (Vf f w). 
  move=> t; rewrite {1} wd=> /setU_P [y ty] /Zo_P [yp yW].
  have tw: (sub y w) by rewrite wd;apply: setU_s1; apply: Zo_i=>//.
  by move: (fprop _ _ yp wp tw); apply; apply: yW. 
split. 
   apply: extensionality=>//. 
    have vq: (inc v q) by apply: Zo_i.
    by move: (qW _ vq)=> aux; rewrite {1} vd;apply: setI_s1. 
  apply: extensionality=>//.  
  have iwp: inc w p by  apply: Zo_i. 
  by move: (pW _ iwp) => aux; rewrite {2} wd;apply: setU_s1. 
move=> z zw wz; split; fprops.
Qed.

(** Exercise 5.1: Properties of product  *)
 
Lemma exercise5_1 I x y:
  (forall i, inc i I -> sub (y i) (x i)) -> nonempty I ->
  productf I y = 
  intersectionf I (fun i=> Vfi (pr_i (Lg I x) i) (y i)).
Proof. 
move=> syxi neI.
have fgL: fgraph (Lg I x) by fprops.
have fpj: forall j, inc j I-> function (pr_i (Lg I x) j). 
  by move=> j jI; apply: pri_f=>//;aw.
set_extens t.
  move /setXf_P=> [fgt dt iVy]; apply: setIf_i=>//. 
  move=> j jI; apply /iim_graph_P.
  exists (Vg t j); first by apply: iVy.
  have jd: inc j (domain  (Lg I x)) by aw.
  have tp:(inc t (productb (Lg I x))).
    apply/setXb_P; saw => i iI.   
    by rewrite LgV//; apply: syxi=>//; apply: iVy.
  by rewrite -(pri_V jd tp); Wtac; rewrite /pr_i lf_source.
have rI: inc (rep I) I by apply: rep_i.
move => h; move:(setIf_hi h  rI) => /iim_graph_P [u uy Jg].
move: (p1graph_source (fpj _ rI) Jg).
rewrite /pr_i;aw; move /setXf_P=>[fgt dt iVV].
apply/setXf_P;split => // i idt. 
move: (setIf_hi h  idt) => /iim_graph_P [v vi Jgv].
move: (Vf_pr (fpj _ idt) Jgv); rewrite pri_V =>//; aw; trivial.
  by move=> <-.
by apply/setXb_P; saw => k ki; rewrite LgV//; apply: iVV.
Qed.

(** Exercise 5.2: Powerset of a product  *)
Lemma exercise5_2 a b:
  bijection (Lf(fun g => Lg a (fun x => direct_image g (singleton x)))
    (powerset (a \times b)) (gfunctions a (powerset b))).
Proof.
set tilde := Lf _ _.
apply: lf_bijective.
    move=> c /setP_P cp; apply:gfunctions_i1 => t ta; apply/setP_P => u.
    by move /dirim_P => [x _ pb]; move/setXp_P: (cp _ pb) => [].
  move => u v; set fx := Lg a _; set fy:= Lg a  _.
  move /setP_P => up /setP_P => vp fxy.
  set_extens x => xs.
    move /setX_P: (up _ xs) => [px Px Qx].
    have: inc (Q x) (Vg fy (P x)). 
      by rewrite -fxy /fx LgV //; apply/dirim_P; ex_tac; rewrite px.
    by rewrite /fy LgV //; move/dirim_P=> [w /set1_P ->]; rewrite px.
  move /setX_P: (vp _ xs) => [px Px Qx].
  have: inc (Q x) (Vg fx (P x)). 
      by rewrite fxy /fy LgV//; apply/dirim_P; ex_tac; rewrite px.
    by rewrite /fx LgV//; move/dirim_P=> [w /set1_P ->]; rewrite px.
move=> y ys; move: (gfunctions_hi ys)=> [f [fs sf tg gf]].
set (g:=Zo (a \times b) (fun z => inc (Q z) (Vg y (P z)))).
have gp: inc g (powerset (a \times b)) by apply/setP_P;apply: Zo_S.
rewrite -gf; ex_tac; apply: fgraph_exten; fprops.
  by aw; rewrite domain_fg. 
red; rewrite - (proj33 fs) sf => x xa; rewrite LgV //  gf;set_extens u. 
  move=> h; apply/dirim_P; exists x; first by fprops.
  apply: Zo_i; [ apply: (setXp_i xa) | by aw].
  rewrite - sf in xa; move: (Vf_target fs xa). 
  by rewrite tg /Vf gf; move/setP_P; apply.
by move /dirim_P => [v /set1_P ->] /Zo_P []; aw.
Qed.

(** Exercise 5.3:  TODO  *)

(** ** Section 6 *)

(** Exercise 6.1: Characterisation of equivalence  *)
Lemma exercise6_1 x g: sgraph g ->
  ((equivalence g /\ substrate g = x) <->
  [/\ domain g = x, range g = x,
    g \cg ((inverse_graph g) \cg g) = g &
    sub (diagonal x) g]).
Proof. 
move=> gg; split.
  move=> [eg sg]; split => //.
  -  by rewrite (domain_sr eg).
  - rewrite - sg /substrate; set_extens t => ts; first by fprops.
    case /setU2_P:ts => // /(domainP gg) [y Jh]; apply/(rangeP gg). 
    exists y; equiv_tac.
  - set_extens y. 
      move /compg_P => [py [z /compg_pP [u pa /igraph_pP pb pc]]].
      have J4: inc (J u z) g by equiv_tac.
      have J5: inc (J (P y) z) g by equiv_tac.
      have: inc (J (P y) (Q y)) g by equiv_tac.
      by rewrite py.
    move=> yg.
    have py: pairp y by  apply: gg.
    have  yv:J (P y) (Q y) = y by aw.
    rewrite - py; apply /compg_pP; exists (P y); last by ue.
    apply /compg_pP; exists (Q y);  [|  apply/igraph_pP]; ue.
  - move => t /diagonal_i_P [pt Pt PQt]. 
    by rewrite -pt -PQt;  rewrite - sg in Pt; equiv_tac. 
move=> [dg rg cg si].
have sg: (substrate g  = x) by rewrite /substrate dg rg; apply: setU2_id.
split=>//.
have p1: forall u, inc u x -> inc (J u u) g.
  by move=> u ux; apply: si; apply /diagonal_pi_P.
have p2: symmetricp g.
  move=> a b ab; red in ab.
  have Jag: (inc (J a a) g) by apply: p1; rewrite -dg; aw;  ex_tac.
  have Jbg: (inc (J b b) g) by apply: p1; rewrite -rg; aw;  ex_tac.
  rewrite -cg; apply /compg_pP; ex_tac; apply /compg_pP; ex_tac.
  by apply /igraph_pP.
have p3: transitivep g.
  move => a b c ab bc; rewrite -cg; apply /compg_pP.
  exists a => //; apply /compg_pP; exists b => //.
    by apply: p1; rewrite - sg; substr_tac.
  by apply/igraph_pP; apply p2.
by apply:symmetric_transitive_equivalence.
Qed.
  

(** Exercise 6.2: equivalence  from a graph *)

Lemma exercise6_2 g: sgraph g ->
  g \cg ( (inverse_graph g) \cg g) = g ->
  [/\ equivalence ((inverse_graph g) \cg g),
    substrate ((inverse_graph g) \cg g) = domain g,
    equivalence (g \cg (inverse_graph g)) &
    substrate (g \cg (inverse_graph g)) = range g].
Proof.
move=> gg cg.
have gig:sgraph (inverse_graph g) by apply: igraph_graph.
have gcigg:sgraph ((inverse_graph g) \cg g) by apply: compg_graph.
have gcgig: sgraph (g \cg (inverse_graph g))  by apply: compg_graph.
have t3:forall x y z t, related g x y -> related g z y -> related g z t ->
    related g x t. 
  move=> x y z t xy zy zt; rewrite -cg; apply/compg_pP.
  by exists z=>//;apply/compg_pP;exists y => //;apply /igraph_pP.
have s1: substrate ((inverse_graph g) \cg g) = domain g.
  set_extens x. 
    case /(substrate_P gcigg) => [] [y /compg_pP [z J1] /igraph_pP J2];
     ex_tac.
  move/(domainP gg) => [y Jg].
  have Jxx: (inc (J x x) ((inverse_graph g) \cg g)).
    by apply/compg_pP; ex_tac; apply /igraph_pP.
  apply: (arg1_sr Jxx).
have s2:substrate (g \cg (inverse_graph g)) = range g.
  set_extens x. 
    case/(substrate_P gcgig)=> [][y /compg_pP [z /igraph_pP J1 J2]];
    ex_tac.
  move/(rangeP gg) => [y Jg].
  have Jxx: (inc (J x x) (g \cg (inverse_graph g))).
    by apply/compg_pP; ex_tac; apply /igraph_pP.
  apply: (arg1_sr Jxx).
split => //; rewrite equivalence_pr; split; 
      try rewrite compg_inverse igraph_involutive //.
  by rewrite - compgA cg.
by rewrite compgA in cg; by rewrite compgA  cg. 
Qed.

(** Exercise 6.3: equivalence associated to [a \cap c] *)
Definition intersection_with x a := 
  Lf (intersection2 a) (powerset x)(powerset x).
Definition intersection_with_canon x a :=
  Lf (fun b => Zo (powerset x)(fun c=> b = a \cap c))
  (powerset a)(quotient (equivalence_associated (intersection_with x a))).

Lemma exercise6_3 a x:
  sub a x -> bijection (intersection_with_canon x a).
Proof. 
move=> ax. 
have ta: lf_axiom (intersection2 a) (powerset x) (powerset x). 
  move=> y /setP_P ay; apply /setP_i;apply: sub_trans ay ;apply: subsetI2r.
have fai: function (intersection_with x a) by apply: lf_function. 
move:(graph_ea_equivalence fai).
set r:= equivalence_associated (intersection_with x a); move => [er sr].
have rr: forall  u v, related r u v <-> 
    [/\ inc u (powerset x), inc v (powerset x)  &  a \cap u = a \cap v].
   move => u v; split.
      move/(ea_relatedP fai); rewrite lf_source; move => [pa pb].
      by rewrite !LfV.
   move => [pa pb pc]; apply/(ea_relatedP fai).
   by rewrite /intersection_with !LfV//; aw.
have aux: forall y, sub y a -> y =  a \cap y by move => y; move/setI2id_Pr.
apply: lf_bijective.
    move=> y /setP_P=> ya;set w:= Zo _ _ . 
    have new: nonempty w.
      exists y;apply: Zo_i; [apply/setP_P; apply: (sub_trans ya ax) | auto].
    have swp: sub w (powerset x) by apply: Zo_S. 
    have rp: inc (rep w) (powerset x) by  apply: swp;apply: rep_i. 
    apply /(setQ_P er); split => //. 
      by move: rp;rewrite sr /intersection_with; aw.
    have ira: (a \cap (rep w) = y).
      have: (inc (rep w) w) by apply: rep_i. 
      by move /Zo_hi => ->. 
    set_extens z.
      move=> zw; apply /(class_P er); apply /rr;split => //; first by apply:swp.
      by rewrite ira; move /Zo_P: zw => [].
    by move/(class_P er)/rr => [pa pb pc]; apply: Zo_i => //; rewrite -pc ira.
  move=> u v /setP_P ua /setP_P va;  set fs:= Zo _ _ => eql. 
  have iua: u = a \cap u by apply: aux.
  have: inc u fs by apply: Zo_i => //; apply/setP_P; apply:(sub_trans ua ax).
  by rewrite eql; move/ Zo_hi => ->.
move=> y /(setQ_P er) cy.
have ip: inc (a \cap (rep y)) (powerset a) by apply/setP_P; apply subsetI2l.
move: sr; rewrite lf_source => sr2.
ex_tac; symmetry;set_extens t.
  move /Zo_P => []; move /setP_P => pd pe.
  apply: (rel_in_class2 er cy); apply/rr;split => //; last by apply /setP_P.
  rewrite - sr2; exact (proj1 cy).
move => ty; apply /Zo_i; first by rewrite - sr2; apply: (sub_class_sr er cy ty).
by move: (rel_in_class er cy ty) => /rr  [_ _].
Qed.

(** Exercise 6.4: some properties of equivalence: composition, intersection *)
Lemma exercise6_4 g a b x:
  let comm F G b := F (G b) = G (F b) in
  equivalence g -> sgraph a -> sgraph b -> substrate g = x -> sub a g ->
  [/\ (domain a = x -> g \cg a = g),
   (range a = x -> a \cg g = g),
  (domain a = x -> comm (composeg^~a) (intersection2 g) b) &
  (range a = x ->  comm (composeg a) (intersection2 g) b)].
Proof. 
move=> comm eg ga gb sg ag.
have gg: sgraph g by fprops. 
split.
+ move=> ax; set_extens y.
    move /compg_P=> [py [z J1a J2g]].
    move: (ag _ J1a) => J1g.
    rewrite - py; equiv_tac.
  move=> yg; move: (gg _ yg)=> py; apply/compg_P.
  split =>//.
  have : (inc (P y) (domain a)) by rewrite ax - sg; substr_tac. 
  move/(domainP ga)=> [z Ja]; exists z =>//.
  move: (ag _ Ja)=> Jg.
  have J2g:inc (J z (P y)) g by  equiv_tac.
  rewrite - py in yg; equiv_tac.
+ move=> ax; rewrite /comp; set_extens y.
    move /compg_P => [py [z J1g J2a]].
    move: (ag _ J2a) => J2g.
    rewrite - py; equiv_tac.
  move=> yg; move: (gg _ yg)=> py; apply/compg_P =>//.
  have : (inc (Q y) (range a)) by rewrite ax - sg; substr_tac. 
  move/(rangeP ga); move=> [z Ja]; split => //;exists z =>//.
  move: (ag _ Ja)=> Jg.
  have J2g:inc (J (Q y) z) g by  equiv_tac.
  rewrite - py in yg; equiv_tac.
+ move=> ax;  set_extens y.
    move /compg_P => [py [z J1a/setI2_P [J2g J3b]]]; apply/setI2_i.
    move: (ag _ J1a) => J1g; rewrite - py; equiv_tac.
    apply/compg_P;split=>//;exists z=>//.
  move=> /setI2_P [yg] /compg_P [py [z J1a J2b]].
  apply/compg_P; split => //; exists z => //; apply:setI2_i => //.
  move: (ag _ J1a)=> Jg.
  have J2g:inc (J z (P y)) g by  equiv_tac.
  rewrite -  py in yg; equiv_tac.
+ move=> ax; set_extens y.
    move /compg_P => [py [z /setI2_P [J2g J3b] J1a]]; apply/setI2_i.
    move: (ag _ J1a) => J1g; rewrite - py; equiv_tac.
    apply/compg_P;split=>//;exists z =>//.
  move=> /setI2_P [yg] /compg_P [py [z J1a J2b]].
  apply/compg_P; split => //; exists z => //; apply:setI2_i => //.
  move: (ag _ J2b)=> Jg.
  have J2g:inc (J (Q y) z) g by  equiv_tac.
  rewrite - py in yg; equiv_tac.
Qed.

(** Exercise 6.5: intersection of equivalence is equivalence. We show here that union is not *)

Lemma symmetric_union a b: symmetricp a -> symmetricp b ->
  symmetricp (a \cup b).
Proof. 
by move=>  sa sb x y;  case /setU2_P=> h; apply/setU2_P;
   [left; apply: sa | right; apply: sb ].
Qed.

Lemma substrate_union_diag x g:
  sub g (coarse x) -> substrate (g \cup (diagonal x)) = x.
Proof. 
move=> gc.
have gg: sgraph g by move=> t tg; move: (gc _ tg) => /setX_P [].
have gu: sgraph (g \cup (diagonal x)).
  by move=> t; case /setU2_P; [ auto | move/diagonal_i_P => []].
set_extens y.  
  case /(substrate_P gu) => [] [z] /setU2_P []. 
  - by move => h;  move: (gc _ h); move /setXp_P=> [].
  - by move/diagonal_pi_P => [].
  - by move => h;  move: (gc _ h); move /setXp_P=> [].
  - by move/diagonal_pi_P => [ h <-].
move=> yx.
have aux: inc (J y y) (g \cup (diagonal x)).
  by apply: setU2_2; apply /diagonal_pi_P; split.
substr_tac.
Qed.

Definition special_equivalence a b x :=
  (doubleton (J a b) (J b a)) \cup  (diagonal x).
Lemma substrate_special_equivalence a b x:
  inc a x -> inc b x ->  substrate(special_equivalence a b x) = x.
Proof. 
move=> ax bx; rewrite/ special_equivalence. 
apply: substrate_union_diag. 
by move=> t /set2_P => [][] ->; apply/setXp_i.
Qed.

Lemma special_equivalence_ea a b x:
  inc a x -> inc b x -> equivalence(special_equivalence a b x).
Proof. 
move=> ax bx.
have gs: sgraph (special_equivalence a b x). 
  move=> t; move/setU2_P; case; first by case/set2_P => ->; fprops.
  by move  /diagonal_i_P => [].
have pair_symm: forall a b c d, J a b = J c d -> J b a = J d c.
  move=> u v u' v' eql.
  apply: pair_exten; fprops; aw.
    apply: (pr2_def eql).  
  apply: (pr1_def eql).
apply: symmetric_transitive_equivalence => //.
  move=> u v h; case/setU2_P: (h).
    case /set2_P => ww; apply/setU2_P; left;
       rewrite (pr1_def ww)(pr2_def ww); fprops.
  by move => /diagonal_pi_P [_ uv]; move: h;rewrite uv.
move=> u v w ra rb.
case /setU2_P: (ra); last by move => /diagonal_pi_P [_ ->].
case /setU2_P: (rb); last by move => /diagonal_pi_P [_ <-].
move => h1 h2; apply/setU2_P.
case /set2_P: h1 => h11; rewrite (pr2_def h11); 
  case /set2_P: h2 => h22; rewrite (pr1_def h22).
- left; fprops.
- by right; apply /diagonal_pi_P.
- by right; apply /diagonal_pi_P.
- left; fprops.
Qed.


Lemma exercise6_5 
  (x := C3)
  (g1:= special_equivalence C0 C1 x)
  (g2:= special_equivalence C0 C2 x):
      [/\ equivalence g1, equivalence g2, substrate g1 = x,
        substrate g2 = x &  ~ (equivalence (g1 \cup g2))].
Proof. 
split.
        apply: special_equivalence_ea; apply /C3_P; in_TP4.
      apply: special_equivalence_ea; apply /C3_P; in_TP4.
    rewrite substrate_special_equivalence //; apply /C3_P; in_TP4.
  rewrite substrate_special_equivalence //; apply /C3_P; in_TP4.
move=> bad.
have p1: (related (g1 \cup g2) C1 C0). 
 apply /setU2_P; left;apply/setU2_P; left; fprops.
have p2: (related (g1 \cup  g2) C0 C2). 
  apply /setU2_P; right;apply/setU2_P; left; fprops.
have :(related (g1 \cup g2) C1 C2) by equiv_tac.
move: C2_ne_C01 => [n1 n2].
case /setU2_P; case/setU2_P.
by case/set2_P=> eq2; move: (pr2_def eq2); auto.
by move /diagonal_pi_P =>  [_]; auto.
by case/set2_P=> eq2; move: (pr1_def eq2); fprops.
by move /diagonal_pi_P =>  [_]; auto.
Qed.

(** Exercise 6.6: Commposition of two equivalences; if it is an equivalence, it is the supremum  *)
Lemma exercise6_6a G H:
  equivalence G -> equivalence H ->
  (equivalence (G \cg H) <-> (G \cg H = H \cg G)).
Proof. 
move=> eG eH.
set (K:= G \cg H).
split. 
  move => eK.  
    have aux a b: inc (J a b) K -> inc (J b a) K by move => h;equiv_tac.
    set_extens x => xK.
    have px: (pairp x) by apply: (@compg_graph G H).
    move: xK ; rewrite - px => /aux.
    move /compg_pP=> [y JH JG]; apply/compg_pP; exists y => //; equiv_tac.
  move: xK =>/compg_P [px [y JG JH]].
  rewrite - px; apply: aux; apply/compg_pP;exists y => //; equiv_tac.
move=> eq.
  move: eG eH; rewrite ! equivalence_pr. 
move=> [GG iG] [HH iH]; split.
  by rewrite {2} /K compgA eq - (compgA H G G) GG - compgA  -/K eq compgA HH.  
by rewrite {2}/K compg_inverse -iH -iG. 
Qed.

Lemma exercise6_6b G H:
  equivalence G -> equivalence H ->  substrate G = substrate H -> 
  substrate (G \cg H) = substrate G.
Proof. 
move=> eG eH sG.
set_extens x. 
  have xx:sgraph (G \cg H) by fprops.
  case /setU2_P; [move /(domainP xx) | move /(rangeP xx)];
    move => [z] /compg_pP [t ta tb]; [rewrite  sG | ] ;  substr_tac.
move=> xsG.
have p3: related  (G \cg H) x x. 
 apply/compg_pP; exists x;equiv_tac => //; ue.
substr_tac.
Qed.

Lemma exercise6_6c G H:
  equivalence G -> equivalence H -> substrate G = substrate H ->
  [/\ sub G (G \cg H), sub H (G \cg H)
    & forall W, equivalence W -> sub G W -> sub H W ->
      sub (G \cg H) W].
Proof. 
move=> eG eH sG.
have gg: sgraph G by fprops.
have gh: sgraph H by fprops.
have gc: sgraph  (G \cg H) by apply: compg_graph.
split.
- move=> y yG.
  move:  (gg _ yG) => py.
  rewrite - py in yG.
  apply/ compg_P;split=>//;exists (P y) => //; equiv_tac=>//.
  rewrite - sG;  substr_tac.
- move=> y yH.
  move:  (gh _ yH) => py.
  rewrite - py in yH.
  apply/compg_P; split=>//;exists (Q y)=>//; equiv_tac=>//.
 rewrite sG;  substr_tac.
- move=> w ew gW hW t.
  move /compg_P=> [tp [y JH JG]].
  move: (gW _ JG) (hW _ JH)=> J1G J2G. 
  have: inc (J (P t) (Q t)) w by equiv_tac.
  by rewrite tp.
Qed.
    
Lemma range_is_substrate g:
  equivalence g -> range g = substrate g.
Proof.
move=> eg; rewrite /substrate; set_extens x. 
  move => pa; fprops.
move:(eg) => [fgg  _ _ _].
case /setU2_P => //; move /(domainP (proj41 eg))=> [y Jg]. 
apply/(rangeP fgg); exists y; equiv_tac.
Qed.

Lemma sub_coarse g:
  equivalence g ->  sub g (coarse (substrate g)).
Proof. 
move=> eg; move: (sub_graph_setX (proj41 eg)).
by rewrite range_is_substrate // domain_sr.
Qed.

Lemma exercise6_6d G H:
  equivalence G -> equivalence H -> substrate G = substrate H ->
  G \cg H = H \cg G ->
  (G \cg H) = intersection(Zo (powerset (coarse (substrate G)))
    (fun W => [/\ equivalence W, sub G W & sub H W])).
Proof. 
move=> eG eH sG cGH.
set (E:= substrate G). 
have sGE: sub G (coarse E) by apply: sub_coarse. 
have sHE: sub H (coarse E) by rewrite /E sG; apply: sub_coarse. 
move: (exercise6_6c eG eH sG)=> [sGc sHc lew].
set_extens t => ts.
  apply: setI_i. 
    exists (coarse E); apply: Zo_i; first by apply: setP_Ti.
    split=> //;apply: proj1 (coarse_equivalence E).
  by move=> y /Zo_P [_ [ey gy hy]]; apply: (lew _ ey gy hy).
move: cGH;rewrite - exercise6_6a // => cGH.
apply: (setI_hi  (y:=(G \cg H)) ts); apply: Zo_i; last by done.
apply /setP_P;rewrite /E - (exercise6_6b eG eH sG); apply: sub_coarse=>//.
Qed.

(** Exercise 6.7: Is this property true ? *)

Remark exercise6_7 G0 G1 H0 H1 E x:
  equivalence G0 -> substrate G0 = E ->
  equivalence H0 -> substrate H0 = E ->
  equivalence G1 -> substrate G1 = E ->
  equivalence H1 -> substrate H1 = E ->
  G1 \cap H0 = G0 \cap H1 ->
  G1 \cg H0 = G0 \cg H1 ->
  inc x E -> (
    let G1x := direct_image G1 (singleton x) in 
      let H1x := direct_image H1 (singleton x) in
        let R0 := induced_relation G0 G1x in
          let S0 := induced_relation H0 H1x in
            equipotent (quotient R0) (quotient S0)).
Proof.
Abort.

(** Exercise 6.8: Inverse image of an equivalence *)
Lemma exercise6_8 f r:
  equivalence r -> function f -> target f = substrate r ->
  (exists g, bijection_prop g (quotient (inv_image_relation f r))
        (quotient (induced_relation r (Imf f)))).
Proof.
move => er ff tf. 
set (s := inv_image_relation f r). 
set (A:= Imf f). 
set (Ra := induced_relation r A).
have ia: (iirel_axioms f r) by [].
have [es _]:= (iirel_relation ia).
have iA: induced_rel_axioms r A.  
   by split =>//; rewrite -tf; apply: Imf_Starget.
have [eR _]:=(induced_rel_equivalence iA).
set (f1:= fun x y =>  [/\ classp r y,
    nonempty (y \cap A) & x = Vfi f y]).
have qsp:forall x, inc x (quotient s) -> exists y, f1 x y. 
  by move=> x /(setQ_P es); move /(iirel_classP ia). 
set (f2:= fun x => choose (fun y => f1 x y)).
have f2p: (forall  x, inc x (quotient s) -> f1 x (f2 x)). 
  move=> x xq; rewrite /f2;apply: choose_pr; apply: (qsp _ xq). 
set (f3:= fun x => (f2 x) \cap A).
have f3p: (forall x,  inc x (quotient s) -> inc (f3 x) (quotient Ra)).
  move=> x xs; rewrite /Ra; move: (f2p _ xs) => [pa pb pc].
  apply/(setQ_P eR); apply/(induced_rel_classP iA).
  by exists (f2 x).  
set (g:= Lf f3 (quotient s) (quotient Ra)).
have sgf: sgraph (graph f) by fprops.
exists g; rewrite /g;saw; apply: lf_bijective => //.
  move => u v uq vq; rewrite /f3 => ii.
  move: (f2p _ uq)(f2p _ vq); rewrite /f1; move=> [cfu niu uv][cfv niv vv].
  move: niv=> [y] /setI2_P [y2v yiA].
  have y2u: inc y (f2 u).
     apply: (@setI2_1 (f2 u) A);rewrite ii; fprops.
     move: yiA;rewrite [A](ImfE ff); move /(rangeP sgf)=> [x Jg].
  have xb: (inc x v) by rewrite vv; apply/iim_graph_P;ex_tac.
  have xu:(inc x u) by rewrite uv; apply/iim_graph_P; ex_tac.
  move : uq vq; move/(setQ_P es) => c1 /(setQ_P es) => c2.
  by case: (class_dichot es c1 c2) => // dj; empty_tac1 x.
move=> y; move /(setQ_P eR) /(induced_rel_classP iA)=> [x [cx nex yi]].
set (u:= Vfi f x).
have uq: inc u (quotient s) by apply/ (setQ_P es) /(iirel_classP ia); exists x. 
ex_tac.
rewrite /f3 yi. 
move:(f2p _ uq); rewrite /f1; move=> [cf2 ni ui].
move: nex=> [t] /setI2_P [tx].
rewrite {1} [A](ImfE ff) ; move/ (rangeP sgf)=> [z Jg].
have: inc z u by apply/iim_graph_P; ex_tac.
rewrite  {1} ui; move/iim_graph_P => [t' t'2u Jg'].
have tt': t = t' by move: (Vf_pr ff Jg) (Vf_pr ff Jg') => <-.
suff: f2 u = x by move->.
case:(class_dichot er cf2 cx)=> // di.
by empty_tac1 t ;rewrite tt'.
Qed.

(** Exercise 6.9: decomposition of some function *)
Lemma exercise6_9 F G p f r:
  equivalence r ->  F = substrate r -> p = canon_proj r ->
  surjection f -> source f = G -> target f = quotient r ->
  exists E g h,
  [/\ surjection_prop g E F, surjection_prop h E G & p \co g = f \co h].
Proof.
move=> er sr xr sjf sf tf.
have ff: function f by fct_tac.
have ba:= C1_ne_C0.
set Ea:= F \times (singleton C0).
set Eb:= G \times (singleton C1).
set E:= Ea \cup Eb.
have gE: sgraph E by move => T /setU2_P; case; move /setX_P => [ok _].
have xep: forall x, inc x E -> (Q x = C0 \/ Q x = C1).
  move=> x /setU2_P; case; move /setX_P => [_ _ ] /set1_P ->; fprops.
have xgp:forall x, inc x G -> inc (Vf f x) (quotient r).
  move=> x xg; rewrite - tf;apply: Vf_target => //; ue.
have xgp1:forall x, inc x G -> inc (rep (Vf f x)) F. 
 move=> x xG; rewrite sr;fprops.
set (gz :=fun z=> Yo (Q z = C0) (P z) (rep (Vf f (P z)))).
have gzP:forall z, inc z Ea -> gz z = P z.
  move=> z /setX_P [_ _] /set1_P h; rewrite /gz Y_true //. 
have gzp': forall z, inc z Ea -> inc (gz z) F.
  by move=> z zEa; rewrite gzP//; move /setX_P : zEa => [_ ok _].
have gzQ:forall z, inc z Eb -> gz z = rep (Vf f (P z)).
  move=> z/setX_P [_ _] /set1_P => h; rewrite /gz Y_false //;  ue.
have gzq':forall z, inc z Eb -> inc (gz z) F.
  by move=> z zE; rewrite gzQ //; apply: xgp1;  move /setX_P : zE => [_ ok _].
have tag:lf_axiom gz E F. 
  move=> t; case /setU2_P; [apply: gzp'| apply: gzq']. 
set (g:= Lf gz E F). 
have sj: surjection g.
  rewrite /g;apply: lf_surjective =>//;  move=> y yF.
  have p1: inc (J y C0) Ea by rewrite /Ea; fprops. 
  have p2: inc (J y C0) E by rewrite /E; aw;fprops.
  by ex_tac;  rewrite gzP; aw. 
have gp: forall x, inc x Eb -> Vf  (canon_proj r) (gz x) = Vf f (P x).
  move=> x xEb. 
  have gzs:  inc (gz x) (substrate r) by rewrite - sr; apply: gzq'.
  have xE: inc x E by move: xEb; rewrite /E;aw => ee; fprops.
  rewrite canon_proj_V // gzQ //; apply: class_rep=>//; apply: xgp.
  by move /setX_P : xEb => [_ ok _].
set (ha:= fun x => rep (Vfi1 f (Vf (canon_proj r) x))).
have haF:forall x, inc x F ->
    ha x = rep (Vfi1 f (class r x)).
  move=> x xF; rewrite /ha canon_proj_V //; ue.
have haF':forall x, inc x F -> 
    sub (Vfi1 f (class r x)) G.
  move=> x xF t /iim_graph_P [u _ jg]; rewrite - sf; Wtac.
have haF'': forall x, inc x F -> 
    inc (ha x) (Vfi1 f (class r x)).
  move => x xF; rewrite haF //; apply: rep_i.
  have ct: inc (class r x) (target f) by rewrite tf; rewrite sr in xF; fprops.
  move:((proj2 sjf) _  ct)=> [u us]; move => ->.
  exists u; apply /iim_graph_P; ex_tac; apply: Vf_pr3=>//.
have haG: forall x, inc x F -> inc (ha x) G. 
  by move=> x xF; apply: (haF' _ xF); apply: haF''.
set(hz:= fun z=> Yo (Q z = C0) (ha (P z)) (P z)).
have hzG: forall z, inc z E -> inc (hz z) G. 
  rewrite /hz;move=> z /setU2_P [] /setX_P [_ pa] /set1_P ->; Ytac0 => //.
  by apply: haG.
set(h:=Lf hz E G).
have sh: surjection h.
  rewrite /h;apply: lf_surjective=>// y yG.
  have JEb:inc (J y C1) Eb by rewrite /Eb;aw; fprops.
  have JE: (inc (J y C1) E) by rewrite /E; aw; fprops.
  by ex_tac; rewrite /hz; aw; rewrite Y_false. 
have WWh: forall x, inc x Ea -> Vf f (hz x) = Vf (canon_proj r) (P x).
  move=> x xEa.
  have xE: inc x E by rewrite /E; aw; intuition.
  have Ps: inc (P x) (substrate r) by rewrite - sr -gzP//; apply: gzp'.
  rewrite /hz canon_proj_V//.
  move /setX_P: xEa=> [px PF] /set1_P ->; Ytac0.
  move /iim_graph_P: (haF'' _ PF) => [u ] /set1_P <- Jg; Wtac.
exists E; exists g; exists h; rewrite /surjection_prop/g/h;aw;split => //. 
have cpg: p \coP g. 
  split; first by rewrite xr;apply: canon_proj_f. 
    by fct_tac. 
  rewrite xr /g; aw; ue. 
have cfh: composable f h by split => //; try fct_tac; rewrite /h; aw.
have sg: source g = source h by  rewrite /g/h; aw.
have tp: target p = target f by  rewrite xr; aw.
move: sj => [fg _].
apply: function_exten; try fct_tac; aw; trivial.
move=> x xE /=; rewrite ! compfV //  ? lf_source // !LfV // .
move /setU2_P: (xE) => [] xE'.
  have Ps: inc (P x) (substrate r) by rewrite - sr -gzP //; apply: gzp'.
  by rewrite WWh // /g; aw; trivial; rewrite gzP // xr; aw.
rewrite xr gp /h /hz; aw =>//; rewrite Y_false //.
by move /setX_P: xE'=> [_ _ ] /set1_P ->.
Qed.


(** Exercise 6.10: least equivalence associated to a relation; connected components *)

Lemma set1_pr2 a X: inc a X -> small_set X -> X = singleton a.
Proof.
by move => tX sX; apply (set1_pr tX) => u zX; exact: (sX _ _ zX tX).
Qed.

Section Exercise6_10.
Lemma Exercise6_10_a (r: relation):
  symmetric_r (fun  x y => r x y /\ r y x).
Proof. by move=>  x y; case. Qed.

Lemma exercise6_10_b r E:
  reflexive_re r E -> reflexive_re (fun  x y => r x y /\ r y x) E.
Proof.  move => rr y; split; [by move/rr | by case; move /rr]. Qed.

Variables (R:relation) (E:Set).
Hypotheses (A1: reflexive_re R E)(A2: symmetric_r R)
  (A3: forall x y, R x y -> inc x E).

(** Let [setF] be the set of all [A] such that that no element of [A] is related to an element of the complementary; let [connected_comp x] be the intersection of all [A] that contains [x] this is the class of [x] for [relS] *)

Definition setF:= Zo (powerset E)(fun A => forall y z, inc y A ->
  inc z (E -s A) -> not (R y z)).
Definition connected_comp x := intersection(Zo setF (fun A => inc x A)). 

Lemma setF_pr A a b:
  inc A setF -> inc a A -> R a b -> inc b A.
Proof. 
move /Zo_P => [] /setP_P AE Ap aA Rab.
case: (inc_or_not b A)=> // nba.
have bc: inc b (E -s A) by apply:setC_i =>//; apply: (A3 (A2 Rab)).
by case: (Ap _ _  aA bc).
Qed. 

Lemma setF_pr2 A a b:
  inc A setF -> inc a A -> chain_related R a b -> inc b A.
Proof. 
move=> As aA [c [cc hcx <-]].
rewrite - hcx in aA; clear hcx.
elim: c cc aA.
   move=> u v /= Ruv uA; apply: (setF_pr As uA Ruv).
move=> u c h /= [uh cc] uA.
apply: h=>//;apply: (setF_pr As uA uh).
Qed.

Lemma setF_pr3 A a: inc A setF -> inc a A ->
                    sub (class (chain_equivalence R E) a) A.
Proof.
move:(chain_equivalence_eq A1 A2 A3)=> [es sr].
move=> As aA t /(class_P es) /graph_on_P1 [_ _ ].
apply: (setF_pr2 As aA). 
Qed.

Lemma setF_pr0 a b: R a b -> related (chain_equivalence R E) a b.
Proof.                                 
move => rab.
move:(A3 rab) (A3 (A2 rab)) => aE bE.
by apply/graph_on_P1; split => //;exists (chain_pair a b).
Qed.
  
Lemma setF_pr4 a: inc a E -> inc (class (chain_equivalence R E) a) setF.
Proof. 
move=> aE; rewrite /setF.
move:(chain_equivalence_eq A1 A2 A3)=> [es sr].
apply: Zo_i.
  apply/setP_P; rewrite - {2} sr; apply: (sub_class_substrate es).
move=> y z ya /setC_P [zE nzc]; dneg yz; apply/(class_P es).
move/(class_P es):ya => way; exact: (proj43 es y _ _ way (setF_pr0 yz)).
Qed.

Lemma connected_comp_class x: inc x E ->
  class (chain_equivalence R E) x = connected_comp x.
Proof.
move=> xE;set_extens t; rewrite /connected_comp. 
  move=> tc;apply: setI_i. 
    exists E; apply: Zo_i =>//; rewrite /setF; apply: Zo_i.
      aw; apply /setP_Ti.
    by move=> y z yE /setC_P [].
  move=> y /Zo_P [yS xy];apply: ((setF_pr3 yS xy) _ tc).
move:(chain_equivalence_eq A1 A2 A3)=> [eq sr].
have cx:inc (class (chain_equivalence R E) x)  (Zo setF (fun A => inc x A)). 
  apply: Zo_i; first by apply: setF_pr4. 
  apply/(class_P eq); rewrite - sr in xE; equiv_tac.
move=> h;apply: (setI_hi h cx).
Qed.

(** Exercise 6.11: Intransitive relations of order [n]. Given [n+4] distinct 
elements [x(i)], if for all pairs but one, [x(i)] is related to [x(j)], then 
the last pair is related too. We consider only the case [n=1]. The relation [R]
is assumed reflexive and symmetric. We give here an alternate definition, assuming only one inequality *)

Definition intransitive1 := forall x y z t,
  x <> y ->  R x y -> R x z -> R x t -> R y z -> R y t -> R z t.

Lemma intransitive1pr : 
  let intransitive_alt:= forall x y z t,
    x <> y -> x <> z -> x <> t -> y <> z -> y <> t -> z <> t ->
    inc x E -> inc y E -> inc z E -> inc t E -> 
    R x y -> R x z -> R x t -> R y z -> R y t -> R z t in
    intransitive1 <-> intransitive_alt.
Proof. 
rewrite /intransitive1; split.
move=> h x y z t  H0 _ _ _ _ _ _ _ _ _ H10 H11 H12 H13 H14.
apply: (h x y z t H0 H10 H11 H12 H13 H14).
move=> h x y z t nxy xy xz xt yz yt.
move: (A3 xy) (A3 yz)(A3 (A2 xz))(A3 (A2 yt)) => xE yE sE tE.
case: (equal_or_not x z) => nxz; first by  ue.
case: (equal_or_not x t) => nxt; first by apply: A2; ue.
case: (equal_or_not y z) => nyz; first by ue.
case: (equal_or_not y t) => nyt; first by apply: A2; ue.
case: (equal_or_not z t)=> nzt; first  by rewrite nzt  -A1. 
apply: (h x y z t) =>//. 
Qed.

(** Let [Cab a b] be the set of elements related to both [a] and [b], 
assuming [a] and [b] related. 
It is stable by [R]; [a] and [b] can be replaced by any element of [Cab]  *)

Definition stableR A:= forall a b, inc a A -> inc b A -> R a b.
Definition Cab a b:= Zo E (fun x => R a x /\ R b x).

Lemma Cab_stable a b: a<> b -> R a b -> intransitive1 ->
  stableR (Cab a b).
Proof.
move=> nab Rab i1; rewrite /Cab=> u v. 
move /Zo_P=> [_ [r1 r2]] /Zo_P [_ [r3 r4]]; apply: (i1 a b u v) =>//.
Qed.

Lemma Cab_trans a b x y: a<> b -> R a b -> intransitive1 ->
  x<> y -> inc x (Cab a b) -> inc y (Cab a b) -> (Cab a b)= (Cab x y).
Proof.
move=> nab rab i1 nxy /Zo_P [xE [r1 r2]] /Zo_P [yE [r3 r4]]. 
set_extens t; move /Zo_P=> [tE [r5 r6]]; apply/Zo_i => //; split.
- apply: (i1 a b x t) =>//. 
- apply: (i1 a b y t) =>//; apply: A2. 
- apply: (i1 x y a t) =>//; first apply: (i1 a b x y)=>//; apply: A2=> //. 
- apply: (i1 x y b t) =>//; first apply: (i1 a b x y)=>//; apply: A2=> //. 
Qed.

(** A set [X] is said to be a constituant if it is [Cab] or a connected 
component (a class for [relS]) that is a singleton *)

Definition is_constituant A :=
  (exists a, [/\ A = singleton a, inc a E & forall b, R a b -> a = b]) \/
  (exists a b, [/\ A = Cab a b, a<> b & R a b]).

Lemma singleton_component A: sub A E ->
  ( (inc A (quotient (chain_equivalence R E) ) /\ singletonp A) <->
    (exists2 a, A = singleton a & forall b, R a b -> a = b)).
Proof. 
move=> AE.
move:(chain_equivalence_eq A1 A2 A3)=> [eq sr].
split. 
  move=> [Asq [x Asx]]; exists x => //.
  move=> b /setF_pr0.
  move /(in_class_relatedP eq) => [y [cy xy]]. 
  have <- : A = y.
    move: Asq => /(setQ_P eq) => cA; case:  (class_dichot eq cy cA)=> //. 
    move=> dy; red in dy; empty_tac1 x; apply:setI2_i => //.
    rewrite Asx; fprops. 
  by rewrite Asx; move /set1_P.
move=> [x As Ap]; rewrite As; split; last by exists x.
have xse: inc x (substrate (chain_equivalence R E)).
  rewrite sr; apply: AE; rewrite As; fprops.
have Aq: forall b, R b x -> b = x. 
  by move => b ba; rewrite (Ap b) //; apply: A2.
suff: (class (chain_equivalence R E) x = singleton x).
  move => <-; apply /(setQ_P eq); apply: (class_class eq xse).
apply: set1_pr; first by  apply /(class_P eq); equiv_tac.
move => w; move /(class_P eq) => /(proj44 eq).
move/graph_on_P1 => [ pa qa [c [cc <-]]].
elim: c cc.
  by move=> u v /= uv vx; rewrite vx in uv; apply: Aq.
by move=> p c h1 /= [Rp cc] tc; apply: Aq; rewrite - (h1 cc tc). 
Qed.

(** The intersection of two distinct constituants is empty or a singleton *)


Lemma constituant_inter2 A B:
  is_constituant A -> is_constituant B -> intransitive1 ->
  A = B \/ small_set (A \cap B).
Proof. 
move=> cA cB i1.
case: (equal_or_not A B); first (by left); move => AB;right; move=> u v.
case: cA.
  move=>[a [Aa aE ap]]; rewrite Aa. 
  by move/setI2_P => [/set1_P -> _] /setI2_P [/set1_P -> _].
case: cB.
   move=>[c [Ac cE cp]] _; rewrite Ac. 
   by move/setI2_P => [_ /set1_P ->] /setI2_P [_ /set1_P ->].
move=> [a [b [Aab nab Rab]]] [a' [b' [Aab' nab' Rab']]].  
case: (equal_or_not u v)=>// nuv.
rewrite Aab Aab';move => /setI2_P [uA uB] /setI2_P [vA vB].
case: AB; rewrite Aab' Aab.
rewrite (Cab_trans nab Rab  i1 nuv uB vB).
by rewrite (Cab_trans nab' Rab'  i1 nuv uA vA).
Qed.

(** Intersection of three constituants *)

Lemma constitutant_inter3 A B C:
  is_constituant A -> is_constituant B -> is_constituant C ->  intransitive1 ->
  A = B \/ A = C \/ B = C \/  A \cap B = emptyset
  \/ A \cap C = emptyset \/ B \cap C = emptyset
  \/ (A \cap B = A \cap C  /\ B \cap C =  A \cap C).
Proof. 
move=> cA cB cC i1.
case: (equal_or_not A B); [by left| move=> nAB; right].
case: (equal_or_not A C); [by left| move=> nAC; right].
case: (equal_or_not B C); [by left| move=> nBC; right].
have ssAB: small_set (A \cap B).
  by case: (constituant_inter2 cA cB i1).
have ssAC: small_set (A \cap C).
  by case: (constituant_inter2 cA cC i1).
have ssBC: small_set (B \cap C).
  by case: (constituant_inter2 cB cC i1).
case: cA.
  move=> [a [Aa aE ap]]; case cB.
    move=> [b [Bb bE bp]].
    left; apply: disjoint_pr=> u ua ub; case: nAB. 
    by move: ua ub;rewrite Aa Bb; move /set1_P => -> /set1_P ->.
  move => [b1 [b2 [Bbb nbb Rbb]]]. 
  left; apply: disjoint_pr => u; rewrite Aa Bbb; move /set1_P => ->.
  move/Zo_hi=> [R1 R2]; case: nbb.
  by rewrite -(ap _ (A2  R1)) (ap _ (A2 R2)).
move => [a1 [a2 [Aaa naa Raa]]].
case: cB.
  move=> [b [Bb bE bp]]; case: cC.
    move=> [c [Cc cE cp]].
    right;right;left; apply: disjoint_pr=> u; rewrite Bb Cc; move /set1_P=> ->. 
    by move/set1_P=> bc; case nBC;rewrite Bb Cc bc.
  move => [c1 [c2 [Ccc ncc Rcc]]]. 
  right; right;left; apply: disjoint_pr => u; rewrite Bb Ccc; move/set1_P=> ->.
  by move /Zo_hi=>  [R1 R2]; case ncc; rewrite -(bp _ (A2 R1)) (bp _ (A2 R2)).
move => [b1 [b2 [Bbb nbb Rbb]]].
case: cC.
  move=> [c [Cc cE cp]].
  right;left;apply: disjoint_pr => u uA uC; move: uC uA; rewrite Aaa Cc.
  move /set1_P=> -> /Zo_hi [R1 R2]; case: naa.
  by rewrite -(cp _ (A2  R1)) (cp _ (A2 R2)).
move => [c1 [c2 [Ccc ncc Rcc]]].
case: (emptyset_dichot (A \cap B));[ by left |  move=> [c ci]; right].
case: (emptyset_dichot (A \cap C));[ by left |  move=> [b bi]; right].
case: (emptyset_dichot (B \cap C));[ by left |  move=> [a ai]; right].
have iAB: A \cap B = singleton c by apply: set1_pr2. 
have iAC: A \cap C = singleton b by apply: set1_pr2.
have iBC: B \cap C = singleton a by apply: set1_pr2.
rewrite iAB iAC iBC.
suff: (inc c C). 
   move=> cC.
   have cAC: inc c (A \cap C) by move/setI2_P: ci => []; fprops.
   have cBC: inc c (B \cap C) by move/setI2_P: ci => []; fprops.
   by rewrite (ssAC _ _ bi cAC) (ssBC _ _ ai cBC).
case: (equal_or_not a b).
  move=> ab.
  have: inc a (A \cap B). 
    apply setI2_i; [by rewrite ab;apply: (setI2_1 bi) | apply: (setI2_1 ai)].
  rewrite iAB; move /set1_P => <-; apply: (setI2_2 ai).
move=> nab.
move: ai bi ci => /setI2_P [aB aC] /setI2_P [bA bC] /setI2_P [cA cB].
move: cA cB bA bC aB aC; rewrite Aaa Bbb Ccc. 
move => /Zo_P [cE [Ra1c Ra2c]] /Zo_hi [Rb1c Rb2c].
move => /Zo_hi [Ra1b Ra2b] /Zo_hi [Rc1b Rc2b].
move => /Zo_hi [Rb1a Rb2a] /Zo_hi [Rc1a Rc2a].
move: (i1 _ _ _ _ ncc Rcc Rc1a Rc1b Rc2a Rc2b) => Rab.
move: (i1 _ _ _ _ nbb Rbb Rb1a Rb1c Rb2a Rb2c) => Rac.
move: (i1 _ _ _ _ naa Raa Ra1b Ra1c Ra2b Ra2c) => Rbc.
move: (i1 _ _ _ _ nab Rab (A2 Rc1a) Rac (A2 Rc1b) Rbc) => Rc1c.
move: (i1 _ _ _ _ nab Rab (A2 Rc2a) Rac (A2 Rc2b) Rbc) => Rc2c.
by apply: Zo_i.
Qed.

End Exercise6_10.

(** Let [X] be a covering,  satisfying the intersection properties above; Then the associated relation is intransitive and the elements of [X] are the constituants  *)
Definition exercise6_11b_assumption X E:=
  [/\ union X = E,
   (forall A, inc A X -> nonempty A),
   (forall A B, inc A X -> inc B X -> A = B \/ small_set (A \cap B)) &
  (forall A B C, inc A X -> inc B X -> inc C X -> 
    ( A=B \/ A = C \/ B = C \/  A \cap B = emptyset 
      \/ A \cap C = emptyset 
      \/ B \cap C = emptyset 
      \/ (A \cap B = A \cap C /\  A \cap B = B \cap C)))].
Definition exercise6_11b_rel X x y := exists A, [/\ inc A X, inc x A & inc y A].

Lemma exercise6_11b1 E X:
  exercise6_11b_assumption X E -> reflexive_re (exercise6_11b_rel X) E.
Proof.
move=> [h _] x; rewrite /exercise6_11b_rel -h;split.
  move => xE; move: (setU_hi xE)=> [y ye xy];ex_tac.
move=> [y [yX xy _ ]]; apply: (setU_i xy yX).
Qed.

Lemma exercise6_11b2 X:
   symmetric_r (exercise6_11b_rel X).
Proof. 
move=> E y; rewrite /exercise6_11b_rel.
by move=>[A [Ax xA yA]];  exists A.
Qed.

Lemma exercise6_11b3 E X: exercise6_11b_assumption X E -> 
  let R := exercise6_11b_rel X in
    forall  x y z t,  
      x <> y ->  x<>z -> x <> t -> y <> z -> y <> t -> z <> t ->
      R x y -> R x z -> R x t -> R y z -> R y t -> R z t.
Proof. 
move=> [uX alne i2 i3] R x y z t nxy nxz nxt nyz nyt nzt
 [XY [XYX xXY yXY]]  [XZ [XZX xXZ zXZ]] [XT [XTX xXT tXT]]
 [YZ [YZX yYZ zYZ]]  [YT [YTX yYT tYT]]. 
case: (equal_or_not XZ XT) => XZXT; first by exists XT; split => //; ue.
case: (equal_or_not XZ YT) => XZYT; first by exists XZ; split => //; ue.
case: (equal_or_not YZ XT) => YZXT; first by exists XT; split => //; ue.
case: (equal_or_not YZ YT) => YZYT; first by exists YT; split => //; ue.
have iXZXT:  (XZ \cap XT = singleton x).  
  by apply: set1_pr2; [ fprops | case: (i2 _ _ XZX XTX)].
have iYZYT:  (YZ \cap YT = singleton y). 
  by apply: set1_pr2; [ fprops | case: (i2 _ _ YZX YTX) ].
case: (equal_or_not XY XZ)=> XYXZ.
  have XYYZ: XY= YZ.
    have yp1:inc y (XY \cap YZ) by fprops.
    have zp1:inc z (XY \cap YZ) by rewrite XYXZ; fprops.
    case: (i2 _ _ XYX YZX) =>// h; case: nyz;apply: (h _ _ yp1 zp1).
  case: (equal_or_not XY YT)=> XYYT; first by exists XY; aw; split => //; ue. 
  case: (equal_or_not XT YT) => XTYT. 
    have xp: inc x (XY \cap YT) by aw; ue. 
    have yp: inc y (XY \cap YT) by aw; ue.  
    case (i2 _ _ XYX YTX) =>// h. 
    case: nxy;apply: (h _ _ xp yp).
  case: (i3 _ _ _ XYX XTX YTX); first by move=> h;exists XY; split => //; ue.
  case; first by move=> h. 
  case; first by move=> h. 
  case; first by move=> h;empty_tac1 x; aw.
  case; first by rewrite XYYZ; move=> h; empty_tac1 y; aw.
  case; first by move=> h; empty_tac1 t; aw.
  move=> [r1 r2].
  have : inc t (XT \cap YT) by fprops.
  by rewrite -r2 XYYZ;move /setI2_P=> [tp _];  exists YZ.
have iXYXZ: (XY \cap XZ = singleton x).
  by apply: set1_pr2; fprops; case:  (i2 _ _ XYX XZX).
case:(equal_or_not XZ YZ)=> XZYZ. 
  have : inc y (singleton x) by rewrite - iXYXZ; apply/setI2_P; split => //; ue.
  move/set1_P => h; case: nxy =>//.
have iXZYZ:  (XZ \cap YZ = singleton z).
   apply: set1_pr2; fprops; case  (i2 _ _ XZX YZX) => //.
case: (equal_or_not XY YT)=> XYYT. 
  have XYXY:  (XY = XT).
    have xp: inc x (XY \cap XT)  by fprops.
    have tp: inc t (XY \cap XT) by rewrite XYYT; fprops.
    case (i2 _ _ XYX XTX) =>// h; case: nxt;apply: (h _ _ xp tp).
  case: (equal_or_not XY YZ)=> XYYZ; first by exists XY;split => //; ue. 
  case: (i3 _ _ _ XYX XZX YZX); first by move=> h;exists XY.
  case; first by move=> h. 
  case; first by move=> h. 
  case; first by move=> h;empty_tac1 x; aw.
  case; first by move=> h; empty_tac1 y; aw.
  case; first by move=> h; empty_tac1 z; aw.
  move=> [r1 r2].
  have : inc z (XZ \cap YZ) by  fprops.
  rewrite -r2 XYYT;move /setI2_P=> [tp _]; exists YT; by aw.
have iXYYT: (XY \cap YT = singleton y).
  by apply: set1_pr2; fprops; case:  (i2 _ _ XYX YTX).
case:  (equal_or_not XT YT)=> XTYT. 
  have : inc x (singleton y) by rewrite -iXYYT; apply/setI2_P; split => //; ue.
  move/set1_P => h; case: nxy =>//.
have iXTYT:  (XT \cap YT = singleton t).
  by apply:set1_pr2;fprops;case: (i2 _ _ XTX YTX).
case (equal_or_not XY XT)=> XYXT. 
  case: (equal_or_not XY YZ)=> XYYZ; first by case: YZXT; ue.  
  case: (i3 _ _ _ XYX XZX YZX); first by move=> h.
  case; first by move=> h.
  case; first by move=> h.
  case; first by move=> h;empty_tac1 x; aw.
  case; first by move=> h;empty_tac1 y; aw.
  case; first by move=> h;empty_tac1 z; aw.
  rewrite iXYXZ iXZYZ; move=> [_ sxz].
  by case: nxz; apply: set1_inj.
case: (i3 _ _ _ XYX XTX YTX); first by move=> h.
case; first by move=> h.
case; first by move=> h.
case; first by move=> h;empty_tac1 x; aw.
case; first by move=> h;empty_tac1 y; aw.
case; first by move=> h;empty_tac1 t; aw.
rewrite iXYYT iXTYT; move=> [sy st].
by rewrite sy in st; case: nyt; apply: set1_inj.
Qed.

Lemma exercise6_11b4 E X
  (R := exercise6_11b_rel X)
  (p1 := fun u => (exists a b, [/\ a<> b, R a b & u = 
      Zo E (fun x => R a x /\ R b x)]))
  (p2:= fun u => (exists x, [/\ u = singleton x, inc x E &
      forall y, inc y E -> R x y -> x = y]))
  (p3:= fun u => (exists v, [/\ inc v X, u <> v, sub u v & singletonp u])):
  exercise6_11b_assumption X E -> 
    [/\  (forall u, inc u X -> p1 u \/ p2 u \/ p3 u ),
      (forall u, p1 u -> inc u X) & (forall u, p2 u -> inc u X)].
Proof. 
move => [uXE alne i2 i3]; split.
  move=> u uX.
  case: (p_or_not_p (singletonp u)) => su.
    right; case: (p_or_not_p (p3 u)) => p3u; first by right.
    left; move: (su) => [x sx]. 
    rewrite sx; exists x; split => //.
      rewrite -uXE; apply: (@setU_i _  u) =>//; rewrite sx; fprops.
    move=> y yE Rxy; case: (equal_or_not x y) =>//. 
    move=> xy; move: Rxy=> [A [AX xA yA]].
    case p3u; exists A; split =>//.  
      by dneg uA; move: yA; rewrite -uA sx;move /set1_P.
    by move=> t; rewrite sx; move/set1_P => ->.
  constructor 1; red.
  move: (alne _ uX) => [y yu]; exists y.
  case (p_or_not_p (exists2 v, inc v u & v <> y)). 
    move=> [x xu xy]; exists x;split; [auto | by exists u |].
    set_extens w.
       move=> wu; apply: Zo_i.
        rewrite - uXE; apply: (@setU_i _ u) =>//. 
      split;exists u; split => //.
    move /Zo_P=> [wE [ [A [AX xA yA]]  [A' [AX' xA' yA']]]].
    case: (equal_or_not A u)=> Au; first by rewrite -Au. 
    case: (equal_or_not A' u)=> Au'; first by rewrite -Au'. 
    have xi: (inc x (u \cap A')) by fprops.
    have yi: (inc y (u \cap A)) by fprops.
    case: (equal_or_not A A') => AA'. 
      case: (i2 _ _ uX AX)=> aux. 
        by case: Au'; rewrite -AA' aux.
      rewrite -AA' in xi.
      by case: xy; apply:(aux _ _ xi yi).
    move: (i3 _ _ _ AX AX' uX).
    case =>//; case =>//; case =>//.
    case; first by move=> h; empty_tac1 w; aw.
    case; first by move=> h; empty_tac1 y; aw.
    case; first by move=> h; empty_tac1 x; aw.
    move=> [h1 h2]. 
    rewrite setI2_C -h2 in xi.
    rewrite setI2_C -h1 in yi.
    case: (i2 _ _ AX AX')=>// aux. 
    case: xy; by apply: (aux _ _ xi yi).
  move=> h;case: su; exists y; apply: set1_pr1; first by ex_tac.
  move => w wu;case: (equal_or_not w y) =>// wy;  by case: h; ex_tac.
(* last case *)
  move=> u [a [b [nab [A [AX aA bA]] uZ]]].
  suff: (u = A) by  move=> ->.
  rewrite uZ; set_extens t. 
    move /Zo_P=> [tE [[A' [AX' aA' bA']]] [A'' [AX'' aA'' bA'']]].
    case: (equal_or_not A A'')=> AA''; first by ue. 
    case: (equal_or_not A A')=> AA'; first by ue. 
    have aAA: inc a (A \cap A') by fprops.
    have bAA: inc b (A \cap A'') by fprops.
    case: (equal_or_not A' A'') => aux.
    case: (i2 _ _ AX AX')=> // ss. 
      rewrite -aux in bAA; case: nab; apply: (ss _ _ aAA bAA).
    case: (i3 _ _ _ AX AX' AX'') =>//; case =>//; case =>//.
    case; first by move=> h; empty_tac1 a; aw.
    case; first by move=> h; empty_tac1 b; aw.
    case; first by move=> h; empty_tac1 t; aw.
    move=> [h1 h2]; rewrite - h1 in  bAA.
    case: (i2 _ _ AX AX')=>// ss. 
    case: nab; by apply: (ss _ _ aAA bAA).
  move=> tA; apply: Zo_i.
      rewrite -uXE;apply: (@setU_i _ A)=>//. 
    by split;exists A.
move=> u  [v [uv vE su]].
move: vE;rewrite  -uXE; move/setU_P=> [y vy yX].
suff: u = y by move=> ->.
rewrite uv; symmetry; apply:set1_pr => // t tv.
symmetry;apply: su.
  rewrite -uXE;apply: (@setU_i _ y) =>//.
by exists y.
Qed.


End Exercise1.
Export Exercise1.

