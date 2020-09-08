(** * Theory of Sets  EII-6 Equivalence relations
  Copyright INRIA (2009-2013-2018) Apics; Marelle Team (Jose Grimm).
  Part of this code comes from Carlos Simpson 
*)
(* $Id: sset4.v,v 1.6 2018/09/04 07:58:00 grimm Exp $ *)

Set Warnings "-notation-overridden".
From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Warnings "notation-overridden".



Require Export sset3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** ** EII-6-1 Definition of an equivalence relation *)

Module Relation.

(** the substrate of a relation are elements that are relate *)

Definition substrate r :=  (domain r) \cup (range r).

Lemma pr1_sr r y:
  inc y r -> inc (P y) (substrate r).
Proof. move => yr; apply: setU2_1; apply/funI_P; ex_tac. Qed.

Lemma pr2_sr r y:
  inc y r -> inc (Q y) (substrate r).
Proof. move => yr; apply: setU2_2; apply/funI_P; ex_tac. Qed.

Lemma arg1_sr r x y:
  related r x y -> inc x (substrate r).
Proof. by move=> rel; rewrite -(pr1_pair x y); apply: pr1_sr.  Qed.

Lemma arg2_sr r x y:
  related r x y -> inc y (substrate r).
Proof. by move=> rel;rewrite -(pr2_pair x y); apply: pr2_sr. Qed.

Ltac substr_tac := 
  match  goal with 
    | H:inc ?x ?r |- inc (P ?x) (substrate ?r) 
      => apply: (pr1_sr H)
    | H:inc ?x ?r |- inc (Q ?x) (substrate ?r) 
      => apply: (pr2_sr H)
    | H:related ?r ?x _ |- inc ?x (substrate ?r)
      => apply: (arg1_sr H)
    | H:related ?r _ ?y |- inc ?y (substrate ?r) 
      => apply: (arg2_sr H)
    | H:inc(J ?x _ ) ?r|- inc ?x (substrate ?r) 
      => apply: (arg1_sr H)
    | H: inc (J _ ?y) ?r |- inc ?y (substrate ?r) 
      => apply: (arg2_sr H)
  end.

Lemma substrate_smallest r s:
  (forall y, inc y r -> inc (P y) s) ->
  (forall y, inc y r -> inc (Q y) s) ->
  sub (substrate r) s.
Proof. move=> h1 h2 x; case /setU2_P; move/funI_P => [z zr ->]; fprops. Qed.

Lemma substrate_P r:  sgraph r -> forall x,
  inc x (substrate r) <-> 
      ((exists y, inc (J x y) r) \/  (exists y, inc (J y x) r)).
Proof.  
move => gr x; split; last by case => [] [y yr]; substr_tac.
by case /setU2_P => /funI_P [z zr ->]; [left | right]; ex_tac; rewrite gr.  
Qed.

(** Reflexivity etc. properties for a relation *)

Section Definitions.
Implicit Type  (r: relation).

Definition reflexive_re r E :=
  forall x, inc x E <-> r x x.

Definition reflexive_rr r :=
  forall x y, r x y -> (r x x /\  r y y).

Definition equivalence_r r :=
  symmetric_r r /\ transitive_r r.

Definition equivalence_re r E :=
  equivalence_r r /\ reflexive_re r E.

Definition order_r r :=
  [/\ transitive_r r,  antisymmetric_r r & reflexive_rr r].

Definition preorder_r r :=
  transitive_r r /\ reflexive_rr r.

Definition order_re  (r: relation)  x :=
  order_r r /\ reflexive_re r x.

End Definitions.

(** Same definitions for a graph *)

Definition reflexivep r :=  forall y, inc y (substrate r) -> related r y y.
Definition symmetricp r := symmetric_r (related r).
Definition antisymmetricp r := antisymmetric_r (related r).
Definition transitivep r :=  transitive_r (related r).

Definition equivalence r :=
  [/\ sgraph r, reflexivep r, transitivep r & symmetricp r].

Definition order r :=
  [/\ sgraph r, reflexivep r, transitivep r & antisymmetricp r].

Definition preorder r :=
  [/\ sgraph r, reflexivep r & transitivep r].

Definition order_on r E := order r /\ substrate r = E.
Definition equivalence_on r E := equivalence r /\ substrate r = E.


(** Basic properties *)

Lemma equivalence_sgraph  r: equivalence r -> sgraph r.
Proof. by move=>  []. Qed.

Lemma order_sgraph r: order r -> sgraph r.
Proof. by move => []. Qed.

Lemma preorder_sgraph r: preorder r -> sgraph r.
Proof. by move => []. Qed.

Hint Resolve order_sgraph equivalence_sgraph : fprops.

Lemma reflexive_domain g: reflexivep g -> domain g = substrate g.
Proof. 
move=> pb; set_extens u; first by apply: setU2_1.
case /setU2_P => // ug; apply/funI_P; exists (J u u);aw; trivial.
exact:(pb _  (setU2_2 (domain g) ug)).
Qed.

Lemma domain_sr g: equivalence g -> domain g = substrate g.
Proof. move=> h; apply: (reflexive_domain (proj42 h)). Qed.


Lemma domain_sr1 r: order r -> domain r = substrate r.
Proof.  move=> h; apply: (reflexive_domain (proj42 h)). Qed.

Lemma substrate_sub: {compat substrate : x y / sub x y}.
Proof. 
move => r s rs; move: (domain_S rs) (range_S rs) => pa pb t.
case /setU2_P => h; apply/setU2_P; fprops.
Qed. 

Lemma symmetric_transitive_equivalence r:
  sgraph r -> symmetricp r -> transitivep r -> equivalence r.
Proof. 
move=> gr sr tr; hnf; split => //.
move => y /(substrate_P gr) [][z pr].
   apply: (tr _ _ _ pr (sr _ _ pr)).
apply: (tr _ _ _  (sr _ _ pr) pr).
Qed. 

Lemma equivalence_relation_pr1 g:
  sgraph g -> equivalence_r (related g)  -> equivalence g.
Proof.
move=> gg [sr tr]; apply: symmetric_transitive_equivalence => //.
Qed.

Lemma reflexivity_e r u:
  equivalence r -> inc u (substrate r) -> related r u u.
Proof. by  move=> er us; apply:(proj42 er). Qed.

Lemma symmetricity_e r u v:
  equivalence r -> related r u v -> related r v u.
Proof. by move=> /proj44; apply. Qed.

Lemma transitivity_e  r v u w:
  equivalence r ->  related r u v -> related r v w -> related r u w.
Proof.
move=> er r1 r2; apply: ((proj43 er) _ _ _ r1 r2).
Qed.

Ltac equiv_tac:=
  match goal with 
    | H: equivalence ?r, H1: inc ?u (substrate ?r) |- related ?r ?u ?u
      => apply: (reflexivity_e H H1) 
    | H: equivalence ?r |- inc (J ?u ?u) ?r
      => apply: reflexivity_e
    | H:equivalence ?r, H1:related ?r ?u ?v |- related ?r ?v ?u
      => apply: (symmetricity_e H H1)
    | H:equivalence ?r, H1: inc (J ?u ?v) ?r |- inc (J ?v ?u) ?r
      => apply: (symmetricity_e H H1)
    | H:equivalence ?r, H1:related ?r ?u ?v, H2: related ?r ?v ?w
      |- related ?r ?u ?w
      => apply: (transitivity_e H H1 H2)
    | H:equivalence ?r, H1:related ?r ?v ?u, H2: related ?r ?v ?w
      |- related ?r ?u ?w
      => apply: (transitivity_e H (symmetricity_e H H1) H2)
    | H:equivalence ?r, H1:related ?r ?u ?v, H2: related ?r ?w ?v
      |- related ?r ?u ?w
      => apply: (transitivity_e H H1 (symmetricity_e H H2))
    | H: equivalence ?r, H1: inc (J ?u ?v) ?r, H2: inc (J ?v ?w) ?r |-
      inc (J ?u ?w) ?r
      => apply: (transitivity_e H H1 H2)
end.



(** Comparison of the two sets of definitions *)

Lemma equivalence_equivalence r:
  equivalence r -> equivalence_re (related r)(substrate r).
Proof. 
move => [gr ra rb rc]; split => // y.
by split => p; [ apply: ra | substr_tac ].
Qed.

(** We say that [g] is the graph of [r] if [related g] is the same function 
as [r]. We define the graph of [r] on [x] as the set of pairs of [x] related
 by [r] *)

Definition graph_on (r:relation) x:= 
  Zo(coarse x)(fun w => r (P w)(Q w)).


Lemma graph_on_exten (p q: relation) E:
  (forall x y, inc x E -> inc y E -> (p x y <-> q x y)) ->
  graph_on p E = graph_on q E.
Proof.
move => hyp.
by set_extens t;move/Zo_P => [pa pb]; move/setX_P: (pa) => [_ qa qb];
  apply: (Zo_i pa); apply/hyp.
Qed.

Lemma graph_on_graph r x: sgraph (graph_on r x).
Proof. by move => y /Zo_S /setX_P [ok _].  Qed.

Lemma graph_on_P0 r x a b:
  inc (J a b) (graph_on r x) <-> [/\ inc a x, inc b x & r a b].
Proof. 
split; first by move/Zo_P => [] /setX_P; aw ; move => [pa pb pc] pd;split.
by move => [pa pb pc]; apply: Zo_i; [apply: setXp_i | aw].
Qed.

Lemma graph_on_P1 r x a b:
  related (graph_on r x) a b <->  [/\ inc a x, inc b x & r a b].
Proof. apply/graph_on_P0. Qed.

Lemma graph_on_P2 r x : equivalence_re r x -> forall u v,
  (related (graph_on r x) u v <-> r u v).
Proof.
move=> [[rs rt] rr] u v; split; first by move/Zo_hi; aw.
move => ruv; apply/ graph_on_P1.
move: (rs _ _ ruv) => rvu; move: (rt _ _ _ ruv rvu) => ruu.
by move: (rt _ _ _ rvu ruv) => rvv; split => //; apply rr.
Qed.

Lemma graph_on_P3 r x:  order_re r x -> forall u v,
  (related (graph_on r x) u v <-> r u v).
Proof.
move=> [[_ _ cc] rr]; split; first by move /Zo_hi; aw.
move => ruv; move: (cc _ _ ruv) => [ruu rvv]. 
by apply: Zo_i ; [by  apply:setXp_i; apply /rr |  aw].
Qed.

Lemma graph_on_sr1 r x:  sub (substrate (graph_on r x)) x.
Proof. 
by move=> y /(substrate_P (@graph_on_graph r x))[] [z] /graph_on_P0 [pa pb _].
Qed.

Lemma order_preorder r: order r -> preorder r.
Proof. by move => [gr tr ar rr]. Qed.

Lemma preorder_from_rel r x:
  preorder_r r -> preorder (graph_on r x).
Proof. 
move=> pr.
have gg: sgraph (graph_on r x) by apply: graph_on_graph.
move: pr=> [tr rr].
split=>//.
  by move=> y /(substrate_P gg) [] [z] /graph_on_P0 [yx zx ryz];
   apply /graph_on_P0; split => // ;move: (rr _ _ ryz) => [].
move=> a b c /graph_on_P1 [ax bx rab] /graph_on_P1 [_ cx rbc].
apply /graph_on_P1;split => //; apply: tr rab rbc.
Qed.

Lemma order_from_rel r x: order_r r -> order (graph_on r x).
Proof.
move=> [ta tb tc].
have [tr pa pb]: preorder (graph_on r x) by apply: preorder_from_rel; split.
split => //.
by move=> a b /graph_on_P1 [ax bx rab] /graph_on_P1 [_ _ rba]; apply: tb.
Qed.

Lemma equivalence_from_rel r x:
  equivalence_r r -> equivalence (graph_on r x).
Proof.
move=> [pa pb].
have gg: sgraph (graph_on r x) by apply: graph_on_graph.
apply: (equivalence_relation_pr1 gg).
split.
   move => a b /graph_on_P1 [ax bx rab]; apply /graph_on_P1. 
   by split => //; apply: pa.
move=> a b c /graph_on_P1 [ax bx rab] /graph_on_P1 [_ cx rbc].
apply /graph_on_P1;split => //; apply: pb rab rbc.
Qed.

Lemma graph_on_sr (r: relation) x:
  (forall a, inc a x -> r a a) ->
  substrate (graph_on r x) = x.
Proof.
move=> rr.
apply: extensionality; first by apply: graph_on_sr1.
move => t xt; move: (rr _ xt) => rtt.
by apply: (arg1_sr (y:=t)); apply: Zo_i; [apply:setXp_i | aw].
Qed.



(** Finest relation on a set: an element is only related to itself 
 The correspondence is the identity, the graph is the diagonal *)

Definition restricted_eq x := fun u v => inc u x /\ u = v.

Lemma diagonal_graph_on x: graph_on (restricted_eq x) x = diagonal x.
Proof.
set_extens t. 
  move /Zo_P => [pa [pb pc]]; apply /diagonal_i_P;split=> //. 
  by move /setX_P: pa =>[].
move /diagonal_i_P=> [pa pb pc];apply/Zo_i => //; apply /setX_P; split => //;ue.
Qed.

Lemma diagonal_equivalence x: equivalence_on (diagonal x) x.
Proof.
rewrite -diagonal_graph_on; split; last by rewrite graph_on_sr // => t tx.
apply: equivalence_from_rel;split.
  by move=> a b /= [ax] <-.
by move=> a b c [au ab] [bu bc]; split =>//; ue.
Qed.

Lemma diagonal_osr x: order_on (diagonal x) x.
Proof.
rewrite -diagonal_graph_on; split; last by rewrite graph_on_sr //_ => t tx.
apply: order_from_rel;split.
- by move=> a b c [au ab] [bu bc]; split =>//; ue.
- by move=> a b /= [ax <-].
- by move=> a b [aa <-].  
Qed.

(** Example of an equivalence without graph: equipotency *)

Lemma equipotent_equivalence: equivalence_r equipotent.
Proof. 
split; first by move=> x y;apply: EqS. 
move => x y z; apply: EqT.
Qed.

(** The coarsest relation on a set: everything is related *)
 

Lemma coarse_related u x y:
  related (coarse u) x y <-> (inc x u /\ inc y u). 
Proof.
by split; [ move/setX_P => [_]; aw | move => [pa pb];apply : setXp_i ].
Qed. 

Lemma coarse_graph x: sgraph (coarse x).
Proof. apply: setX_graph. Qed.

Lemma coarse_equivalence  u:  equivalence_on (coarse u) u. 
Proof.
have sr: substrate (coarse u) = u.
  rewrite /coarse/substrate. 
  transitivity (u \cup u); last by apply: setU2_id.
  case: (emptyset_dichot u); first by move ->; rewrite setX_0l; aw.  
  by move=> h; aw;rewrite setX_domain // setX_range //.
split; [split | exact].
- by apply: coarse_graph. 
- by move => y; rewrite sr => yu;apply/ coarse_related.
   move=> x y z /coarse_related [pa pb]/coarse_related [pc pd].
- by apply/coarse_related.
- by move=> x y /coarse_related  [pc pd]; apply/coarse_related.
Qed.

Lemma sub_graph_coarse_substrate r:
  sgraph r -> sub r (coarse (substrate r)).
Proof. 
rewrite /coarse=> gr t tr; apply: setX_i; first (by apply: gr); substr_tac. 
Qed.

(** Example 5 page E II.114 *)

Lemma equivalence_relation_bourbaki_ex5 A E
    (r := (fun x y => (inc x (E -s A) /\ (x = y) \/ (inc x A /\ inc y A)))):
    sub A E ->  equivalence_on (graph_on r E)  E.
Proof. 
move => sa; split; last first.
  apply: graph_on_sr; move => a ae.
  by case: (inc_or_not a A) => h; [right | left]; split => //; apply /setC_P.
apply: equivalence_from_rel; split.
  move=> x y; case=> [] [pa pb]; [left | right ]; split => //; ue.
move => y x z [] [pa pb]; first by rewrite pb.
move => h;right; case:h =>  [] [qa qb]; split => //; ue.
Qed.

(** Intersection of equivalence relations is an equivalence *)

Lemma setIrel_graph  z:
  (alls z sgraph) -> sgraph (intersection z).
Proof. 
case: (emptyset_dichot z).
   move => -> _; rewrite setI_0; apply: sgraph_set0.
move => [t tz] alg y yi; apply: (alg _ tz); exact: (setI_hi yi tz).
Qed.


Lemma setIrel_P z:  nonempty z -> forall x y,
  (related (intersection z) x y <->
    (forall r, inc r z -> related r x y)). 
Proof. move=> nez x y; apply/(setI_P nez). Qed.

Lemma setIrelR z:
  (alls z reflexivep) -> reflexivep (intersection z).
Proof.
move => alr.
case: (emptyset_dichot z).
   move => -> x; rewrite setI_0 /substrate domain_set0 range_set0.
   by case /setU2_P => /in_set0.
move => nez y ys; apply/(setIrel_P nez) => r rz; apply: (alr _ rz).
apply: (substrate_sub (setI_s1 rz) ys).
Qed.

Lemma setIrel_sr z e:
  nonempty z -> (alls z reflexivep) ->
  (forall r, inc r z -> substrate r = e) ->
  substrate (intersection z) = e.
Proof. 
move=> nez allr alls.
move: (setIrelR allr)=> ir. 
set_extens t => ts.
  move: (ir _ ts); rewrite /related=> aux.
  move: nez => [u uz]; move: (setI_hi aux uz) => Ju.
  by rewrite - (alls _ uz); apply: (arg1_sr Ju).
have rtt: related (intersection z) t t.
  apply/(setIrel_P nez) => r rz; rewrite - (alls _ rz) in ts. 
  by apply: (allr _ rz). 
substr_tac.
Qed.

Lemma setIrelT z:
  (alls z transitivep) -> transitivep (intersection z).
Proof. 
move=> allt; case: (emptyset_dichot z).
   move => ->; rewrite setI_0 => a b c;case; case.
move=> neX y x u /(setIrel_P neX) rxy /(setIrel_P neX) ryz. 
apply/(setIrel_P neX) => r rz. 
exact: ((allt _ rz) _ _ _ (rxy _ rz)  (ryz _ rz)).
Qed.


Lemma setIrelS z:
  (alls z symmetricp) -> symmetricp (intersection z).
Proof.
move=> alls; case: (emptyset_dichot z).
  move ->; rewrite setI_0 => a b; case; case.
move=>nez x y /(setIrel_P nez) rxy; apply/(setIrel_P nez) => r rz.
apply: ((alls _ rz) _ _ (rxy _ rz)).
Qed.

Lemma setIrel_equivalence z:
  (alls z equivalence) -> equivalence (intersection z).
Proof. 
move=> alleq; apply: symmetric_transitive_equivalence.
- by apply: setIrel_graph => r /alleq  []. 
- by apply: setIrelS=> // r /alleq [_ _]. 
- by apply: setIrelT=> // r /alleq [_ _ ]. 
Qed.

Lemma setIrel_or z: (alls z order) -> order (intersection z).
Proof. 
move=> alleq;split.
- by apply: setIrel_graph => r /alleq [].
- by apply: setIrelR => r /alleq [_ ].
- by apply: setIrelT=> //  r /alleq [_ _ ]. 
- case: (emptyset_dichot z).
    move => ->; rewrite setI_0 => a b; case; case.
  move => [t te] x y pa pb; move: (alleq _ te)=> [_ _ _]; apply.
    apply:(setI_hi pa te).
  apply:(setI_hi pb te).
Qed.

(** The set of all relations or all equivalences of a set *)

Definition equivalences x :=
  Zo (\Po (coarse x)) (equivalence_on ^~ x).


Lemma equivalencesP r x:
  inc r (equivalences x) <-> (equivalence_on r x).
Proof. 
split; first by move /Zo_hi. 
move => pa; apply:Zo_i => //; apply/setP_P.
move: pa => [[xx _ _ _] <-].
by move: (sub_graph_coarse_substrate xx). 
Qed. 

Lemma inc_coarse_all_equivalence_relations u:
  inc (coarse u) (equivalences u).
Proof. 
by apply/equivalencesP; apply: coarse_equivalence. 
Qed.

(** We show that an equivalence is a self-inverse projector *)

Lemma selfinverse_graph_symmetric r: sgraph r ->
  (symmetricp r <-> (r = inverse_graph r)).
Proof.
move => gr; split => sp; last by move => x y Jr; rewrite sp; apply/igraph_pP.
set_extens t => tr.
  move: (gr _ tr) => aux.
  by rewrite - aux; apply/igraph_pP; apply: sp; hnf; rewrite  aux.
by move /igraphP: tr => [pt pa]; rewrite -pt; apply: sp.
Qed.

Lemma idempotent_graph_transitive r:
  sgraph r -> (transitivep r <-> sub  (r \cg r) r).
Proof. 
move=> gr; split. 
  move=> tr t /compg_P [pt [y J1r J2r]].
  rewrite - pt; move: tr J1r J2r; apply.
by move => h x y z Jxy Jyz; apply: h; apply/compg_pP; exists x.
Qed.

Theorem equivalence_pr r:
  equivalence r  <-> ((r \cg r) = r /\  r = inverse_graph r).
Proof.
split => hyp. 
  move: (hyp) => [pa pb pc pd].
  split; last by apply /selfinverse_graph_symmetric.
  apply: extensionality.
    by apply /idempotent_graph_transitive.
  move=> x xr; move: (pa _ xr) => px.
  rewrite - px; apply /compg_pP; exists (P x); rewrite ? px //.
  equiv_tac =>//; substr_tac.
move: hyp=> [crr ri].
have gr: (sgraph r) by rewrite ri; fprops.
apply: symmetric_transitive_equivalence => //.
  by apply /selfinverse_graph_symmetric.
apply/idempotent_graph_transitive => //; rewrite crr; fprops.
Qed.


(** ** EII-6-2 Equivalence classes; quotient set *)

(** Equivalence associated to a function [f] by  [f x = f y] *)

Definition eq_rel_associated f x y := 
  [/\ inc x (source f), inc y (source f) & Vf f x = Vf f y].

Definition equivalence_associated f := 
   (inverse_graph (graph f)) \cg (graph f).

Section EquivalenceAssociated.
Variable (f: Set).
Hypothesis (ff : function f).

Lemma ea_graph_on: 
   graph_on (eq_rel_associated f) (source f) = equivalence_associated f.
Proof.
set_extens t. 
  move /Zo_P => [/setX_P[pe _ _] [pb pc pd]].
  rewrite - pe; apply /compg_pP; exists (Vf f (P t)) => //; first Wtac.
  apply/igraph_pP; rewrite pd; Wtac.
move/compg_P => [pt [z pa /igraph_pP pb]].
have pc: inc (P t) (source f) by Wtac.
have pd: inc (Q t) (source f) by Wtac.
apply: Zo_i; first by apply /setX_P.
by split => //; rewrite - (Vf_pr ff pa) - (Vf_pr ff pb).
Qed.

Lemma ea_relatedP x y:
  related (equivalence_associated f) x y <->
  [/\ inc x (source f), inc y (source f) & Vf f x = Vf f y].
Proof. 
rewrite - ea_graph_on; split; first by move/graph_on_P1 => [_ _].
by move =>[pa pb pc]; hnf; apply /graph_on_P1.
Qed.


Lemma graph_ea_equivalence:
  equivalence_on (equivalence_associated f) (source f).
Proof.
rewrite - ea_graph_on; split; last by rewrite graph_on_sr. 
apply: equivalence_from_rel; split.
  by move => a b [pa pb pc].
move => a b c [pa pb pc] [pd pe pf]; split  => //; ue.
Qed. 

End EquivalenceAssociated.

(** The class of [x] is the set of elements related to [x] *)

Definition class r x := fun_image (Zo r (fun z => P z = x)) Q.
Definition quotient r := fun_image (substrate r) (class r).
Definition classp r x := inc (rep x) (substrate r) /\ x = class r (rep x).

Section Class.
Variable (r:Set).
Hypothesis (er: equivalence r).

Lemma class_P x y:  inc y (class r x) <-> related r x y.
Proof. 
have gr: (sgraph r) by fprops.
rewrite /related; split.
  by move/funI_P => [z /Zo_P [pa <-] ->]; rewrite (gr _ pa).
by move=> h; apply/funI_P; exists (J x y); [ apply: Zo_i |]; aw.
Qed.

Lemma class_is_im_of_singleton x: 
  class r x = im_of_singleton r x. 
Proof. 
set_extens t; first by move/class_P/dirim_set1_P.
by move/dirim_set1_P/class_P.
Qed.

Lemma sub_class_substrate x: sub (class r x) (substrate r).
Proof. move=> t /class_P rt; substr_tac. Qed.

Lemma class_eq1 u v:  related r u v -> class r u = class r v.
Proof. 
move=> ruv; set_extens x; move/class_P => h; apply/class_P; equiv_tac.
Qed.

Lemma class_eq2 u v: inc u (class r v) -> class r u = class r v.
Proof.
by move =>  pb; symmetry;apply: class_eq1; apply/class_P.
Qed.

Lemma setQ_ne x: inc x (quotient r) -> nonempty x.
Proof. 
by move/funI_P => [z zr ->]; exists z; apply/class_P; equiv_tac.
Qed.

Lemma setQ_repi x: inc x (quotient r) -> inc (rep x) x.
Proof. by move => /setQ_ne; apply: rep_i. Qed.

Lemma inc_class_setQ x:
  inc x (substrate r) -> inc (class r x) (quotient r).
Proof. move => ta; apply/funI_P; ex_tac. Qed.

Lemma class_class x: inc x (substrate r) -> classp r (class r x).
Proof. 
move=> xs; move: (setQ_repi (inc_class_setQ xs)) =>/class_P rxr.
by split =>//; [substr_tac | apply: class_eq1].
Qed.

Lemma setQ_P x: inc x (quotient r) <-> classp r x.
Proof. 
apply: (iff_trans (funI_P _ _ _)); split.
  by move => [z zs ->]; apply: class_class.
move => [pa pb]; ex_tac.
Qed.

Lemma class_rep x: inc x (quotient r) -> class r (rep x) = x.
Proof. by move /setQ_P => [_].  Qed. 

Lemma in_class_relatedP  y z:
  related r y z <-> (exists x, [/\ classp r x, inc y x & inc z x]).
Proof. 
split.
  move=> ryx;exists (class r y). 
  have ys: inc y (substrate r) by substr_tac.
  split; first (by apply: class_class); apply/class_P => //; equiv_tac.
move =>[w [ [_ ->]]] /class_P pb /class_P pc; equiv_tac.
Qed.

Lemma related_rep_in_class  x y:
  inc x (quotient r) -> inc y x -> related r (rep x) y.
Proof. 
move=> xq; move: (xq) =>/setQ_P cx yx; apply/in_class_relatedP; exists x.
split => //;by apply: setQ_repi.
Qed.

Lemma rep_in_class x: classp r x -> inc (rep x) x.
Proof. move /setQ_P; apply: setQ_repi. Qed.

Lemma rel_in_class x y: classp r x -> inc y x -> related r (rep x) y.
Proof. by move /setQ_P => xq yx; apply: related_rep_in_class. Qed.

Lemma sub_class_sr x: classp r x -> sub x (substrate r).
Proof. move => [pa ->]; apply: sub_class_substrate. Qed.

Lemma rel_in_class2 x y: classp r x -> related r (rep x) y -> inc y x.
Proof. by move => pa pb; rewrite (proj2 pa); apply /class_P. Qed.

Lemma class_dichot x y: classp r x -> classp r y -> disjointVeq x y.
Proof. 
move=> cx cy; mdi_tac xy.
move => u ux uy; case: xy.
move: (rel_in_class cx ux) => pa.
move: (rel_in_class cy uy) => pb.
rewrite (proj2 cx)  (proj2 cy); apply: class_eq1; equiv_tac.
Qed.

Lemma inc_in_setQ_sr x y:
  inc x y -> inc y (quotient r) -> inc x (substrate r).
Proof. 
move=> xy /setQ_P [pa pb]; apply: (@sub_class_substrate (rep y)); ue.
Qed.

Hint Resolve inc_class_setQ: fprops.

Lemma setU_setQ: union (quotient r) = substrate r. 
Proof.
set_extens t => ts. 
  move: (setU_hi ts) => [z tz zu]; apply: (inc_in_setQ_sr  tz zu).
apply: (@setU_i _ (class r t)); [ apply/class_P; equiv_tac | fprops].
Qed. 

Lemma rep_i_sr x:  inc x (quotient r) -> inc (rep x) (substrate r).
Proof. by move /setQ_P => [g _]. Qed.

Lemma inc_itself_class x: inc x (substrate r) ->  inc x (class r x).
Proof. move => xsr; apply/class_P; equiv_tac. Qed.

Lemma related_rep_class x: inc x (substrate r) -> related r x (rep (class r x)).
Proof. 
move=> xs.
suff: related r (rep (class r x)) x by move=> h; equiv_tac.
by apply: related_rep_in_class; fprops; apply: inc_itself_class.
Qed.
 
Lemma related_rr_P u v:
  inc u (quotient r) -> inc v (quotient r) ->
  (related r (rep u) (rep v) <-> (u = v)). 
Proof.
move => uq vq; split.
  move=> h; rewrite - (class_rep uq) -(class_rep vq).
  by apply: class_eq1. 
by move=> ->; apply: (reflexivity_e er); apply: rep_i_sr.
Qed.

Lemma related_equiv_P  u v:
  related r u v <->
   [/\ inc u (substrate r), inc v (substrate r) & class r u = class r v].
Proof.
split.
  by move=> ruv; split; [substr_tac | substr_tac| apply: class_eq1].
move=> [us vs cuv]. 
apply /class_P; rewrite cuv; by apply: inc_itself_class.
Qed.

Lemma is_class_pr x y:
  inc x y -> inc y (quotient r) -> y = class r x.
Proof. 
move=> xy yq.
have <-: class r (rep y) = y by apply: class_rep.
apply: class_eq1=>// ; apply: (related_rep_in_class  yq xy).
Qed.

End Class.

Hint Resolve rep_i_sr inc_itself_class inc_class_setQ : fprops.


(** Canonical projection on the quotient *)

Definition canon_proj r := Lf (class r) (substrate r) (quotient r).

Section CanonProj.
Variable (r:Set).
Hypothesis (er: equivalence r).

Lemma canon_proj_f : function (canon_proj r).
Proof. apply: lf_function => t ts /=; fprops. Qed.

Lemma canon_proj_s : source (canon_proj r) = substrate r.
Proof. by rewrite /canon_proj; aw. Qed.

Lemma canon_proj_t : target (canon_proj r) = quotient r.
Proof. by rewrite /canon_proj; aw. Qed.

Hint Rewrite canon_proj_s canon_proj_t: aw.
Hint Resolve canon_proj_f: fprops.

Lemma canon_proj_V x:
  inc x (substrate r) -> Vf (canon_proj r) x = class r x.
Proof. move => sr ;rewrite LfV // => t ts /=; fprops.  Qed.



Lemma canon_proj_setQ_i  x:
  inc x (substrate r) -> inc (Vf (canon_proj r) x) (quotient r).
Proof. move=> xs; rewrite canon_proj_V //; fprops. Qed.

Lemma rel_gcp_P  x y:
  inc x (substrate r) -> inc y (quotient r) ->
  (inc (J x y) (graph (canon_proj r)) <-> inc x y).
Proof. 
move=> xs yq.
have fc: (function (canon_proj r)) by fprops. 
split => h.
move: (Vf_pr fc h). rewrite canon_proj_V //.
  move => ->; apply/class_P => //; equiv_tac.
have: (y = Vf (canon_proj r) x).
  rewrite (canon_proj_V xs).
   move: (class_rep er yq) h => <- /(class_P er) rryx.
  by apply: class_eq1.
by move=> ->; Wtac; aw.
Qed.

Lemma canon_proj_fs: surjection (canon_proj r).
Proof. 
split;[ fprops | move=> y; aw => yr; exists (rep y); fprops].
by rewrite (canon_proj_V (rep_i_sr er yr)) (class_rep er yr).
Qed.


Lemma sub_im_canon_proj_quotient a x:
  sub a (substrate r) ->
  inc x (Vfs (canon_proj r) a) ->
  inc x (quotient r).
Proof. 
move=> sas xi.
have fc:function (canon_proj r) by fprops. 
have sa: sub a (source (canon_proj r)) by aw.
move /(Vf_image_P fc sa): xi => [u ua ->]; rewrite (canon_proj_V); fprops.
Qed.


(** Criterion 55 of Bourbaki*)

Lemma related_e_P u v:
  related r u v <->
   [/\ inc u (source (canon_proj r)),
     inc v (source (canon_proj r)) & 
     Vf (canon_proj r) u = Vf (canon_proj r) v].
Proof. 
rewrite canon_proj_s; split.
  by move/(related_equiv_P er)=> [us vs cuv]; split=> //; rewrite !canon_proj_V.
move => [us vs h]; apply/(related_equiv_P er); split => //; move: h.
by rewrite !canon_proj_V.
Qed.

End CanonProj.

Hint Rewrite canon_proj_s canon_proj_t: aw.
Hint Resolve canon_proj_f: fprops.

(** The diagonal is the graph of equality *)

Lemma diagonal_class x u:
  inc u x -> class (diagonal x) u = singleton u.
Proof.
have h:= (proj1 (diagonal_equivalence x)).
move=> ux; apply: set1_pr; first by apply/(class_P h) /diagonal_pi_P.
by move => z /(class_P h) /diagonal_pi_P [_ ->].
Qed.
 
Lemma canon_proj_diagonal_fb x:
  bijection (canon_proj (diagonal x)).
Proof. 
have [h sr] :=(diagonal_equivalence x).
have cps:= (canon_proj_fs h).
split => //; split;first by fct_tac.
aw; move=> a b ax bx /=. rewrite !canon_proj_V //.
move: ax bx;rewrite sr => ax bx.
rewrite ! diagonal_class //; apply:set1_inj.
Qed.

Lemma canon_proj_diagonal_fb_contra r:
  equivalence r ->  bijection (canon_proj r) -> 
  r = diagonal (substrate r).
Proof.
move => pa pb.
set_extens t; last first.
 by move /diagonal_i_P => [Px px qx]; rewrite -Px -qx; apply: reflexivity_e.
move => tr; move: (pa) => [sa _ _ _]; move: (sa _ tr) => pt.
have ptsr: inc (P t) (substrate r) by substr_tac.
have qtsr: inc (Q t) (substrate r) by substr_tac.
apply /diagonal_i_P; split => //.
move: (bij_inj pb); rewrite canon_proj_s => h; move: (h _ _  ptsr qtsr).
rewrite !canon_proj_V //.
by apply; apply: class_eq1 => //;rewrite /related pt.
Qed.

(** Relation associated to [P] in a product *)

Definition first_proj_eqr x y :=
  eq_rel_associated (first_proj (x \times  y)).

Definition first_proj_eq x y :=
  equivalence_associated (first_proj (x \times y)).

Lemma first_proj_equivalence x y:
  equivalence_on (first_proj_eq x y) (x \times y).
Proof. 
by move:(graph_ea_equivalence (first_proj_f (x\times y))); rewrite lf_source.
Qed.

Lemma first_proj_eq_related_P x y a b:
  related (first_proj_eq x y) a b <->
  [/\ inc a (x \times y), inc b (x \times y) & P a = P b].
Proof.
have ff: function (first_proj (x \times y)) by apply:first_proj_f.
split.
  move/(ea_relatedP ff); rewrite lf_source; move => [pa pb].
  by rewrite ! first_proj_V.
by move => [pa pb pc]; apply/(ea_relatedP ff);rewrite lf_source !first_proj_V.
Qed.

Lemma first_proj_classP x y:  nonempty y -> forall z,
  (classp (first_proj_eq x y) z <->
  exists2 u, inc u x & z = (singleton u) \times y).
Proof. 
move=> [y0 y0y].
case:(first_proj_equivalence x y).
set (r:=first_proj_eq x y) => er sr.
move => z; split.
  move => cz; move: (proj1 cz); rewrite sr; move /setX_P  => [sa sb sc].
  exists (P (rep z)) => //.
  set_extens t => ta.
     move: (rel_in_class er cz ta) => /first_proj_eq_related_P [qa qb qc].
     by move /setX_P: qb => [rq rb rc]; apply /indexedrP.
  rewrite (proj2 cz); apply /(class_P er); apply /first_proj_eq_related_P.
  move/indexedrP: ta => [pa pb pc]; split => //; apply /setX_P; split => //; ue.
move=> [u uz zp]; rewrite zp.
have nep: (nonempty (singleton u \times y)). 
  by exists (J u y0); apply: setXp_i; fprops.
move: (rep_i nep); set w:= rep _ => pa.
move /indexedrP: (pa) => [ra rb rc].
have wp: inc w (x \times y) by apply /setX_P;split => //; ue.
hnf; rewrite - /w; split; first by ue.
set_extens t.
  move /indexedrP => [sa sb sc]; apply /(class_P er).
  by apply /first_proj_eq_related_P;split; [exact | apply /setX_P |];rewrite sb.
move /(class_P er) =>  /first_proj_eq_related_P [_ /setX_P [qa qb qc] qd].
apply /indexedrP;split => //; ue.
Qed.


Lemma first_proj_equiv_proj x y:
  nonempty y->
  bijection (Lf (fun u => (singleton u) \times y)
    x (quotient (first_proj_eq x y))).
Proof. 
move=> ney.
set (f:=fun u => (singleton u) \times y).
set (g:= (Lf f x (quotient (first_proj_eq x y)))).
have efp:=(proj1 (first_proj_equivalence x y)).
have ta: lf_axiom f x (quotient (first_proj_eq x y)).
  move => u ux ; apply /(setQ_P efp) /(first_proj_classP _  ney); ex_tac.
rewrite /g; apply: lf_bijective => //.
  rewrite /f => u v ux vx sp. 
  apply: set1_inj; rewrite - (setX_domain (singleton u) ney). 
  by rewrite sp setX_domain.
move=>z /(setQ_P efp) /(first_proj_classP _ ney) [u ux ep]; ex_tac.
Qed.

Lemma sub_quotient_powerset r:
  equivalence r ->
  sub (quotient r) (\Po (substrate r)).
Proof.
by move=> er x /(setQ_P er) => cr; apply /setP_P; apply: sub_class_sr.
Qed.

Lemma partition_from_equivalence r:
  equivalence r ->
  partition_s (quotient r)(substrate r).
Proof. 
move=> er.
split; last by move=> t tq; apply: (setQ_ne er tq).
split; first by apply: setU_setQ.
by move=> a b /(setQ_P er) ca /(setQ_P er) cd;apply: (class_dichot er).
Qed.

(** Partition of a set and induced equivalence *)

Definition in_same_coset f x y:=
   exists i, [/\ inc i (source f) , inc x (Vf f i) & inc y (Vf f i)].

Definition partition_relation f x := 
  graph_on (in_same_coset f) x.

Section InSameCoset.
Variables (f x: Set).
Hypothesis (ff: function f).
Hypothesis fpa:  partition_w_fam (graph f) x. 

Lemma partition_inc_unique1 i j y:
  inc i (source f) -> inc y (Vf f i) ->
  inc j (source f) -> inc y (Vf f j) -> i = j.
Proof.
rewrite (proj33 ff) => p1 p2 p3 p4.
by rewrite -(cover_at_pr fpa p1 p2) - (cover_at_pr fpa p3 p4).
Qed.

Lemma isc_hi a b: (in_same_coset f a b) -> (inc a x /\ inc b x).
Proof.
move => [t [tsf p1 p2]]; rewrite (proj33 ff) in tsf.
rewrite -(proj33 fpa); split; union_tac.
Qed.

Lemma isc_rel_P a b:
  (related (partition_relation f x) a b <-> in_same_coset f a b).
Proof. 
move: fpa => [qa qb qc].
split; first by move /graph_on_P1 => [_ _].
by move => h; move: (isc_hi h) => [ax bx]; apply /graph_on_P1.
Qed.

Lemma isc_rel1P a b: inc a x -> inc b x ->
   ((in_same_coset f a b) <-> (cover_at (graph f) a = cover_at (graph f) b)).
Proof.
move => ax bx; split.
  move => [t [tsf pa pb]].
  rewrite (proj33 ff) in tsf.
  by rewrite(cover_at_pr fpa tsf pa) (cover_at_pr fpa tsf pb).
move => h. 
move: (cover_at_in fpa ax) (cover_at_in fpa bx); rewrite -h - (proj33 ff).
set s := (cover_at (graph f) a); move => [pa pb] [pc pd].
by exists s.
Qed.

Lemma isc_rel_sr: substrate (partition_relation f x) =  x.
Proof. by apply: graph_on_sr => a ax; apply /isc_rel1P. Qed.

Lemma isc_rel_equivalence:
  equivalence (partition_relation f x).
Proof. 
apply: equivalence_from_rel; split.
  by move => u v [i [isf Wx Wy]]; exists i.
move => b a c pa pb.
move: (isc_hi pa) (isc_hi pb) => [ax bx] [_ cx].
apply/(isc_rel1P ax cx). 
by move /(isc_rel1P ax bx): pa => ->; move /(isc_rel1P bx cx): pb => ->.
Qed.

Lemma isc_rel_class a:
  classp (partition_relation f x) a ->
  exists2 u, inc u (source f) & a = Vf f u.
Proof.
move=> [rs ac].
move: isc_rel_equivalence => ec.
rewrite isc_rel_sr in rs.
move: (cover_at_in fpa rs); set u := cover_at _ _;move => [pa pb].
rewrite ac /Vf (proj33 ff); ex_tac.
set_extens t. 
   move /(class_P ec) /isc_rel_P => h; move: (proj2 (isc_hi h)) => tx.
   by move: (cover_at_in fpa tx)=> []; move /(isc_rel1P rs tx): h => <-.
move => ts.
have tx: inc t x by rewrite - (proj33 fpa); union_tac.
apply /(class_P ec) /isc_rel_P /(isc_rel1P rs tx).
by symmetry; apply:(same_cover_at fpa rs ts). 
Qed.

Lemma isc_rel_class2 u:
  inc u (source f) -> nonempty (Vf f u) ->
  classp (partition_relation f x)  (Vf f u) .
Proof. 
move=> us neW.
move: isc_rel_equivalence => ec.
rewrite (proj33 ff) in us.
have sWx: (sub  (Vf f u) x) by rewrite -(proj33 fpa) => t tW; union_tac.
move: (rep_i neW) => rw;move: (sWx _ rw) => rs.
move:(cover_at_pr fpa us rw) => pa.
hnf; rewrite  isc_rel_sr //; split=> //.
set_extens t.
  move => ts.
  have tx: inc t x by rewrite - (proj33 fpa); union_tac.
  apply /(class_P ec) /isc_rel_P /(isc_rel1P rs tx).
  by symmetry; apply:(same_cover_at fpa rs);rewrite pa.
move /(class_P ec) /isc_rel_P => h; move: (proj2 (isc_hi h)) => tx.
rewrite -pa; move: (proj1 (cover_at_in fpa tx)).
by move /(isc_rel1P rs tx): h => ->.
Qed.

Lemma partition_fun_fb:
  (allf (graph f) nonempty) ->
  bijection (Lf (Vf f)  (source f) (quotient (partition_relation f x))).
Proof. 
move: isc_rel_equivalence => er.
rewrite /allf - (proj33 ff); move=> alne; apply: lf_bijective.
- move=> t tf; apply/(setQ_P er). 
  apply: isc_rel_class2 =>//; apply: (alne _ tf). 
- move=> u v us vs sW.
  move: (alne _ us)=> [y yu]; have yv: (inc y (Vf f v)) by rewrite - sW.
  by apply: (partition_inc_unique1 us yu vs yv).
- move=> y; move/(setQ_P er) => ic.
  move: (isc_rel_class ic) => [u us] ->; ex_tac.
Qed.

End InSameCoset.

(** A system of representatives for the partition f of x as a set f 
   or a function g *)

Definition representative_system s f x :=
  [/\ function f, partition_w_fam (graph f) x, sub s x 
  & forall i, inc i (source f) -> singletonp ((Vf f i) \cap s)].

Definition representative_system_function g f x :=
  injection g /\ (representative_system (Imf g) f x).

Lemma rep_sys_function_pr g f x i:
  representative_system_function g f x -> inc i (source f) ->
  exists! a, (inc a (source g) /\ inc (Vf g a) (Vf f i)).
Proof. 
move=> [[fg ig] [ff pf gg  alsi]] ins.
move: (alsi _ ins) => [u isu].
apply /unique_existence; split.
  move: (set1_1 u). 
  rewrite - isu; move /setI2_P => [pa] /(Imf_P fg) [a asg pb]. 
  by exists a; rewrite - pb.
move=> a b [asg Wa][bsg Wb]; apply: ig => //.
have aux: (forall a, inc a (source g) -> inc (Vf g a) (Vf f i) -> Vf g a = u).
  move=> c csg Wc.
  apply: set1_eq; rewrite -isu; apply: setI2_i => //; Wtac.
rewrite aux // aux //.
Qed.

Lemma rep_sys_function_pr2 g f x:
  injection g -> function f -> partition_w_fam (graph f) x ->
  sub (target g) x  ->
  (forall i, inc i (source f) ->
      exists! a, (inc a (source g) /\ inc (Vf g a) (Vf f i))) ->
  representative_system_function g f x.
Proof.
move=> ig ff pf stx exu; move:(ig)=> [fg _].
split =>//; split=>//; first by apply:(sub_trans (Imf_Starget fg) stx).
move=> i isf; move: (exu _ isf) => [a [[asg Wa] un]].
exists (Vf g a); set_extens t.
  move/setI2_P => [tv /(Imf_P fg) [z zsg eq]]; apply/set1_P. 
  by rewrite eq;congr (Vf g _); symmetry;apply: un;rewrite - eq.
move /set1_P => ->; apply/setI2_P; split => //; Wtac.
Qed.

Lemma section_canon_proj_pr g f x y r:
  r = partition_relation f x ->  function f -> partition_w_fam (graph f) x ->
  is_right_inverse (canon_proj r) g ->
  inc y x ->
  related r y (Vf g (class r y)).
Proof. 
move=> pr ff pf ri yx.
have eq: equivalence r by rewrite pr; apply: isc_rel_equivalence.
have sr: substrate r = x by rewrite pr isc_rel_sr //. 
rewrite - sr in yx.
have cyq: inc (class r y) (quotient r) by fprops.
have sg: source g = target (canon_proj r) by apply: right_i_source.
move: sg; aw => sg; rewrite - sg in cyq.
have yri: inc y (class r y) by apply: inc_itself_class => //.
apply: (symmetricity_e eq).
apply /(class_P eq).
have <- //: (class r y) = class r (Vf g (class r y)).
have [pa pb] := ri.
set t := (class r y).
have Wcs: inc (Vf g t) (substrate r) by move: pa=> [_ fg]; aw; move=>->; Wtac.
move: (compfV pa cyq). rewrite pb idV // ? canon_proj_V //; aw; ue.
Qed.

Lemma section_is_representative_system_function g f x:
  function f -> partition_w_fam (graph f) x ->
  is_right_inverse  (canon_proj (partition_relation f x)) g ->
  (forall u, inc u (source f) -> nonempty (Vf f u)) ->
  representative_system_function g f x.
Proof. 
move=> ff pf ti alne.
have ig: injection g by apply: (right_inverse_fi ti). 
apply: rep_sys_function_pr2=>//.  
  rewrite - (proj33 (proj1 ti)) canon_proj_s isc_rel_sr; fprops.
move=> i isf.
set (r:=partition_relation f x) in *.
have sf: domain (graph f) =source f by apply: domain_fg. 
have er: equivalence r by rewrite /r; apply: isc_rel_equivalence.
have sr: substrate r = x by rewrite /r isc_rel_sr.
rewrite (right_i_source ti); aw.
apply /unique_existence;split.
  set z:= (rep (Vf f i)).
  have zW: inc z (Vf f i) by rewrite /z; apply: rep_i; apply: alne.
  have zx: inc z x by move: pf=>[_ md <-];  rewrite - sf in isf; union_tac. 
  exists (class r z); split. 
    aw; rewrite - sr in zx; fprops. 
  move: (section_canon_proj_pr (refl_equal r) ff pf ti zx).
  move /(isc_rel_P ff pf) => [ u [usf zW' qW]]. 
  by rewrite (partition_inc_unique1 ff pf isf zW usf zW'). 
aw; move=> a b [atx Wa] [btx Wb].
have Wiq: inc (Vf f i) (quotient r).
  apply/(setQ_P er); apply (isc_rel_class2 ff pf isf); ex_tac.
have aux: (forall u, inc u (quotient r) -> inc (Vf g u) (Vf f i) -> Vf f i = u).
  move=> u /(setQ_P er) [rs eq] iWW; rewrite sr in rs.
  rewrite eq; apply: is_class_pr=> //.
  move: (section_canon_proj_pr (refl_equal r) ff pf ti rs).
  rewrite - eq; move /(isc_rel_P ff pf) => [v [usf zW' qW]].
  by rewrite (partition_inc_unique1 ff pf isf iWW usf qW). 
by rewrite -(aux _ atx Wa) (aux _ btx Wb).
Qed.


(** ** EII-6-3 Relations compatible with an equivalence relation *)

(** A relation is compoatible if the set of objects satisfying the relation is a union of classes *)

Definition compatible_with_equiv_p (p: property) (r:Set) :=
  forall x x', p x -> related r x x' -> p x'.

Lemma trivial_equiv p x:
  compatible_with_equiv_p p (diagonal x).
Proof. by move=> u v pa /diagonal_pi_P [_] <-. Qed.

(** A compatible relation induces a relation on the quotient *)

Definition relation_on_quotient p r :=
  fun t => inc t (quotient r) /\ exists2 x, inc x t & p x.

Lemma rel_on_quoP p r:
  equivalence r -> compatible_with_equiv_p p r -> forall t,
  (relation_on_quotient p r t <-> 
     (inc t (quotient r) /\  forall x, inc x t -> p x)).
Proof. 
move=> er co t; split.
  move=> [tq [x xt px]]; split=>// u ut; apply: (co _  _ px).  
  by move: tq => /(setQ_P er) h; apply /(in_class_relatedP er); exists t.
move => [tq xtpx];move: (setQ_ne er tq) => /rep_i net.
split =>//; ex_tac.
Qed.

Lemma rel_on_quoP2 p r:
  equivalence r -> compatible_with_equiv_p p r -> forall y,
  ( (inc y (substrate r) /\ relation_on_quotient p r (Vf (canon_proj r) y)) <->
    (inc y (substrate r) /\ p y)).
Proof.
move=> er co; split; move => [ysr]; rewrite (canon_proj_V ysr).
  move => [tq [x xt px]]. 
  have yx: related r x y by move : xt; move /(class_P er) => h; equiv_tac. 
  by split =>//; apply: (co _ _  px yx).
move => py;split =>//; split; fprops.
move:(inc_itself_class er ysr) => h; ex_tac.
Qed.

(** ** EII-6-4 saturated subsets *)

(** A set is satured if it is a union of classes*)

Definition saturated r x  := compatible_with_equiv_p (fun y=> inc y x) r.


(** If f is the canonical projection this defines that smallest saturated set that contains x*)

Definition inverse_direct_value f x :=
  Vfs (inverse_fun f) (Vfs f x).

Lemma idvalue_P f x: function f -> sub x (source f) ->forall y,
  inc y (inverse_direct_value f x) <-> 
    (inc y (source f) /\  (exists2 z, inc z x & Vf f y = Vf f z)).
Proof.
move => ff sxf.
split.
  move /dirim_P => [u]; aw; move /dirim_P => [z zx pa] /igraph_pP pb.
  split; [Wtac | by ex_tac; rewrite - (Vf_pr ff pa) - (Vf_pr ff pb) ].
move => [ysf [z zx  pa]].
apply/dirim_P; exists (Vf f z).
   apply/dirim_P;ex_tac; Wtac.  
aw; apply/igraph_pP; rewrite -pa; Wtac.
Qed.

Lemma idvalue_cprojP r x: 
  equivalence r -> sub x (substrate r) ->forall y,
  inc y (inverse_direct_value (canon_proj r) x) <-> 
    (inc y (substrate r) /\ (exists2 z, inc z x & class r y = class r z)).
Proof.
have ff:= (canon_proj_f r).
move => pa pb; move: (pb); rewrite - canon_proj_s => pc y.
split.
  move/(idvalue_P ff pc) => [qa [v qb vx]]; split; first by exact.
  have ysr: inc y (substrate r) by rewrite - canon_proj_s.
  by ex_tac; move: vx; rewrite !canon_proj_V  //;apply: pb.
move => [qa [v qb qc]]; apply/(idvalue_P ff pc).
have vsr: inc v (substrate r) by apply: pb.
have ysr: inc y (substrate r) by move: qa; aw.
by split => //;ex_tac;  rewrite !canon_proj_V.
Qed.

Lemma saturatedP r x:
  equivalence r -> sub x (substrate r) ->
  ((saturated r x) <-> (forall y, inc y x -> sub (class r y) x)).
Proof. 
move=> er sxs; split.
  move=> sr y yx t; move/(class_P er); apply: (sr _ _  yx). 
by move=> yw u v ux ruv; apply: (yw _ ux); apply/(class_P er).
Qed.

Lemma saturated2P r x:
  equivalence r -> sub x (substrate r) ->
  ((saturated r x) <->
      exists2 y, (forall z, inc z y -> classp r z) & x = union y).
Proof. 
move => er sxs; move: (saturatedP er sxs) => aux;split.
  move => srx.
  exists (Zo (\Po x)(fun z => exists2 a, inc a x & z = class r a)).
    move=> z /Zo_P [] /setP_P zx [a ax ->]. 
    by apply: class_class =>//; apply: sxs.
  set_extens t => ts. 
    apply: (@setU_i _ (class r t)). 
      by move: (sxs _ ts)=>h; apply/(class_P er);equiv_tac.
    apply: Zo_i; [ by apply/setP_P;move /aux: srx; apply | ex_tac].
  by move /setU_P: ts => [y ty /Zo_P [] /setP_P yx [a ax yc]]; apply: yx.
move => [y yp xu]; apply/aux; rewrite xu => z zu.
move: (setU_hi zu) =>[t zt ty]; move: (yp _ ty) => ct.
move => u /(class_P er) rz; apply:(setU_i _ ty).
have pa := (rel_in_class er ct zt).
rewrite (proj2 (yp _ ty)); apply /(class_P er); equiv_tac. 
Qed.


Lemma class_is_inv_direct_value r x:
  equivalence r -> inc x (substrate r) ->
  class r x = inverse_direct_value (canon_proj r) (singleton x).
Proof.
move=> er xs.
move: (set1_sub xs) => xs1.
set_extens t => ts.
  apply/(idvalue_cprojP er xs1); split.
    exact: (sub_class_substrate er ts).
  exists x; fprops; exact :(class_eq2 er ts).
move/(idvalue_cprojP er xs1): ts => [v [pa /set1_P <- <-]]; fprops.
Qed.

Lemma saturated_P3 r x:
  equivalence r -> sub x (substrate r) ->
  (saturated r x <-> (x= inverse_direct_value (canon_proj r) x)).
Proof. 
move=> er xs.
set (p:=canon_proj r). 
have fp: function p by rewrite /p; fprops.
split => h.
  apply: extensionality.  
    by apply: inverse_direct_image =>//; rewrite /p; aw.
  move => y /(idvalue_cprojP er xs) [z [pa pb pc]].
  move /(saturatedP er xs): h => q; move: (q _ pb); rewrite -pc.
  apply; fprops.
apply/(saturatedP er xs); rewrite {2} h => y yx t tc.
apply /(idvalue_cprojP er xs); split.
  exact: (sub_class_substrate  er tc).
ex_tac;exact:(class_eq2 er tc).
Qed.

Lemma saturated_P4 r x:
  equivalence r -> sub x (substrate r) ->
  (saturated r x <-> (exists2 b, sub b (quotient r) 
    & x = Vfs (inverse_fun (canon_proj r)) b)).
Proof.
move=> er xs.
have qr: quotient r = target (canon_proj r) by aw.
have sj := (canon_proj_fs er).
split. 
  move/(saturated_P3 er xs) => hyp. 
  exists (Vfs (canon_proj r) x) =>//.
  rewrite qr;apply: sub_trans (f_range_graph (proj1 sj)); apply: dirim_Sr. 
move=> [b bq xeq].
apply/(saturated_P3 er xs).
rewrite qr in bq; move: (direct_inv_im_surjective sj bq).
by rewrite /inverse_direct_value -xeq => ->.
Qed.

(** Links between saturation and union, intersection, complement *)

Lemma saturated_setU r x:
  equivalence r ->
  (alls x (sub^~ (substrate r))) -> (alls x (saturated r)) ->
  (sub (union x) (substrate r) /\  saturated r (union x)).
Proof. 
move=> er als alsa.
have r1: (sub (union x) (substrate r)).
  by move => t /setU_P [z tz zx]; apply: (als _ zx).
split=>//;apply /saturatedP => // y /setU_P [z yz zx]. 
apply: sub_trans (setU_s1 zx).
by move: (alsa _ zx)  => /(saturatedP er (als _ zx)); apply.
Qed.

Lemma saturated_setI r x:
  equivalence r -> nonempty x ->
  (alls x (sub^~ (substrate r))) -> (alls x (saturated r)) ->
  (sub (intersection x) (substrate r) /\  saturated r (intersection x)).
Proof. 
move=> er nex als alsa.
have aux: (sub (intersection x) (substrate r)). 
  by move: nex => [y yx]; apply: sub_trans (als _ yx); apply: setI_s1.
split =>//; apply /(saturatedP er aux) => y yi t tc; apply: (setI_i nex). 
move=> z zx; move:(alsa _ zx). 
move /(saturatedP er (als _ zx))=> s; apply: (s _ (setI_hi yi zx) _ tc). 
Qed.

Lemma saturated_setC r a:
  equivalence r -> sub a (substrate r) -> saturated r a -> 
  saturated r ((substrate r) -s a).
Proof. 
move=> er ar.
move /(saturated_P4 er ar) => [b sq aib].
apply /(saturated_P4 er);first by apply: sub_setC.
exists ((quotient r) -s b); first by apply: sub_setC.
move: (iim_fun_C b (canon_proj_f r)). 
by rewrite aib iim_fun_pr canon_proj_s canon_proj_t. 
Qed.

Definition saturation_of r x :=
  inverse_direct_value (canon_proj r) x.

Lemma saturation_of_pr r x:
  equivalence r -> sub x (substrate r) ->
  saturation_of r x =
  union (Zo (quotient r)(fun z=> exists2 i, inc i x & z = class r i)).
Proof. 
move=> er sr.
have fc: function (canon_proj r) by fprops.
rewrite /saturation_of/inverse_direct_value. 
set_extens y.
  move /(idvalue_cprojP er sr) => [v [pa pb pc]].
  apply: (@setU_i  _ (class r y)); fprops; apply: Zo_i; fprops.
  by ex_tac; rewrite pd.
move /setU_P => [z zy/Zo_P [zq [i ix sc]]].
move: zy; rewrite sc; move/(class_P er) => pc.
apply/(idvalue_cprojP er sr); split;first by substr_tac.
ex_tac;symmetry;by apply:class_eq1.
Qed.


Lemma saturation_of_smallest r x:
  equivalence r -> sub x (substrate r) ->
  [/\ saturated r (saturation_of r x),
    sub x (saturation_of r x) 
    & (forall y, sub y (substrate r) -> saturated r y -> sub x y
      -> sub (saturation_of r x) y)].
Proof.
move=> er xsr.
have fc: function (canon_proj r) by fprops.
split.
- apply /(saturated_P4 er). 
    by move => t /(idvalue_cprojP er xsr) [pa _].
  exists (Vfs (canon_proj r) x) => //.
  rewrite - canon_proj_t.
  apply: sub_trans (f_range_graph fc); apply: dirim_Sr.
- move => t tx; apply/(idvalue_cprojP er xsr); split; [by apply: xsr| ex_tac].
- move=> y ys sy sxy t.
  move /(idvalue_cprojP er xsr) => [tsr [z tx sc]].
  move /(saturated_P3 er ys): sy => ->.
  by apply/(idvalue_cprojP er ys); split => //; exists z => //; apply: sxy.
Qed.

Definition union_image x f:=
  union (Zo x (fun z=> exists2 i, inc i (source f) & z = Vf f i)).

Lemma saturation_of_union r f g:
  equivalence r -> function f -> function g ->
  (forall i, inc i (source f) -> sub (Vf f i) (substrate r)) ->
  source f = source g ->
  (forall i, inc i (source f) -> saturation_of r (Vf f i) = Vf g i)
  -> saturation_of r (union_image (\Po(substrate r)) f) = 
  union_image (\Po(substrate r)) g.
Proof.
move=> er ff fg als sfsg alsat.
have fc: function (canon_proj r) by fprops.
have U1sr: sub (union_image (\Po (substrate r)) f) (substrate r).
  by move => t /setU_P [z zt /Zo_P [/setP_P h _]]; apply: h.
set_extens x. 
  move/(idvalue_cprojP er U1sr) => [zu [z /setU_P [v zv]] /Zo_P []
     /setP_P vsr [i isf fi] sc].
  move:(als _ isf) => pa.
  apply/setU_P; exists (Vf g i); rewrite -(alsat _ isf).
    apply/(idvalue_cprojP er pa); split => //; exists z => //; ue.
  apply: Zo_i; first by apply/setP_P=> t /(idvalue_cprojP er pa) [ ok _].
  rewrite - sfsg; ex_tac.
move => /setU_P [z xz /Zo_P [/setP_P zr [i isr zv]]].
move: xz; rewrite - sfsg in isr; rewrite zv - (alsat _ isr).
move/(idvalue_cprojP er (als _ isr)) => [pa [t pb pc]].
apply/(idvalue_cprojP er U1sr); split => //; exists t => //.
apply /setU_P; exists (Vf f i) => //; apply:Zo_i; last by ex_tac.
by apply /setP_P; apply: als.
Qed.

(** ** EII-6-5 Mappings compatible with equivalence relations *)

(** The canonical projection is surjective, thus has a section *)

Definition section_canon_proj r :=
  Lf rep (quotient r) (substrate r).

Lemma section_canon_proj_axioms r:
  equivalence r ->
  lf_axiom rep (quotient r) (substrate r).
Proof. move=> er t ta; fprops. Qed.

Lemma section_canon_proj_V r x:
  equivalence r ->
  inc x (quotient r) -> Vf (section_canon_proj r) x = (rep x).
Proof.
by move=> er iq; rewrite LfV //; apply: section_canon_proj_axioms. 
Qed.

Lemma section_canon_proj_f r:
  equivalence r -> function (section_canon_proj r).
Proof. 
rewrite/section_canon_proj=> er. 
by apply: lf_function; apply: section_canon_proj_axioms.
Qed.

Lemma right_inv_canon_proj r:
  equivalence r ->
  is_right_inverse (canon_proj r) (section_canon_proj r).
Proof. 
move=> er.
have ss: source (section_canon_proj r) = quotient r.
  by rewrite/section_canon_proj; aw.
have fs: function (section_canon_proj r) by apply: section_canon_proj_f.
have fc: function (canon_proj r) by fprops.
have cpo: (canon_proj r) \coP (section_canon_proj r).
  by split => //; rewrite/ section_canon_proj; aw.
split=> //.
apply: function_exten; try fct_tac; aww.
rewrite ss=> x xs.  
have ro:  inc (rep x) (substrate r) by apply: rep_i_sr.
rewrite compfV // ? ss // section_canon_proj_V // idV // canon_proj_V //.
by apply: class_rep.
Qed.

(** A mapping is compatible with an equivalence if it is constant on classes; 
   it is compatible with two equivalences is the image of a class is a 
   subset of a class *)

Definition compatible_with_equiv f r :=
  [/\ function f, source f = substrate r &
  forall x x', related r x x' -> Vf f x = Vf f x'].

Definition compatible_with_equivs f r r' :=
  [/\ function f, target f =  substrate r' &
  compatible_with_equiv ((canon_proj r') \co f) r].

(* This is the definition of Bourbaki *)

Lemma compatible_with_equiv_pr f r:
  function f -> source f = substrate r  ->
  (compatible_with_equiv f r <->
    (forall y, compatible_with_equiv_p (fun x => y = Vf f x) r)).
Proof. 
move=> ff sf; rewrite/compatible_with_equiv/compatible_with_equiv_p. 
split.
  by move=> [_ _ hyp] y x x' => ->; apply: hyp.
by move=> hyp; split => // x x'; apply: (hyp (Vf f x) x x'). 
Qed.

Lemma compatible_constant_on_classes f r x y:
  equivalence r ->
  compatible_with_equiv f r -> inc y (class r x) -> Vf f x = Vf f y.
Proof. 
by move=> eq [ff sf hyp] yc; apply: hyp; move/(class_P eq): yc.
Qed.

Lemma compatible_constant_on_classes2 f r x:
  equivalence r -> compatible_with_equiv f r -> 
  constantfp (restriction f (class r x)).
Proof.
move=> re [ff sf hyp].
have scs: sub (class r x) (substrate r) by apply: sub_class_substrate.
rewrite - sf in scs.
split; first by apply: (proj31 (restriction_prop ff scs)).
have sr: source (restriction f (class r x)) = class r x.
  by rewrite /restriction; aw.
rewrite sr.  
move=> a b ac bc /=; rewrite ! restriction_V //; apply: hyp.
move: ac bc => /(class_P re) ac /(class_P re) bc; equiv_tac.
Qed.

Lemma compatible_with_proj f r x y:
  equivalence r -> compatible_with_equiv f r -> 
  inc x (substrate r) -> inc y (substrate r) -> 
  Vf (canon_proj r) x = Vf (canon_proj r) y -> Vf f x = Vf f y.
Proof. 
move=> er cgt xs ys; rewrite !canon_proj_V // => sx.
apply: (@compatible_constant_on_classes _ r) =>//; rewrite sx; fprops.
Qed.

Lemma compatible_with_pr r r' f x y:
  equivalence r ->  equivalence r' ->
  compatible_with_equivs f r r' -> 
  related r x y -> related r' (Vf f x) (Vf f y).
Proof. 
move=> er er'  [ff sf [fc sc hyp]] rxy.
have cc: ((canon_proj r') \coP f) by split; first (by fprops); aw.
move: sc; aw => sc.
have xs: inc x (source f) by rewrite sc; substr_tac.
have ys: inc y (source f) by rewrite sc; substr_tac.
have px: (inc (Vf f x) (substrate r')) by Wtac.
have py: (inc (Vf f y) (substrate r')) by Wtac.
move: (hyp _ _ rxy). rewrite ! compfV // !canon_proj_V // =>  sc1.
by apply/related_equiv_P.
Qed.

Lemma compatible_with_pr2 r r' f:
  equivalence r ->  equivalence r' ->
  function f ->
  target f = substrate r'-> source f = substrate r->
  (forall x y,  related r x y -> related r' (Vf f x) (Vf f y)) ->
  compatible_with_equivs f r r'.
Proof.
move=> er er' ff tf sf rr'.
have cc: (canon_proj r') \coP f by split; fprops; symmetry; aw.
split =>//; saw;first by fct_tac.
move=> x x' rxx'; move: (rr' _ _ rxx'); move /(related_equiv_P er').
move => [Ws Ws' cxx'].
rewrite ! compfV // ? canon_proj_V // sf; substr_tac.  
Qed.

Lemma compatible_with_proj3  r r' f x y:
  equivalence r -> equivalence r' -> 
  compatible_with_equivs f r r'->
  inc x (substrate r) -> inc y (substrate r) ->
  Vf (canon_proj r) x = Vf (canon_proj r) y -> 
  class r' (Vf f x) = class r' (Vf f y).
Proof.
move=> er er' co xs ys; rewrite !canon_proj_V // => sc.
apply: class_eq1 =>//; apply: (compatible_with_pr er er' co).
by apply /(related_equiv_P er). 
Qed. 

(** A compatible mapping induces a mapping on the quotient *)

Definition fun_on_quotient r f :=
  f \co (section_canon_proj r).

Lemma exists_fun_on_quotient f r:
  equivalence r -> function f -> source f = substrate r ->
  (compatible_with_equiv f r <->
  (exists h, h \coP (canon_proj r) /\ h \co (canon_proj r) = f)).
Proof.
move=> er ff sf.
rewrite exists_left_composable; aw => //; last by apply: canon_proj_fs.
split. 
  by move => co x y xs ys sW; apply: (compatible_with_proj er co xs ys sW). 
move=> hyp; split=>//.
move=> x x' /(related_equiv_P er)  [xs ys cc];apply: hyp => //.
by rewrite ! canon_proj_V.
Qed.

Lemma exists_unique_fun_on_quotient f r h:
  equivalence r -> compatible_with_equiv f r ->
  h \coP (canon_proj r) -> h \co (canon_proj r) = f ->
  h = fun_on_quotient r f.
Proof. 
move=> er cfr chc chcf; move: (cfr) => [ff sf1 _].
have sc: (surjection (canon_proj r)) by apply: canon_proj_fs.
have ri := (right_inv_canon_proj er).
have sf: source f = source (canon_proj r) by aw.
apply: (exists_left_composable_aux ff sf ri chc chcf).
Qed.

Lemma compose_foq_proj f r:
  equivalence r ->  compatible_with_equiv f r ->
  (fun_on_quotient r f) \co (canon_proj r) = f.
Proof.
move=> er co; move: (co)=> [ff sf hyp].
set (g:= canon_proj r). 
have sg: surjection g by rewrite/g; apply: canon_proj_fs.
have sfsg: source f = source g by rewrite /g; aw.
have sW: forall x y, inc x (source g) ->  inc y (source g) ->
     Vf g x = Vf g y -> Vf f x = Vf f y. 
  rewrite - sfsg sf; move=> x y xr yr h.
  by apply: (compatible_with_proj er co xr yr). 
apply: (left_composable_value ff sg sfsg sW (right_inv_canon_proj er) 
    (refl_equal (fun_on_quotient r f))).
Qed.

(** A mapping compatible with two relations induces a mapping on the two quotients *)

Definition fun_on_rep f: Set -> Set := fun x=> f(rep x).
Definition fun_on_reps r' f := fun x=> Vf (canon_proj r') (f(rep x)) .

Definition function_on_quotient r f b  :=
  Lf (fun_on_rep f)(quotient r)(b).

Definition function_on_quotients r r' f :=
  Lf (fun_on_reps r' f)(quotient r)(quotient r').

Definition fun_on_quotients r r' f :=
  ((canon_proj r') \co f) \co (section_canon_proj r).

Lemma foq_axioms r f b:
  equivalence r ->
  lf_axiom f (substrate r) b ->
  lf_axiom (fun_on_rep f) (quotient r) b.
Proof. move=> er h x xs;apply: h; fprops. Qed.

Lemma foqs_axioms r r' f:
  equivalence r ->
  equivalence r' ->
  lf_axiom f (substrate r)(substrate r') ->
  lf_axiom (fun_on_reps r' f) (quotient r) (quotient r').
Proof.
move => er er' h x xs. 
have w: (inc (rep x) (substrate r)) by fprops. 
rewrite /fun_on_reps canon_proj_V //; fprops.
Qed.

Lemma foqc_axioms r f:
  equivalence r ->
  function f -> source f = substrate r ->
  f \coP (section_canon_proj r).
Proof. 
move=> er ff sf. 
split =>//; first by apply: section_canon_proj_f. 
by rewrite /section_canon_proj; aw. 
Qed.

Lemma foqcs_axioms r r' f:
  equivalence r ->
  equivalence r' ->
  function f -> source f = substrate r -> target f = substrate r' ->
  (canon_proj r' \co f) \coP (section_canon_proj r).
Proof. 
move=> er er' ff sf tf.
have fc: (function (canon_proj r')) by fprops. 
split; first by fct_tac => //; symmetry; aw.
  by apply: section_canon_proj_f. 
by rewrite/section_canon_proj; aw.
Qed.

Lemma foq_f r f b:
  equivalence r ->
  lf_axiom f (substrate r) b ->
  function (function_on_quotient r f b).
Proof. 
by rewrite /function_on_quotient=> *; apply: lf_function; apply: foq_axioms.
Qed.

Lemma foqs_f r r' f:
  equivalence r ->
  equivalence r' ->
  lf_axiom f (substrate r)(substrate r') ->
  function (function_on_quotients r r' f).
Proof.
by rewrite /function_on_quotients=> *;apply: lf_function; apply: foqs_axioms.
Qed.

Lemma foqc_f r f:
  equivalence r -> function f ->
  source f = substrate r ->
  function (fun_on_quotient r f).
Proof. 
rewrite/fun_on_quotient=> er ff sf; fct_tac. 
  by apply: section_canon_proj_f.
by rewrite /section_canon_proj; aw.
Qed.

Lemma foqcs_f r r' f:
  equivalence r ->
  equivalence r' ->
  function f -> source f = substrate r -> target f = substrate r' ->
  function (fun_on_quotients r r' f).
Proof. 
rewrite/fun_on_quotients=> er er' ff sf tf.
by apply: compf_f; apply: foqcs_axioms.
Qed.

Lemma foq_V r f b x:
  equivalence r ->
  lf_axiom f (substrate r) b ->
  inc x (quotient r) ->
  Vf (function_on_quotient r f b) x = f (rep x).
Proof. 
by move => er ta xq; rewrite LfV //; apply: foq_axioms. 
Qed.

Lemma foqc_V r f x:
  equivalence r -> function f ->
  source f = substrate r -> inc x (quotient r) ->
  Vf (fun_on_quotient r f) x = Vf f (rep x).
Proof. 
move =>  er ff sf xq. rewrite  compfV //.
    by rewrite section_canon_proj_V. 
  by apply: foqc_axioms.
by rewrite /section_canon_proj; aw.
Qed.

Lemma foqs_V r r' f x:
  equivalence r ->
  equivalence r' ->
  lf_axiom f (substrate r)(substrate r') ->
  inc x (quotient r) ->
  Vf (function_on_quotients r r' f) x = class r' (f (rep x)).
Proof.
move => er er' ta xq. rewrite LfV//; last by  apply: foqs_axioms.
rewrite /fun_on_reps canon_proj_V //; apply: ta; fprops.
Qed.

Lemma foqcs_V r r' f x:
  equivalence r ->
  equivalence r' ->
  function f -> source f = substrate r -> target f = substrate r' ->
  inc x (quotient r) ->
  Vf (fun_on_quotients r r' f) x = class r' (Vf f (rep x)).
Proof. 
move=> er er' ff sf tf xq.
rewrite /fun_on_quotients. 
have fs: function(section_canon_proj r) by apply: section_canon_proj_f.
have ccf: (canon_proj r') \coP f by split; fprops; symmetry;aw.
have cc2: ( (canon_proj r') \co f) \coP (section_canon_proj r).
  by split; first (by fct_tac); rewrite /section_canon_proj; aw.
have Wt: inc (Vf (section_canon_proj r) x) (target (section_canon_proj r)).
  by Wtac; rewrite /section_canon_proj; aw.
have irs: inc (rep x) (source f) by ue.
rewrite compfV //; last by  rewrite/section_canon_proj; aw.
rewrite section_canon_proj_V // compfV // canon_proj_V //; Wtac.
Qed.

Lemma fun_on_quotient_pr r f x:
  Vf f x = fun_on_rep (fun _ => Vf f x) (Vf (canon_proj r)x).
Proof. done. Qed.

Lemma fun_on_quotient_pr2 r r' f x:
  Vf (canon_proj r')  (Vf f x) = 
  fun_on_reps r' (fun _ => Vf f x) (Vf (canon_proj r) x).
Proof. trivial. Qed.

Lemma composable_fun_proj r f b:
  equivalence r -> 
  lf_axiom f (substrate r) b ->
  (function_on_quotient r f b) \coP (canon_proj r).
Proof. 
move=> er ta. 
by split; [apply: foq_f | fprops | rewrite/function_on_quotient; aw ].
Qed.

Lemma composable_fun_projs r r' f:
  equivalence r -> 
  equivalence r' -> 
  lf_axiom f (substrate r) (substrate r') ->
  (function_on_quotients r r' f) \coP (canon_proj r).
Proof.
move=> er er' ta.
by split; [apply: foqs_f | fprops | rewrite/function_on_quotients; aw ].
Qed.

Lemma composable_fun_projc r f:
  equivalence r -> 
  compatible_with_equiv f r ->
  (fun_on_quotient r f) \coP (canon_proj r).
Proof. 
move=> er [ff sf h].
split; [ by apply: foqc_f | fprops | ].
by rewrite/fun_on_quotient/section_canon_proj; aw.
Qed.

Lemma composable_fun_projcs r r' f:
  equivalence r -> equivalence r' -> 
  compatible_with_equivs f r r'->
  (fun_on_quotients r r' f) \coP (canon_proj r).
Proof. 
move=> er er'  [ff sf [fg sg h]].
move: sg; aw => sg.
split; fprops;first by apply: foqcs_f.  
by rewrite/fun_on_quotients/section_canon_proj; aw.
Qed.


Lemma fun_on_quotient_pr3 r f x:
  equivalence r -> inc x (substrate r) ->  
  compatible_with_equiv f r ->
  Vf f x = Vf (fun_on_quotient r f) (Vf  (canon_proj r) x).
Proof. 
move=> er xs co; rewrite - compfV; last by aw.
  by rewrite compose_foq_proj. 
by apply: composable_fun_projc.
Qed.


(** Figure 3 (French version only) *)

Lemma fun_on_quotient_pr4 r r' f:
  equivalence r -> equivalence r' -> 
  compatible_with_equivs f r r'->
  (canon_proj r') \co f = (fun_on_quotients r r' f) \co (canon_proj r).
Proof. 
rewrite/fun_on_quotients; move=> er er' [ff sf h].
symmetry; apply: (compose_foq_proj er h).
Qed.

Lemma fun_on_quotient_pr5 r r' f x:
  equivalence r -> equivalence r' -> 
  compatible_with_equivs f r r'->
  inc x (substrate r) ->  
  Vf (canon_proj r') (Vf f x)  =
  Vf (fun_on_quotients r r' f) (Vf (canon_proj r) x). 
Proof. 
move => er er' co  xs.
move: (co)=> [ff sf [fg sg h]]; move: sg; rewrite compf_s => sg.
have cc: composable (canon_proj r') f by split; fprops;symmetry; aw.
rewrite - compfV //; try ue. 
rewrite - compfV //; last by aw.
  by rewrite -fun_on_quotient_pr4 //.
by apply: composable_fun_projcs=>//.
Qed.

Lemma compose_fun_proj_ev r f b x:
  equivalence r -> 
  compatible_with_equiv (Lf f (substrate r) b) r -> 
  inc x (substrate r) ->
  lf_axiom f (substrate r) b ->
  Vf (function_on_quotient r f b \co canon_proj r) x = f x.
Proof. 
move=> er co xr ta.
have cq: (inc (class r x) (quotient r)) by fprops.
have cop:= composable_fun_proj er ta.
have rrx: related r (rep (class r x)) x.
  by apply: symmetricity_e=>//; apply: related_rep_class=>//.
rewrite compfV // ? canon_proj_s // canon_proj_V // foq_V //.
move: (proj33 co _ _ rrx); rewrite ! LfV //; fprops.
Qed.

Lemma compose_fun_proj_ev2 r r' f x:
  equivalence r -> 
  equivalence r' -> 
  compatible_with_equivs (Lf f (substrate r) (substrate r')) r r' -> 
  lf_axiom f (substrate r) (substrate r') ->
  inc x (substrate r) ->
  inc (f x) (substrate r') ->
  Vf (canon_proj r') (f x)  =
  Vf (function_on_quotients r r' f \co canon_proj r) x.
Proof. 
move=> er er' co ta xs fxs.
have xsc: inc x (source (canon_proj r)) by aw.
rewrite canon_proj_V // compfV //; last by apply: composable_fun_projs.
set (y:= (Vf (canon_proj r) x)). 
have -> : (Vf (function_on_quotients r r' f) y
    = (Vf (fun_on_quotients r r' (Lf f (substrate r) (substrate r'))))y). 
  have ys: inc y (quotient r) by rewrite /y canon_proj_V; fprops.
  have h :=(rep_i_sr er ys).
  rewrite foqs_V // foqcs_V //; aw; trivial; try apply: lf_function => //.
  by rewrite LfV.
by rewrite - fun_on_quotient_pr5 // LfV // canon_proj_V //.
Qed.

Lemma compose_fun_proj_eq r f b:
  equivalence r -> 
  compatible_with_equiv (Lf f (substrate r) b) r -> 
  lf_axiom f (substrate r) b ->
  (function_on_quotient r f b) \co (canon_proj r) = 
    Lf f (substrate r) b.
Proof.
move=> er co ta.
apply: function_exten; try solve [ rewrite/function_on_quotient; aw; trivial].
- apply: compf_f; apply: composable_fun_proj=>//. 
  by apply: lf_function.  
- rewrite /function_on_quotient; aw =>x  xs.
  by rewrite compose_fun_proj_ev // LfV.
Qed.

Lemma compose_fun_proj_eq2 r r' f:
  equivalence r -> 
  equivalence r' -> 
  lf_axiom f (substrate r) (substrate r') ->
  compatible_with_equivs (Lf f (substrate r) (substrate r')) r r'->
  (function_on_quotients r r' f) \co (canon_proj r) = 
  (canon_proj r') \co (Lf f (substrate r) (substrate r')).
Proof.
move=> er er' ta co.
have ffoq:function (function_on_quotients r r' f) by apply: foqs_f.
have fa: function  (Lf f (substrate r) (substrate r')) by apply: lf_function.
have cn: (function_on_quotients r r' f) \coP (canon_proj r).
  by split; fprops; rewrite/function_on_quotients; aw.  
have cc: (canon_proj r') \coP (Lf f (substrate r) (substrate r')).
  by split; aww.
apply: function_exten; try fct_tac; aw; trivial .  
  by rewrite /function_on_quotients; aw. 
move => x xs.
have aux: (inc (f x) (substrate r')) by apply: ta.
rewrite -compose_fun_proj_ev2 // compfV //; aw;trivial.
by rewrite ! canon_proj_V // LfV.
Qed.

Lemma compatible_ea f:
  function f ->
  compatible_with_equiv f (equivalence_associated f).
Proof. 
move=>  ff.
have sr := proj2(graph_ea_equivalence ff).
by split=> // x x' /(ea_relatedP ff) [_ _]. 
Qed.

Lemma ea_foq_fi f:
  function f ->
  injection (fun_on_quotient (equivalence_associated f) f).
Proof. 
move=>  ff.
case:(graph_ea_equivalence ff).
set (g:= equivalence_associated f) => eg sf.
split; first by apply: foqc_f.
have: source (fun_on_quotient g f) = (quotient g)
  by rewrite/fun_on_quotient/section_canon_proj; aw. 
move => -> x y xq yq.
rewrite  foqc_V // foqc_V // => h. 
move: (rep_i_sr eg xq) (rep_i_sr eg yq) => xs ys. 
have: (related g (rep x) (rep y))  by  apply/(ea_relatedP ff);rewrite - sf.
by move/related_rr_P; apply.
Qed.

Lemma ea_foq_on_im_fb f:
  function f ->
  bijection (restriction2 (fun_on_quotient (equivalence_associated f) f)
    (quotient (equivalence_associated f)) (Imf f)).
Proof. 
move=> ff.
case:(graph_ea_equivalence ff).
set (g:= equivalence_associated f) => eg sfsg.
set (h:= fun_on_quotient g f).
have ih: injection h by rewrite /h/g; apply: ea_foq_fi. 
have fh: function h by  fct_tac.
have qg: quotient g = source h.
   by rewrite /h/fun_on_quotient/section_canon_proj; aw.
have aux: sub (quotient g) (source h)  by rewrite qg.
suff rg: Imf f =  Vfs h (quotient g). 
  rewrite rg qg restriction1_pr //.
  apply: restriction1_fb; fprops.
set_extens t.
  move /(Imf_P ff) => [x xsf ->].
  rewrite - sfsg in xsf.
  have gxq: inc (class g x) (quotient g) by fprops.
  apply /(Vf_image_P fh aux); exists (class g x) => //.
  have : (related g x (rep (class g x))) by  apply: related_rep_class.
  move / (ea_relatedP ff x (rep (class g x))) => [pa pb ->].
  rewrite - (foqc_V eg) //;Wtac. 
move /(Vf_image_P fh aux)=> [u us ->].
by rewrite foqc_V //; Wtac; rewrite - sfsg; apply: rep_i_sr.
Qed.

(** Canonical decomposition of a function as a surjection, a bijection and an ionjection  *)

Lemma canonical_decompositiona f (r:= equivalence_associated f):
  function f ->
    function ((restriction2 (fun_on_quotient r f)
      (quotient r) (Imf f)) 
     \co (canon_proj r)).
Proof. 
move=> ff.
set (g:= canon_proj r). 
set (a:= Imf f).
set (j:=canonical_injection a (target f)).
set (k:=restriction2 (fun_on_quotient r f) (quotient r) a).
have [er sr]:= (graph_ea_equivalence ff).
have sat: sub a (target f) by apply: Imf_Starget.
have fj: function j by  apply: ci_f.
have ffo: function (fun_on_quotient r f) by apply: foqc_f.
have ra: restriction2_axioms (fun_on_quotient r f) (quotient r) a.
  hnf;rewrite{2 3}/fun_on_quotient/section_canon_proj; aw;split => //.
  move => x /(dirim_P) [z zq zj].
  rewrite (Vf_pr ffo zj) foqc_V //; apply/Imf_P => //. 
  exists (rep z) => //; rewrite - sr; fprops.
have fk:function k by rewrite /k; apply: (proj31 (restriction2_prop ra)).
have ckg: k \coP g.
  by rewrite  /k/g; split; fprops; rewrite /restriction2;aw. 
fct_tac.
Qed.

Lemma canonical_decomposition f (r:= equivalence_associated f):
  function f ->
  f = (canonical_injection (Imf f) (target f))
      \co (restriction2 (fun_on_quotient r f) (quotient r) (Imf f)
           \co (canon_proj r)).
Proof.
move=> ff.
set (g:= canon_proj r). 
set (a:= Imf f).
set (j:=canonical_injection a (target f)).
set (k:=restriction2 (fun_on_quotient r f) (quotient r) a).
have [er sr]:= (graph_ea_equivalence ff).
have sat: sub a (target f) by rewrite /a ; apply: Imf_Starget.
have fj:function j by rewrite /j;apply: ci_f.
have foq: function (fun_on_quotient r f) by apply: foqc_f.
have ra: restriction2_axioms (fun_on_quotient r f) (quotient r) a.
  hnf;rewrite{2 3}/fun_on_quotient/section_canon_proj; aw;split => //.
  move => x /(dirim_P) [z zq zj].
  rewrite (Vf_pr foq zj) foqc_V //; apply/Imf_P => //. 
  exists (rep z) => //; rewrite - sr; fprops.
move: (proj31 (restriction2_prop ra)) => fr.
have fk:function k by rewrite /k.
have ckg:k \coP g.
  by rewrite /k/g; split; fprops; rewrite /restriction2;aw. 
have sfg: source f = source g by rewrite /g; aw.
have fkg: function (k \co g) by fct_tac. 
have cjkg: j \coP (k \co g).
  by split => //; rewrite/j/k/canonical_injection/restriction2; aw.
apply: function_exten=>//; try fct_tac; aw; trivial.
  by rewrite/j/canonical_injection; aw.
move=> x xsf.
  move: (xsf); rewrite - sr=> xsr; rewrite sfg in xsf.
  have a1: (quotient r = target g) by rewrite /g;aw.
  have W1q: inc (Vf g x) (quotient r) by Wtac; fct_tac.
  have p1: inc (Vf k (Vf g x)) a.
    have ->: (a = target k) by rewrite/k/restriction2; aw.
    by Wtac; rewrite /k/restriction2; aw;trivial; ue.
rewrite compfV // ? compf_s // compfV// ci_V //  restriction2_V //.
rewrite foqc_V // canon_proj_V //.
have : (related r x (rep (class r x))) by apply: related_rep_class.
by move/(ea_relatedP ff) => [_ _].
Qed.


Lemma surjective_pr7 f:
  surjection f -> 
  canonical_injection (Imf f) (target f) = identity (target f).
Proof. 
move=> sf; rewrite surjective_pr0 //.
Qed.

Lemma canonical_decomposition_surj f (r:= equivalence_associated f):
  surjection f ->
  f =  (restriction2 (fun_on_quotient r f) (quotient r) (target f))
       \co (canon_proj r).
Proof. 
move=> sf.
move: (surjective_pr7 sf)  (surjective_pr0 sf) => p1 p2.
move: sf => [sf _].
move: (canonical_decomposition sf); rewrite /= p1 p2 -/r => {1} ->.
set (g:= (restriction2 (fun_on_quotient r f) (quotient r) (target f))).
set (h:= g \co (canon_proj r)).
have fh: function h by move:(canonical_decompositiona sf); rewrite -/r p2.
have -> : (target f = target h) by rewrite /h/g/restriction2; aw.
by apply:compf_id_l.
Qed.

Lemma canonical_decompositionb f (r:= equivalence_associated f):
  function f ->
    restriction2 (fun_on_quotient r f)  (quotient r) (target f) =
    (fun_on_quotient r f).
Proof. 
move=> ff.
set (k:=restriction2 (fun_on_quotient r f) (quotient r) (target f)).
have [er sr]:= (graph_ea_equivalence ff).
have ffoq: function (fun_on_quotient r f) by apply: foqc_f.
have ra: restriction2_axioms (fun_on_quotient r f) (quotient r) (target f).
  hnf;rewrite{2 3}/fun_on_quotient/section_canon_proj; aw;split => //.
  move => x /(dirim_P) [z zq zj].
  rewrite (Vf_pr ffoq zj) foqc_V //; Wtac; rewrite - sr;fprops.
have fk: function k by rewrite /k; apply: (proj31(restriction2_prop ra)).
have sk: source k = quotient r by rewrite /k/restriction2; aw.
apply: function_exten =>//.
- by rewrite /restriction2/fun_on_quotient/section_canon_proj; aw.
- by rewrite/k/restriction2/fun_on_quotient; aw. 
- move=> x; rewrite sk => xq; rewrite restriction2_V //. 
Qed.

Lemma canonical_decomposition_surj2 f (r:= equivalence_associated f):
  surjection f ->
  f =  (fun_on_quotient r f) \co (canon_proj r).
Proof.
move=> sf; move: (canonical_decomposition_surj sf). 
by move: sf => [ff _]; move: (canonical_decompositionb ff) => /= -> <-.
Qed.

(** **  EII-6-6 Inverse image of an equivalence relation; induced equivalence relation *)

(** We have an equivalence on the source induced by the equivalence on the target*)

Definition inv_image_relation f r :=
  equivalence_associated (canon_proj r \co f). 

Definition iirel_axioms f r :=
  [/\ function f, equivalence r & substrate r = target f].

Lemma iirel_f f r:
   iirel_axioms f r -> function (canon_proj r \co f).
Proof. 
by move=> [ff er tf]; fct_tac; [ fprops | aw].
Qed.

Lemma iirel_relation f r:
  iirel_axioms f r -> equivalence_on (inv_image_relation f r) (source f).
Proof. 
by move=> ia;move:(graph_ea_equivalence(iirel_f ia)); aw.
Qed.

Lemma iirel_relatedP f r:  iirel_axioms f r ->  forall x y,
  (related (inv_image_relation f r) x y <->
   [/\ inc x (source f), inc y (source f) & related r (Vf f x) (Vf f y)]). 
Proof. 
move=> ia.
have fc : function ((canon_proj r) \co f) by apply: iirel_f.
move: ia => [ff er tf].
rewrite /inv_image_relation.
have cct: ((canon_proj r) \coP f) by split; aww.
have iWs: forall u, inc u (source f) -> inc (Vf f u) (substrate r).
  by move=> u; rewrite tf; fprops. 
move => x y; split.
  move/(ea_relatedP fc); rewrite compf_s; move => [xs ys].
  move: (iWs _ xs) (iWs _ ys)=> p1 p2.
  rewrite ! compfV // ! canon_proj_V // => p3;split => //.
  by apply/(related_equiv_P er).
move => [pa pb pc].
apply /(ea_relatedP fc); aw; split => //; rewrite ! compfV // ! canon_proj_V //.
+ by apply: class_eq1;fprops.
+ Wtac.
+ Wtac.
Qed.

Lemma iirel_classP f r:
  iirel_axioms f r -> forall x, 
  (classp (inv_image_relation f r) x  <->
  exists y, [/\ classp r y,
    nonempty (y \cap (Imf f))
    & x = Vfi f y]).
Proof. 
move=> ia; move: (ia) => [ff er tf].
have [pa sir] := (iirel_relation ia).
move => x; split.
  move => clix; move: (clix)=> []; rewrite sir => sa sb.
  have iWs: inc (Vf f (rep x)) (substrate r) by rewrite tf;  Wtac.
  exists (class r (Vf f (rep x))); split.
  - by apply: class_class.
  - exists (Vf f (rep x)); apply: setI2_i; [ fprops | Wtac ].
  - set_extens t.
    rewrite {1} sb => /(class_P pa)  /(iirel_relatedP ia) [ysf tsf ryt].
    apply/(iim_fun_P); exists (Vf f t); [ by apply /class_P | Wtac].
  move /(iim_fun_P) => [u uc Jg]; rewrite sb; apply /(class_P pa).
  apply /(iirel_relatedP ia);split => //; first by Wtac.
  by rewrite - (Vf_pr ff Jg); apply /(class_P er).
move=> [y [cy [u ui] xi]]; move: cy => [c1 c2].
move: ui => /setI2_P [uy] /(Imf_P ff) [v vsf uw].
have vx: inc v x by rewrite xi; apply /(iim_fun_P); ex_tac; rewrite uw; Wtac.
have qc: related r (rep y) (Vf f v) by rewrite - uw;apply /class_P => //; ue.
suff: x = class (inv_image_relation f r) v.
  move => ->; apply: class_class => //; ue.
set_extens t.
  rewrite  xi => /(iim_fun_P) [z' z'y Jg2].
  apply/(class_P pa); apply /(iirel_relatedP ia);split => //; first by Wtac.
  have pb: related r (rep y) z' by apply /(class_P er); ue.
  rewrite - (Vf_pr ff Jg2); equiv_tac.
move /(class_P pa) => /(iirel_relatedP ia)  [_ qa qb].
rewrite xi; apply /(iim_fun_P); exists (Vf f t) => //; last by  Wtac. 
rewrite c2; apply /class_P => //; equiv_tac.
Qed.

(** Equivalence induced on a subset of the substrate *)

Definition induced_relation r a :=
  inv_image_relation (canonical_injection a (substrate r)) r.

Definition induced_rel_axioms r a  :=
   equivalence r /\ sub a (substrate r).
Definition canonical_foq_induced_rel r a :=
  restriction2 (fun_on_quotients (induced_relation r a) r 
    (canonical_injection a (substrate r))) 
  (quotient (induced_relation r a))
  (Vfs (canon_proj r) a).

Section InducedRelation.
Variables (r a: Set).
Hypothesis ira: induced_rel_axioms r a. 

Lemma induced_rel_iirel_axioms:
  iirel_axioms (canonical_injection a (substrate r)) r.
Proof.
by move: ira=> [er ar]; split; fprops;rewrite/canonical_injection; aw.
Qed.

Lemma induced_rel_equivalence:
  equivalence_on (induced_relation r a) a.
Proof.
move: (iirel_relation induced_rel_iirel_axioms).
by rewrite/canonical_injection; aw. 
Qed.


Lemma induced_rel_relatedP u v:
  related (induced_relation r a) u v <->
    [/\ inc u a, inc v a & related r u v].
Proof. 
move: (induced_rel_iirel_axioms) => iia.
move: ira=> [er ar].
split.
  move/(iirel_relatedP iia); rewrite lf_source; move => [pa pb].
  rewrite ci_V //ci_V  //.
move => [ua va ruv];apply/(iirel_relatedP iia); rewrite lf_source; split => //.
rewrite ci_V //ci_V  //. 
Qed.

Lemma induced_rel_classP x:
  (classp (induced_relation r a) x <->
  exists y, [/\ classp r y, nonempty (y \cap a) & x = (y \cap a)]).
Proof. 
have iia:=(induced_rel_iirel_axioms).
move: (ira)=> [er ar].
have p: forall y, Vfi (canonical_injection a (substrate r)) y
   = y \cap a.
  rewrite/Vfi /canonical_injection; aw.
  rewrite - diagonal_is_identity.
  move=> y;set_extens t.
    move /iim_graph_P => [u uy] /diagonal_pi_P [pa pb]; apply/setI2_P.
    split => //; ue.
  move /setI2_P => [ty ta]; apply /iim_graph_P; ex_tac. 
  by apply /diagonal_pi_P.
split.
  move/(iirel_classP iia); rewrite (ci_range ar); move => [y]; rewrite p.
  by move => [pa pb pc]; exists y.
move => [y [cy ney xi]]; apply/(iirel_classP iia); exists y.
split; [ done |  by rewrite (ci_range ar) | by rewrite p ].
Qed.

Lemma compatible_injection_induced_rel:
  compatible_with_equivs (canonical_injection a (substrate r))
  (induced_relation r a) r.
Proof. 
move: (ira)=> [er sa].
move:(induced_rel_equivalence) => [qa qb].
apply: compatible_with_pr2 =>//.
- by apply: ci_f.
- by rewrite/canonical_injection; aw. 
- by rewrite/canonical_injection;aw.
- move=> x y /induced_rel_relatedP [xa ya rxy]; rewrite ci_V // ci_V //. 
Qed.

Lemma foq_induced_rel_fi:
  injection (fun_on_quotients (induced_relation r a) r 
    (canonical_injection a (substrate r))).
Proof.
move: (ira)=> [er sa].
set (f := (canonical_injection a (substrate r))).
have [ei sr] := (induced_rel_equivalence).
have ff: function f by rewrite /f;apply: ci_f.
have tf: target f = substrate r by rewrite /f /canonical_injection; aw.
have sf: source f = substrate (induced_relation r a).  
  by rewrite /f sr // /canonical_injection; aw.
split; first by apply: foqcs_f. 
have ->: (source (fun_on_quotients (induced_relation r a) r f) = 
    quotient (induced_relation r a) ).
  by rewrite/fun_on_quotients /section_canon_proj; aw. 
move=> x y xs ys /=; rewrite  foqcs_V // foqcs_V //.
have eq: a = substrate (induced_relation r a) by rewrite sr.
have rxa: inc (rep x) a by rewrite eq; fprops.
have rya: inc (rep y) a by rewrite eq; fprops.
rewrite ci_V //  ci_V // => cc.
have: (related (induced_relation r a) (rep x) (rep y)).
  apply /induced_rel_relatedP; split => //; apply/ related_equiv_P => //.
   by split => //; apply: sa. 
by move /(related_rr_P ei xs ys).
Qed.

Lemma foq_induced_rel_image :
  Vfs  (fun_on_quotients (induced_relation r a) r 
    (canonical_injection a (substrate r))) (quotient (induced_relation r a))
  = Vfs (canon_proj r) a.
Proof. 
move: (ira)=> [er sa].
set (ci := canonical_injection a (substrate r)).
have fci: function ci by apply: ci_f.
have [ei qb] := induced_rel_equivalence.
have sci: source ci = substrate (induced_relation r a).
  by rewrite qb /ci  /canonical_injection; aw.
set (f:= fun_on_quotients (induced_relation r a) r ci).
move: (foq_induced_rel_fi); rewrite -/ci -/f; move => inf.
have ff: function f by fct_tac. 
have gf: sgraph (graph f) by fprops.
have tci: target ci = substrate r by rewrite /ci/canonical_injection; aw.
have fc: function (canon_proj r) by fprops.
set_extens x. 
  move/dirim_P => [y yq Jg].
  move: (yq) => /(setQ_P ei) /induced_rel_classP [z [cz nei yi]].
  move: (Vf_pr ff Jg); rewrite foqcs_V // => cx. 
  have: (inc (rep y) (z \cap a)) by rewrite -yi; apply: (setQ_repi ei).
  move /setI2_P => [ryz rya]; rewrite  ci_V // in cx. 
  move: nei=> [u] /setI2_P [uz ua]; apply /dirim_P; ex_tac.
  have ryu: (related r (rep y) u) by apply/(in_class_relatedP er); exists z.
  move: (sa _ ua) => us.  
  have ->: x = Vf (canon_proj r) u.
    by rewrite canon_proj_V // cx; apply: class_eq1.
  by Wtac; aw.
move/dirim_P => [y ya Jg]; move: (sa _ ya)=> yu.
move: (Vf_pr fc Jg);  rewrite canon_proj_V // => cx.
have yx: (inc y x) by rewrite cx; fprops.
set (z:= x \cap a).
have ney: nonempty z by rewrite /z; exists y; fprops. 
have zq: inc z (quotient (induced_relation r a)).
  apply/(setQ_P ei); apply/ induced_rel_classP; exists x; split => //.
   rewrite cx; apply: class_class =>//. 
apply /dirim_P; ex_tac.
have: (inc (rep z) (x \cap a)) by apply: (setQ_repi ei).
move /setI2_P => [rzx rza].
have -> : x = Vf f (x \cap a).  
  rewrite /f foqcs_V// ci_V // -/z cx.  
  have:  (related r y (rep z)). 
    apply /(in_class_relatedP er); exists x; split => //.
    by rewrite cx; apply: class_class.
  by move /(related_equiv_P er) => [_ _].
by rewrite -/z; Wtac; rewrite/f/fun_on_quotients/section_canon_proj; aw.
Qed. 

Lemma canonical_foq_induced_rel_fb:
 bijection (canonical_foq_induced_rel r a).
Proof.
set ci:= (canonical_injection a (substrate r)).
have sf: source (fun_on_quotients (induced_relation r a) r ci) = 
     quotient (induced_relation r a).
  by rewrite /fun_on_quotients/section_canon_proj; aw.
have ra:restriction2_axioms
     (fun_on_quotients (induced_relation r a) r ci)
     (quotient (induced_relation r a)) (Vfs (canon_proj r) a).
  move: (foq_induced_rel_fi) => ifoq. 
  split; first by fct_tac.
     by rewrite /fun_on_quotients/section_canon_proj; aw.
    rewrite /fun_on_quotients; aw; move=> t ts; move: ira=> [er ar].
    by apply: (sub_im_canon_proj_quotient  ar ts). 
  by rewrite foq_induced_rel_image; fprops.
split; first  by apply: restriction2_fi=>//; apply: foq_induced_rel_fi.
apply: restriction2_fs=>//.
by rewrite - foq_induced_rel_image /Imf sf.
Qed.

End InducedRelation.

(** ** EII-6-7 Quotients of equivalence relations *)

(** Definition of a finer equivalence *)

Definition finer_equivalence s r:= 
  forall x y, related s x y -> related r x y.

Definition finer_axioms s r := 
  [/\ equivalence s,  equivalence r & substrate r = substrate s].

Lemma finest_equivalence r:
   equivalence r -> finer_equivalence (diagonal (substrate r)) r.
Proof. move=> er x t /diagonal_pi_P [xs <-]; equiv_tac. Qed.

Lemma coarsest_equivalence r:
   equivalence r -> finer_equivalence r (coarse (substrate r)).
Proof. 
move=>  er x y;rewrite coarse_related; move /(related_equiv_P er) => [pa pb _].
by split.
Qed.

Section FinerEquivalence.
Variable (r s: Set).
Hypothesis fa: finer_axioms s r.

Lemma finer_sub_equivP:
  (finer_equivalence s r <-> sub s r).
Proof. 
move: fa => [es er srss].
split. 
  move=> fe t ts. 
  have gs: (sgraph s) by fprops. 
  by rewrite -(gs _ ts); apply: fe; hnf; rewrite (gs _ ts).
move => t x y; rewrite /related; apply: t.
Qed.

Lemma finer_sub_equivP2:
  (finer_equivalence s r <-> 
    (forall x, exists y, sub (class s x) (class r y))).
Proof.
move: fa=> [es er srss].
split. 
  move=> fsr x; exists x. 
  by move=> u /(class_P es) h; apply /(class_P er); apply:fsr.
move=> h x y rxy.
move:(h x)=> [z sxz]. 
have xs: inc x (substrate s) by substr_tac.
have ixc: inc x (class s x) by fprops.
have ys: inc y (class s x) by apply /(class_P es).
move: (sxz _ ixc)(sxz _ ys) => /(class_P er) pa /(class_P er) pb; equiv_tac.
Qed.

Lemma finer_sub_equivP3:
  (finer_equivalence s r <-> forall y, saturated s (class r y)).
Proof. 
move: (fa)=>[es er srss].
split.  
  move=> fe y.
  apply/(saturatedP es); first by  rewrite - srss; apply: sub_class_substrate. 
  move => z zc; move: fe => /finer_sub_equivP2 fe.
  move/(class_P er): (zc) => r1.
  have zs: (inc z (substrate s)) by rewrite - srss; substr_tac.
  move: (fe z)=> [x cxy]. 
  suff: (class r x = class r y) by move=> <-.
  have: (inc z (class r x)) by apply: cxy; fprops.
  move =>  /(class_P er) r2.
  apply: (class_eq1 er); equiv_tac.
move=> p x y re; move: (p x).
move: (sub_class_substrate er (x:=x)); rewrite  srss => aux.
move /(saturatedP es aux) => h.
have p1: inc x (substrate s) by substr_tac.
have p2: inc x (class r x) by rewrite - srss in p1;fprops.
have p3: inc y (class s x) by apply/class_P.
by move:((h  _ p2) _ p3) => /(class_P er).
Qed.

Lemma compatible_with_finer:
  finer_equivalence s r -> 
  compatible_with_equiv (canon_proj r) s.
Proof. 
move :fa=> [es er fh] fe.
split; aww => x y rxy.
move: (fe _ _ rxy) => /(related_equiv_P er) [p1 p2 h].  
by rewrite !canon_proj_V.
Qed. 

Lemma foq_finer_f:
  finer_equivalence s r -> function(fun_on_quotient s (canon_proj r)).
Proof. by move : fa=> [es er fh] fe;  apply: foqc_f; fprops; aw. Qed.

Lemma foq_finer_V x:
  finer_equivalence s r ->  inc x (quotient s) ->
  Vf (fun_on_quotient s (canon_proj r)) x = class r (rep x).
Proof. 
move: fa => [es er fh] fe xq.
rewrite  foqc_V // ?canon_proj_V // ? fh; aw; fprops.
Qed.

Lemma foq_finer_fs:
  finer_equivalence s r -> surjection(fun_on_quotient s (canon_proj r)).
Proof. 
move=> fe.
split; first by apply: foq_finer_f.
move: fa=> [es er ss] y yt.
have yq:inc y (quotient r) by  move:yt; rewrite/fun_on_quotient; aw.
have rys:(inc (rep y) (substrate r)) by fprops.
have sfo:source (fun_on_quotient s (canon_proj r)) = (quotient s).
  by rewrite /fun_on_quotient/section_canon_proj; aw.
set(x := class s (rep y)). 
have xq: (inc x (quotient s)) by rewrite /x; rewrite ss in rys; fprops. 
rewrite sfo; ex_tac.
rewrite foq_finer_V //. 
have cry: (class r (rep y) = y) by apply: class_rep=>//. 
rewrite -cry; apply: class_eq1 =>//;apply: fe.
apply /(class_P es);apply: rep_i; rewrite /x. 
apply /(setQ_ne es); apply /(setQ_P es); apply/(class_class es); ue.
Qed.

End FinerEquivalence.

(** Quotient of a relation by a finer one *)

Definition quotient_of_relations r s:= 
  equivalence_associated (fun_on_quotient s (canon_proj r)).

Lemma cqr_aux s x y u:
  equivalence s -> sub y (substrate s) -> 
  x = Vfs (canon_proj s) y ->
  (inc u x <-> (exists2 v, inc v y & u = class s v)).
Proof. 
move=> es ys xi.
split.
  rewrite xi /Vfs => ui.
  move:(sub_im_canon_proj_quotient  ys ui) => uqs.
  move: ui=> /dirim_P [z zy Jg]; move : (ys _ zy) => zs. 
  move: Jg => /(rel_gcp_P es zs uqs) zu.
  ex_tac.
  have aux: (class s (rep u) = u) by (apply: class_rep). 
  have : related s (rep u) z by apply /(class_P es); ue.
  move /(related_equiv_P es) => [_ _]; ue.
have fc: function (canon_proj s) by fprops. 
move=> [v vy ->]; move: (ys _ vy) => vs; rewrite xi.
apply/dirim_P; ex_tac; apply /(rel_gcp_P es vs); fprops. 
Qed.

Section QuotientRelations.
Variables (r s: Set).
Hypotheses (fa:finer_axioms s r) (fe: finer_equivalence s r).

Lemma quo_rel_equivalence: 
  equivalence_on (quotient_of_relations r s) (quotient s).
Proof. 
move: (graph_ea_equivalence (proj1 (foq_finer_fs fa fe))). 
by rewrite/fun_on_quotient/section_canon_proj; aw.
Qed.


Lemma quo_rel_relatedP x y:
  related (quotient_of_relations r s) x y <->
    [/\ inc x (quotient s), inc y (quotient s) & related r (rep x) (rep y)].
Proof.
have foq: function (fun_on_quotient s (canon_proj r)).
  by apply:(surj_function (foq_finer_fs fa fe)).
have fc: function (canon_proj r) by fprops.
have sf: source (fun_on_quotient s (canon_proj r)) = quotient s.
  by rewrite /fun_on_quotient/section_canon_proj; aw. 
move: fa =>[es er ss].
have sc:source (canon_proj r) = substrate s by aw.
rewrite/quotient_of_relations; split.
  move /(ea_relatedP foq); rewrite sf.
  move => [xq yq h];split => //.
  have p1: (inc (rep x) (substrate r)) by rewrite ss; fprops.
  have p2: (inc (rep y) (substrate r)) by rewrite ss; fprops.
  move: h;rewrite ! foqc_V // ! canon_proj_V // => svc.
  by apply/(related_equiv_P er).
move => [xs ys rr]; apply /(ea_relatedP foq); rewrite sf; split => //.
move/(related_equiv_P er): rr => [p1 p2 p3].
by rewrite ! foqc_V // ! canon_proj_V.
Qed.

Lemma quo_rel_related_bisP  x y:
  inc x (substrate s) -> inc y (substrate s) ->
  (related (quotient_of_relations r s) (class s x) (class s y)
     <-> related r x y).
Proof. 
move=> xs ys.
move: fa =>[es er ss].
have p1:(related r x (rep (class s x))) by apply: fe; apply: related_rep_class.
have p2:(related r y (rep (class s y))) by apply: fe; apply: related_rep_class.
split.
  move/quo_rel_relatedP=> [ixs iys rxy].
  apply: (@transitivity_e _ (rep (class s x))) =>//.
  apply: (@transitivity_e _  (rep (class s y))) =>//. 
  equiv_tac.
move=> h; apply/quo_rel_relatedP; split; fprops.
apply: (@transitivity_e _  x) =>//.
apply: symmetricity_e=>//. 
equiv_tac. 
Qed.

Lemma quo_rel_class_bisP x:
  ( inc x (quotient (quotient_of_relations r s)) <->
    exists2 y, inc y (quotient r) & x = Vfs (canon_proj s) y).
Proof. 
have [eq aux ]:=(quo_rel_equivalence).
move: (fa) =>[es er ss]. 
have fc: function (canon_proj s) by fprops.
split.
  move/(setQ_P eq) => cq; move: (cq)=> [ca cb].
  set(y:= Zo (substrate r) (fun v => exists2 u, inc u x & inc v u)).
  move: (rep_in_class eq cq) => rxx.
  move: (sub_class_sr eq cq); rewrite aux => scx.
  move: (scx _ rxx) => repxq; move: (setQ_repi es repxq) => rrx.
  have rrsr: inc (rep (rep x)) (substrate r).
    by rewrite ss; apply: (inc_in_setQ_sr es rrx repxq).
  have ys: sub y (substrate r) by rewrite /y ss; apply: Zo_S.
  have cy: y = class r (rep (rep x)).
    set_extens u.
       move /Zo_P => [usr [t tx ut]]; apply /(class_P er).
       move: tx; rewrite {1} cb; move /(class_P eq).
       move /quo_rel_relatedP => [uq vq ruv].
       apply: (@transitivity_e _ (rep t))=>//.
       by apply: fe; apply/(class_P es); rewrite class_rep.
    move /(class_P er) => rab.
    move: (arg2_sr rab) => bsr; move: rab.
    rewrite ss in rrsr bsr.
    move /(quo_rel_related_bisP rrsr bsr).
    move /(class_P eq); rewrite (class_rep es repxq) - cb => h.
    apply: Zo_i; [ ue | ex_tac].
  exists y.
    rewrite cy; apply/(setQ_P er); apply: (class_class er rrsr).
  set (xx := Vfs (canon_proj s) y). 
  rewrite ss in ys.
  set_extens u. 
    move => ux; move: (scx _ ux) => aux1; 
    apply/ (cqr_aux u es ys (refl_equal xx)).
    move: (setQ_repi es aux1) => ur.
    exists (rep u); first by apply: Zo_i; [ ue | ex_tac].
    by symmetry; apply: class_rep.
  move/ (cqr_aux u es ys (refl_equal xx)) => [v vy ->].
  move: vy => /Zo_P [vr [w wx vw]].
  have wq: (inc w (quotient s)) by apply: scx.
  move: (related_rep_in_class es wq vw).
  move => /(related_equiv_P es) [rws vd]. 
  by move: (class_rep es wq) => -> <-.
move =>  [y] /(setQ_P er) cy xd; apply /(setQ_P eq).
move: (rep_in_class er cy) => ryy.
move: (sub_class_sr er cy); rewrite ss => ysr.
have sxq: sub x (quotient s).
   by move => t tx; apply: (sub_im_canon_proj_quotient ysr); ue.
have nex: nonempty x.
  by rewrite xd; apply: nonempty_image => //; aw; trivial;ex_tac.
move: (rep_i nex) => rrx.
move: (rrx) => /(cqr_aux (rep x) es ysr xd) [v vy asv].
split; [ue |  set_extens t].
  move => tx; apply/(class_P eq).
  move/ (cqr_aux t es ysr xd): tx => [w wy asw].
  rewrite asv asw ; apply /quo_rel_related_bisP; try apply: ysr => //.
  by apply /(in_class_relatedP er); exists y.
move /(class_P eq) => /quo_rel_relatedP [aq bq rab].
apply/(cqr_aux t es ysr xd); exists (rep t); last by symmetry; apply: class_rep.
move: (rel_in_class er cy vy) => s1.
apply: (rel_in_class2 er cy).
apply: (transitivity_e er s1).
apply: (@transitivity_e _ (rep (rep x)))=>//.
apply: fe; apply /(in_class_relatedP es).
exists (rep x); split.
- by rewrite asv; apply: class_class =>//; apply: ysr.
- by rewrite asv; apply: inc_itself_class =>//; apply: ysr.
- by apply: (setQ_repi es).
Qed.


Lemma quotient_canonical_decomposition
   (f := fun_on_quotient s (canon_proj r))
   (qr := quotient_of_relations r s):
  f =  (fun_on_quotient qr f) \co (canon_proj qr).
Proof.
have sj: (surjection f) by rewrite /f;apply: foq_finer_fs.
apply: (canonical_decomposition_surj2 sj).
Qed.

End QuotientRelations.

Lemma quo_rel_pr s t
  (r := inv_image_relation (canon_proj s) t):
  equivalence s -> equivalence t -> substrate t = quotient s ->
  t = quotient_of_relations r s.
Proof. 
move=> es et st.
have iaa: iirel_axioms (canon_proj s) t. 
  by split;aww.
have [er sr]:=(iirel_relation iaa).
have fa:finer_axioms s r.
  by split=>//; rewrite /r sr //; aw.
have fe: finer_equivalence s r. 
  move => x y sxy; apply / iirel_relatedP =>  //. 
  have xs: inc x (substrate s) by  substr_tac.
  have ys: inc y (substrate s) by  substr_tac.
  aw; rewrite !canon_proj_V//; split=>//.
  have -> : (class s x =class s y) by  apply: class_eq1.
  by apply: reflexivity_e=>//; rewrite st; fprops.
have [eq sr'] := (quo_rel_equivalence fa fe).
apply/sgraph_exten; fprops.
move=> u v; split.
  move => tuv; apply/quo_rel_relatedP => //.
  have us: (inc u (quotient s))  by rewrite - st; substr_tac.
  have vs: (inc v (quotient s))  by rewrite - st; substr_tac.
  have rus: (inc (rep u) (substrate s)) by fprops.
  have rvs: (inc (rep v) (substrate s)) by fprops.
  split=>//; apply /iirel_relatedP => //.
  by aw;split; trivial; rewrite !canon_proj_V// !class_rep //.
move/(quo_rel_relatedP fa fe) => [uq vq]. 
move /(iirel_relatedP iaa) ;rewrite canon_proj_s. 
by move=> [ru rv]; rewrite !canon_proj_V// ! class_rep.  
Qed.

(** ** EII-6-8 Product of two equivalence relations *)

Definition prod_of_relation r r':=
  graph_on 
    (fun x y=> inc (J(P x)(P y)) r /\ inc (J(Q x)(Q y)) r')
  ((substrate r) \times (substrate r')).

Lemma substrate_prod_of_rel r r':
  equivalence r ->equivalence r' ->
  substrate (prod_of_relation r r') =  (substrate r)\times (substrate r').
Proof.
move => pa pb; rewrite graph_on_sr //.
by move => a /setX_P [_ ta tb]; split; equiv_tac.
Qed.

Lemma order_product2_sr1 f g:
  preorder f -> preorder g -> 
  substrate (prod_of_relation f g) = (substrate f) \times (substrate g).
Proof. 
move=> [_ rf _] [_ rg _ ]; apply: graph_on_sr. 
move => a /setX_P [pa Ps Qs]. 
by split; [apply: rf | apply: rg].
Qed.

Lemma order_product2_sr f g:
  order f -> order g -> 
  substrate (prod_of_relation f g) = (substrate f) \times (substrate g).
Proof.
move=> orf og; apply: order_product2_sr1; by apply: order_preorder.
Qed.

Lemma equivalence_prod_of_rel r r':
  equivalence r -> equivalence r' ->
  equivalence (prod_of_relation r r').  
Proof.
move => pa pb.
apply: equivalence_from_rel; split.
  move => a b [ra rb];split; equiv_tac.
move => a b c [ra rb] [rc rd];split; equiv_tac.
Qed. 

Lemma order_product2_preorder f g:
  preorder f -> preorder g -> preorder (prod_of_relation f g).
Proof.
move => [_ rf tf] [_ rg tg]; apply: preorder_from_rel; hnf; split.
  move => x y z[pxy qxy][pyz qyz].  
  split; [ apply: tf pxy pyz | apply: tg qxy qyz].
move=> x y [pxy qxy]; split; split; try apply: rf; try apply: rg; substr_tac.
Qed.

Lemma order_product2_or f g:
  order f -> order g -> order (prod_of_relation f g).
Proof. 
move=> orf og.
have [gr rr tr]: preorder (prod_of_relation f g).
  by apply: order_product2_preorder;  apply: order_preorder.
move: orf og => [_ rf tf af] [_ rg tg ag].
split => //.
move => x y /Zo_P [pa [pb pc]] /Zo_P [qa [qb qc]].
move: pb pc qb qc; aw => pb pc qb qc.
move: pa => /setX_P [_ ]; aw ;move /setX_P => [px _ _] /setX_P [py _ _].
apply: pair_exten => //; [exact: (af _ _ pb qb) | exact: (ag _ _ pc qc)].
Qed.

Lemma prod_of_rel_P r r' a b:
  related (prod_of_relation r r')  a b <->
  [/\ pairp a, pairp b, related r (P a) (P b) & related r' (Q a) (Q b)].
Proof.
rewrite /related /prod_of_relation; split.
  by move /graph_on_P0 =>  [] /setX_P [pa _ _]  /setX_P [pb _ _] [pc pd].
move => [pa pb pc pd]; apply /graph_on_P0;split => //;
  apply/setX_P; split => //; substr_tac.
Qed.

Lemma related_prod_of_relP1  r r' x x' v:
 related (prod_of_relation r r') (J x x') v <->
   (exists y y', [/\ v = J y y',  related r x y & related r' x' y']).
Proof.
split.
  move /prod_of_rel_P; aw; move=> [_ pb pc pd].
  by exists (P v); exists  (Q v).
move=> [y [y' [eq r1 r2]]]; rewrite eq; apply /prod_of_rel_P; aw; split; fprops.
Qed.

Lemma related_prod_of_relP2 r r' x x' v:
  (related (prod_of_relation r r') (J x x') v <->
    inc v ((im_of_singleton r x) \times (im_of_singleton r' x'))).
Proof. 
split. 
  move=> /related_prod_of_relP1 [y [y' [eq r1 r2]]]; rewrite eq. 
  by apply/setXp_i; apply /dirim_set1_P.
move /setX_P => [pv /dirim_set1_P j1r /dirim_set1_P j2r]. 
by apply/related_prod_of_relP1;exists (P v); exists (Q v);aw.
Qed.

Lemma class_prod_of_relP2 r r':
  equivalence r -> equivalence r' -> forall x,
  (classp (prod_of_relation r r') x  <->
    exists u v, [/\ classp r u, classp r' v & x = u \times v]).
Proof.
move=> er er'.
move:(equivalence_prod_of_rel er er')=> er''.
split.
  move => cx; move: (cx) => [ca cb].
  move: (ca); rewrite (substrate_prod_of_rel er er') => /setX_P [pa pb pc].
  exists (class r (P (rep x))); exists (class r' (Q (rep x))); split => //.
    by apply: (class_class er).
    by apply: (class_class er').
  set_extens v.
    rewrite {1} cb; move /(class_P er'') => /prod_of_rel_P [qa qb qc qd].
    apply /setX_P => //; split => //; apply /class_P => //.
  move /setX_P => [qa qb qc]; rewrite cb; apply /(class_P er'').
  by apply /prod_of_rel_P;split => //; apply /class_P.
move=> [u [v [pa pb pe]]].
move: (pa)(pb) => [pc _] [pd _].
suff : x = class (prod_of_relation r r') (J (rep u) (rep v)).
  move => ->; apply: (class_class er'').
  by rewrite (substrate_prod_of_rel er er'); apply:setXp_i.
set_extens t.
  rewrite pe; move => /setX_P [qa qb qc].
  apply /(class_P er''); apply /prod_of_rel_P; aw.
  split; fprops; by apply :rel_in_class. 
move /(class_P er'') =>  /prod_of_rel_P; aw; move => [_ qa qb qc].
rewrite pe; apply /setX_P;split => //.
  apply: (rel_in_class2 er pa qb).
apply: (rel_in_class2 er' pb qc).
Qed.

Lemma ext_to_prod_rel_f r r':
  equivalence r -> equivalence r' ->
  function (ext_to_prod(canon_proj r)(canon_proj r')).
Proof. move=> er er'; apply: ext_to_prod_f; fprops. Qed.

Lemma ext_to_prod_rel_V r r' x x':
  equivalence r -> equivalence r' ->
  inc x (substrate r) -> inc x' (substrate r') ->
  Vf (ext_to_prod(canon_proj r)(canon_proj r'))  (J x x') =
  J (class r x) (class r' x').
Proof. 
move=> er er' xs xs'.  
by rewrite ext_to_prod_V; aww; rewrite !canon_proj_V.
Qed.

Lemma compatible_ext_to_prod r r':
  equivalence r -> equivalence r' ->
   compatible_with_equiv (ext_to_prod (canon_proj r) (canon_proj r'))
     (prod_of_relation r r').
Proof. 
move=> er er'.
have fc: function (canon_proj r) by fprops.
have fc': function (canon_proj r') by fprops.
split; first by  apply: ext_to_prod_f. 
  by rewrite  substrate_prod_of_rel // /ext_to_prod; aw.
move=> x x'.
move /prod_of_rel_P=> [px px'].
move/(related_equiv_P er) => [pxs qx cx] /(related_equiv_P er') [pys qy cy].
have q1: (J (P x)(Q x) = x) by aw.
have q2: (J (P x')(Q x') = x') by aw.
rewrite -q1 -q2 ! ext_to_prod_V //; aw; trivial. 
by rewrite ! canon_proj_V // cx cy.
Qed.

Lemma compatible_ext_to_prod_inv r r' x x':
  equivalence r -> equivalence r' ->
  pairp x -> inc (P x) (substrate r) -> inc (Q x)  (substrate r') ->
  pairp x' -> inc (P x') (substrate r) -> inc (Q x')  (substrate r') ->
  Vf (ext_to_prod (canon_proj r) (canon_proj r')) x =
  Vf (ext_to_prod (canon_proj r) (canon_proj r')) x'
  -> related (prod_of_relation r r') x x'.
Proof. 
move=>  er er' px Px Qx px' Px' Qx'.
have p1: (J (P x) (Q x) = x) by aw. 
have p2: (J (P x') (Q x') = x') by aw. 
rewrite -p1 -p2 ext_to_prod_rel_V // ext_to_prod_rel_V // => Jeq.
move: (pr1_def Jeq) (pr2_def Jeq)=> eq1 eq2.
by apply/prod_of_rel_P; aw; split; fprops; apply/related_equiv_P.
Qed.

Lemma related_ext_to_prod_rel r r':
  equivalence r -> equivalence r' ->
  equivalence_associated (ext_to_prod(canon_proj r)(canon_proj r')) =
  prod_of_relation r r'.
Proof. 
move=> er er'.
move:(compatible_ext_to_prod er er')=> [fe se re].
have eq: equivalence (prod_of_relation r r')
   by apply: equivalence_prod_of_rel.
have eq' := proj1(graph_ea_equivalence fe). 
apply: sgraph_exten; fprops. 
have f1: function (canon_proj r) by fprops.
have f2: function (canon_proj r') by fprops. 
move=> u v; split.
  move /(ea_relatedP fe) => [].
  rewrite  {1 2} /ext_to_prod lf_source. 
  move /setX_P => [up Pu Qu] /setX_P [vp Pv Qv].
  have r1: (J (P u)(Q u) = u) by aw.
  have r2: (J (P v)(Q v) = v) by aw.
  rewrite  -r1 -r2 ext_to_prod_V // ext_to_prod_V //.
  move: Pu Qu Pv Qv; rewrite 2! canon_proj_s => Pu Qu Pv Qv.
  rewrite !canon_proj_V // => neq.
  move: (pr1_def neq) (pr2_def neq)=> eq1 eq2.
  by apply /prod_of_rel_P;split; fprops; aw; apply/related_equiv_P.
move /prod_of_rel_P => [pu pv] /(related_equiv_P er)[Pu Pv c1]
    /(related_equiv_P er') [Qu Qv c2]. 
apply /(ea_relatedP fe); split.
  by rewrite /ext_to_prod lf_source; aw;apply/setX_P.
  by rewrite /ext_to_prod lf_source; aw;apply/setX_P.
by apply: re; apply/prod_of_rel_P; split => //; apply /(related_equiv_P).
Qed.

Lemma decomposable_ext_to_prod_rel r r':
  equivalence r -> equivalence r' ->
  exists h,  [/\ bijection h,
    source h = quotient (prod_of_relation r r'),
    target h = (quotient r) \times (quotient r') &
    h \co (canon_proj (prod_of_relation r r')) = 
    ext_to_prod(canon_proj r)(canon_proj r')].
Proof.
move=> er er'.
set (r'':=prod_of_relation r r').
set (f'':=ext_to_prod (canon_proj r) (canon_proj r')).
set (h:=fun_on_quotient r'' f'').
have er'': equivalence r'' by rewrite /r''; apply: equivalence_prod_of_rel. 
have co: compatible_with_equiv f'' r''.
  rewrite /f'' /r'';  apply: compatible_ext_to_prod=>//. 
move :(compose_foq_proj er'' co); rewrite -/h => cop.
have sh: source h = quotient r''.
   by rewrite /h /fun_on_quotient/section_canon_proj; aw.
have th: target h = (quotient r) \times (quotient r').
  by rewrite /h/fun_on_quotient/ f'' /ext_to_prod; aw.
have fh: function h.
  rewrite /h /f''; apply: foqc_f =>//.
    apply: ext_to_prod_f; fprops. 
  by rewrite /r'' substrate_prod_of_rel // /ext_to_prod; aw.
have ff'': function f'' by rewrite /f''; apply: ext_to_prod_rel_f.
have sf'':  source f'' = substrate r''. 
  by rewrite /f'' /r''/ext_to_prod substrate_prod_of_rel; aw. 
have ih: injection h.
  split=>//. 
  move=> x y; rewrite sh /h => xs ys.  
  rewrite foqc_V // foqc_V //.
  move: (rep_i_sr er'' xs)(rep_i_sr er'' ys). 
  rewrite substrate_prod_of_rel //.
  move=> /setX_P [px Px Qx] /setX_P [py Py Qy] WW.
  move: (compatible_ext_to_prod_inv er er' px Px Qx py Py Qy WW).
  by move/(related_rr_P er'' xs ys). 
exists h;split => //;split =>//;split =>//.
move=> y; rewrite th; move /setX_P=> [py Py Qy].
have p1: (inc (J (rep (P y)) (rep (Q y))) (substrate r'')).
  rewrite /r'' substrate_prod_of_rel //;apply:setXp_i; fprops.
set (x:= class r'' (J (rep (P y)) (rep (Q y)))).
have xq: inc x (quotient r'') by rewrite /x; fprops.
have rxs: inc (rep x) (substrate r'') by fprops.
move: (related_rep_class er'' p1).
move: rxs; rewrite substrate_prod_of_rel //;  move /setX_P => [ pr Pr Qr].
move: p1; rewrite substrate_prod_of_rel //; move /setXp_P=>  [Py' Qy'].
rewrite -/x; move /(related_prod_of_relP1)=> [u [v [e1 e2 e3]]].
exists x; rewrite ?sh // /h foqc_V //- pr - py /f'' ext_to_prod_rel_V //. 
have <-: (P y = class r (P (rep x))). 
  apply: is_class_pr =>//; rewrite e1; aw.
  by move:Py => /(setQ_P er) [_ ->]; apply /(class_P er).
have <- //: (Q y = class r' (Q (rep x))) . 
  apply: is_class_pr =>//; rewrite e1; aw.
  by move:Qy => /(setQ_P er') [_ ->]; apply /(class_P er').
Qed.


Section LeastEquiv.

Definition eqv_smaller (R: relation) r :=
  forall x y, R x y -> related r x y.     

Definition eqv_smallest E R :=
  intersection (Zo (equivalences E) (eqv_smaller R)).

Lemma eqv_smallest_prop E R (r := (eqv_smallest E R)):
  (forall x y, R x y -> inc x E /\ inc y E) ->
  equivalence_on r E /\ eqv_smaller R r.
Proof.
move => ha.
have hb:equivalence r.
  apply: setIrel_equivalence.
  by move => t /Zo_P [/equivalencesP []].
have ne:nonempty (Zo (equivalences E) (eqv_smaller R)).
  exists (coarse E); apply/Zo_P; split.
    apply: inc_coarse_all_equivalence_relations.
  by move => x y /ha /coarse_related.
have sr: substrate r = E.
  by apply:(setIrel_sr ne) => t /Zo_P [/equivalencesP []] // [].
split => //  x y rxy.
by apply/(setI_P ne) => s /Zo_P [uu]; apply.
Qed.

Lemma eqv_smallest_prop2 E (R: relation) r:
  (forall x y, R x y -> inc x E /\ inc y E) ->
  equivalence_on r E -> eqv_smaller R r ->
  (forall r', equivalence_on r' E -> eqv_smaller R r' -> sub r r') ->
  r = eqv_smallest E R.
Proof.
move => ep er sm h.
set F := (Zo (equivalences E) (eqv_smaller R)).
have ha: inc r F by apply/Zo_P; split => //; apply/equivalencesP.
move:(eqv_smallest_prop ep) => [hb hc]; move:(h _ hb hc) => sub1.
by apply: extensionality => //; apply:setI_s1.
Qed.

Lemma eqv_smallest_sym E (R: relation):
  (forall x y, R x y -> inc x E /\ inc y E) ->
  (eqv_smallest E R) = (eqv_smallest E (fun x y => R x y \/ R y x)).
Proof.
move => ha.
set R' := (fun x y : Set => R x y \/ R y x).
rewrite /eqv_smallest.
congr intersection; apply: Zo_exten1 => s /equivalencesP[eq ss].
split => h x y.
    case; [ by apply:h | move/h ; apply:(proj44 eq)].
by move=> rxy; apply:h; left.
Qed.

Lemma eqv_smallest_refl E (R: relation)
      (R' :=  fun x y => R x y \/ (inc x E /\ x = y)):
  (forall x y, R x y -> inc x E /\ inc y E) ->
  (eqv_smallest E R) = (eqv_smallest E  R').
Proof.
move => ha.
rewrite /eqv_smallest.
congr intersection; apply: Zo_exten1 => s /equivalencesP[eq ss].
split => h x y.
  case; [ by apply: h | by move => [xE <-];  apply:(proj42 eq); rewrite ss ].
by move=> rxy; apply:h; left.
Qed.


(** A chain is a list with at least two elements; it has a head and a tail. *)

Inductive chain:Type :=
  chain_pair: Set -> Set -> chain
 | chain_next: Set -> chain -> chain. 

Definition chain_head x :=
  match x with chain_pair u _ => u | chain_next u _ => u end.
 
Fixpoint chain_tail x :=
  match x with chain_pair _ u => u | chain_next _ u => chain_tail u end.

Fixpoint concat_chain x y : chain :=
  match x with chain_pair u _ => chain_next u y 
| chain_next u v => chain_next u  (concat_chain v y) end.

Lemma head_concat x y:
  chain_head (concat_chain x y) = chain_head x.
Proof. by case: x.  Qed.

Lemma tail_concat x y: 
  chain_tail (concat_chain x y) = chain_tail y.
Proof. by elim: x. Qed.



(** We may revert a chain *)
Fixpoint reconc_chain (x y:chain)  :chain:=
  match x with chain_pair u v => chain_next v (chain_next u y)
   | chain_next u v => reconc_chain v (chain_next u y) end.

Lemma tail_reconc x y: chain_tail (reconc_chain x y) = chain_tail y.
Proof.  by move: x y; elim=> [a b y | a c r] // y; by rewrite r. Qed.

Lemma head_reconc x y:chain_head (reconc_chain x y) = chain_tail x.
Proof. move: x y; elim=> [a b y | a c r] // y; by rewrite r. Qed.


Definition chain_reverse x:=
  match x with chain_pair u v => chain_pair v u
    | chain_next u v =>
      match v with chain_pair u' v' => chain_next v' (chain_pair u' u)
        | chain_next u' v' => reconc_chain v' (chain_pair u' u)
      end end.

Lemma head_reverse x: chain_head (chain_reverse x) = chain_tail x.
Proof. elim x=>// y;elim =>// P c h h1 /=; apply: head_reconc.
Qed.

Lemma tail_reverse x: chain_tail (chain_reverse x) = chain_head x.
Proof. elim: x =>// y;elim =>// P c h h1 /=; apply: tail_reconc. Qed.



Variables (R:relation) (E:Set).
Hypotheses (A1: reflexive_re R E)(A2: symmetric_r R)
  (A3: forall x y, R x y -> inc x E).


Fixpoint chained_r x :=
  match x with chain_pair u v => R u v 
    | chain_next u v => R u (chain_head v) /\ chained_r v
 end.


Lemma chained_concat x y:
  chained_r x -> chained_r y -> chain_tail x = chain_head y ->
  chained_r (concat_chain x y).
Proof. 
move=> cx cy txhy;elim: x cx txhy => [a b cp ct| a c r cp ct].
  split=>//; by  rewrite -ct //.
by move: cp => [pa pb];split; [rewrite head_concat | apply: r].
Qed.

Lemma chained_reconc x y: chained_r x -> chained_r y -> 
  R (chain_head y) (chain_head x) ->  chained_r (reconc_chain x y).
Proof. 
move: x y; elim => [a b y c cy | P c r]=>//=; auto.
by move=> y [rPh cc] cy RhyP; apply: r=>//; split => //; apply: A2.
Qed.


Lemma chained_reverse x: chained_r x -> chained_r (chain_reverse x).
Proof. 
elim: x; first by move=> a b;apply:A2.
move=> a; elim; first by move => b c /= _ [/A2 h2 /A2 h3]. 
move=> b c hr hr1 /= [/A2 Rab [Rbc cc]].
by apply: chained_reconc. 
Qed.

Definition chain_related x y := exists c:chain, 
  [/\ chained_r c, chain_head c = x  & chain_tail c = y].

Definition chain_equivalence := graph_on chain_related E.

Lemma chain_related_re x:
  inc x E <-> chain_related x x.
Proof.
split.
  by move=> xE; exists (chain_pair x x);split => //;  apply /A1.
case; case => a b [h <- _]; [by  apply: (A3 h) | by  case:h => /A3 ].
Qed.
  
Lemma chain_equivalence_eq: equivalence_on chain_equivalence E.
Proof.
split; last by apply: graph_on_sr => x /chain_related_re.
apply: equivalence_from_rel.
split.
  move=> x y [c [cc hcx tcy]].
  exists (chain_reverse c); split.
  + by apply: chained_reverse.
  + by rewrite head_reverse.
  + by rewrite tail_reverse.
move => y x z [c [cc hcx tcy]][c' [cc' hcy  tcz]].
exists (concat_chain c c'); split => //.
    apply: chained_concat=>//;  ue. 
  by rewrite head_concat.
by rewrite tail_concat.
Qed.


Lemma chain_equivalence_is_smallest:
  chain_equivalence = eqv_smallest E R.
Proof.
apply:eqv_smallest_prop2.
+ move => x y rxy;split; [exact: (A3 rxy)| exact (A3 (A2 rxy))].
+ exact chain_equivalence_eq.
+  move => x y Rxy;apply/graph_on_P1; split.
   - apply: (A3 Rxy).
   - apply: (A3 (A2 Rxy)).
   - exists (chain_pair x y); split => //.
+ move => r' [er' _] p q. 
  have aux:(forall w, chained_r w -> inc (J (chain_head w) (chain_tail w)) r').
    elim => [a b | a c h [aux cc]] //=; first by apply: p.
    move: (h cc)(p _ _ aux) => r1 r2; apply:(proj43 er' _ _ _ r2 r1).
  move /Zo_P => [pp  [c [cc hcx htx]]].
  have <-: (J (P q)(Q q) = q) by move/setX_P: pp => [pp _].
  by rewrite -hcx -htx ; apply: aux.
Qed.

End LeastEquiv.

End Relation.
Export Relation.
