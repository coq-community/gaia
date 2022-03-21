(** * Theory of Sets : Exercises
  Copyright INRIA (2009-2012 2018) Apics/Marelle Team (Jose Grimm).
*)
(* $Id: ssete2.v,v 1.4 2018/09/04 07:58:00 grimm Exp $ *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From gaia Require Export sset13b ssete1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module Exercise2.


(** ** Section 1 *) 

(** Exercise 1.1: Example of a non-order  *)

Lemma Exercise1_1 r (E:= substrate r)
     (R := fun x y => [/\ inc x E, inc y E & glt r x y]) :
    order r ->  (exists x y, x <> y /\ related r x y) ->
    [/\ transitive_r R, antisymmetric_r R & ~(reflexive_rr R)].
Proof. 
move=> or [x [y [xy rxy]]]; split => //.
+ move => a b c [aE bE ab] [_ cE bc]; split => //; order_tac.
+ move => a b [aE bE [ab nab]] [_ _ ba]; order_tac.
+ have sxy : R x y by hnf; rewrite /E;split => //; try substr_tac; split.
  by move => ref; move: (ref _  _ sxy) => [_ [_ _ [_]]].
Qed.

(** ---- Exercise 1.2: Quotient of a preorder relation [r] by an equivalence [s]

We start with some auxiliary definitions 
*)

Definition ne_substrate r := nonempty (substrate r).


Definition Ex1_2_strong_l r s:=
  (forall x x' y,  gle r x y -> related s x x' -> gle r x' y).
Definition Ex1_2_strong_r r s:=
   (forall x y y',  gle r x y -> related s y y' -> gle r x y').
Definition Ex1_2_hC r s:=
  forall x y x', gle r x y -> related s x x' -> exists2 y',
    related s y y' & gle r x' y'.

Definition Ex1_2_hC' r s:=
  forall x y z, gle r x y -> gle r y z -> related s x z -> related s x y.
Definition Ex1_2_hD r f :=
   forall x y x', gle r x y -> inc x' (source f) -> Vf f x = Vf f x' ->
    exists y', [/\ inc y' (source f), gle r x' y' & Vf f y = Vf f y'].
Definition Ex1_2_hD' r r' f :=
  forall x y, inc x (source f) -> inc y (source f) ->
    gle r' (Vf f x) (Vf f y) -> exists x' y', 
     [/\ Vf f x = Vf f x', Vf f y = Vf f y' & gle r x' y'].

Definition preorder_quo_axioms r s:=
  [/\ preorder r, equivalence s &  substrate s = substrate r].
Definition weak_order_compatibility r s:=
  preorder_quo_axioms r s /\ Ex1_2_hC r s.

Definition increasing_pre f r r':=
 [/\ preorder r, preorder r', function_prop f (substrate r) (substrate r')
  & fincr_prop f r r'].

Definition preorder_isomorphism f r r' := 
 [/\ preorder r, preorder r', bijection_prop f (substrate r) (substrate r')
  & fiso_prop f r r'].

(** We can always endow the quotient with a preorder.*)

Definition quotient_order_r r s X Y :=
  [/\ inc X (quotient s), inc Y (quotient s) &
  forall x, inc x X -> exists2 y, inc y Y & gle r x y].

Definition quotient_order r s := graph_on (quotient_order_r r s) (quotient s).

Lemma Exercise1_2a r s:
  preorder_quo_axioms r s -> preorder_r (quotient_order_r r s).
Proof. 
move=> [ [gr rr tr] es sssr]; split.
  move=> a b c [aq bq abp] [_ cq bcp];split => //.
  move => x /abp [y /bcp [z zc yz] xy]; ex_tac; apply: tr xy yz.
move=> a b [aq bq abp]. 
by split; split => // x xs; ex_tac; apply: rr; rewrite - sssr;
  apply: (inc_in_setQ_sr es xs).  
Qed.

Lemma quotient_orderP r s x y:
  related (quotient_order r s) x y <-> quotient_order_r r s x y.
Proof.
split; [by move /Zo_hi; aw | move => h; move: (h) => [pa pb _] ].
by apply: Zo_i; aw; trivial; apply /setXp_P.
Qed.

Lemma quotient_is_preorder r s:
  preorder_quo_axioms r s ->  preorder (quotient_order r s).
Proof.
by move=> h; apply: preorder_from_rel; apply: Exercise1_2a.
Qed.

Lemma substrate_quotient_order r s:
  preorder_quo_axioms r s ->  substrate (quotient_order r s) = quotient s.
Proof. 
move=> ax;move: (quotient_is_preorder ax)=> pq.
set_extens x.
  by move /(preorder_reflexivity _ pq) /quotient_orderP => [xs _]. 
move=> xs; apply  /(preorder_reflexivity _ pq)  /quotient_orderP.
have [po es ssr] := ax.
split => //y yx; ex_tac; apply /(preorder_reflexivity _ po).
rewrite - ssr; apply: (inc_in_setQ_sr es yx xs).
Qed.

(** Strong compatibility implies weak compatibility. 
Weak compatibilility says that [g: E/S -> F] is increasing if and only if it 
composition with the canonical projection is increasing [E -> F]. *)

Lemma Exercise1_2b1 r s g r':
  preorder_quo_axioms r s ->
  function g -> quotient s = source g ->
  increasing_pre (g \co (canon_proj s)) r r' ->
  increasing_pre g (quotient_order r s) r'.
Proof.
move=> [_ es sssr] fg qs [pr pr' [fc sq sr'] ale].
split => //.
    by apply: quotient_is_preorder.
  by hnf; aw;rewrite substrate_quotient_order//; split => //; rewrite - sr'; aw.
have cc: (g \coP (canon_proj s)) by split;fprops; aw; ue.
move => x y /quotient_orderP [xq yq h].
have [y0 y0y aux] := (h _ (setQ_repi es xq)).
move:(arg1_sr aux)(arg2_sr aux); rewrite - sssr => h2 h1.
have h0: source (canon_proj s) = substrate s by aw.
move: (ale _ _ aux); rewrite !compfV //; try ue; rewrite !canon_proj_V //.
rewrite - (class_eq1 es (related_rep_in_class es yq y0y)).
by rewrite (class_rep es xq) (class_rep es yq).
Qed.

Lemma strong_order_compatibility r s:
  preorder_quo_axioms r s -> Ex1_2_strong_l r s ->
  weak_order_compatibility r s.
Proof. 
move=> h1 h2; split => //.
move: h1 => [po eq ss] x y x' xy sxx'; exists y; last by apply: h2 xy sxx'.
apply: reflexivity_e => //;red in xy;rewrite ss; substr_tac. 
Qed.

Lemma compatibility_proj_increasing r s:
  preorder_quo_axioms r s ->
  (weak_order_compatibility r s <->
    increasing_pre (canon_proj s) r (quotient_order r s)).
Proof.
move=> ax; move: (quotient_is_preorder ax) => pq.
have [pr es sr] := ax.
rewrite /increasing_pre - sr substrate_quotient_order //; aw.
have gs: sgraph s by fprops.
split.
  move=> [_ woc]; split;fprops; first by split; aww.
  move=> x y lexy.
  move:(arg1_sr lexy) (arg2_sr lexy); rewrite - sr => xss yss.
  apply /quotient_orderP; rewrite /quotient_order_r !canon_proj_V //.
  split;fprops.
  move=> z /(class_P es) /(woc _ _ _ lexy) [y' /(class_P es) syy' rzy'];ex_tac.
move=>[fc [_ _ _ _ ci]]; split => //.
move=> x y x' rxy /(class_P es) sxx'.
move:(arg1_sr rxy) (arg2_sr rxy); rewrite - sr => xss yss.
move /quotient_orderP:(ci _ _ rxy) => [_ _].
rewrite /quotient_order_r !canon_proj_V// => h.
by move: (h _ sxx') => [y'] /(class_P es) pa pb; exists y'.
Qed.

(** The equivalence [ P x = P y] is weakly compatible with order-product; 
In general it is not strongly compatible 
(unless all elements of the second set are related by the preorder). *)

Lemma Exercise1_2c1 r1 r2:
  preorder r1 -> preorder r2 ->
  weak_order_compatibility (order_product2 r1 r2)
  (first_proj_eq (substrate r1) (substrate r2)).
Proof.
move:(first_proj_equivalence (substrate r1) (substrate r2)) => [q1 q2].
move=> p1 p2; split;first split => //.
- by apply: order_product2_preorder.
- by rewrite q2 order_product2_sr1.
- move=> x y x' /order_product2_P [/setX_P [px px1 qx2] s2 [rp rq]].
  move /first_proj_eq_related_P => [_ s3 sp].
  move: (s2)(s3) => /setX_P [py py1 qy2] /setX_P [px' px'1 qx'2].
  exists (J (P y) (Q x')).
    by apply /first_proj_eq_related_P; saw; apply /setXp_P.
  apply /order_product2_P; saw; first by apply /setXp_P. 
  by split => //; [ ue | apply /preorder_reflexivity].
Qed.

Lemma Exercise1_2c2 r1 r2 (p :=first_proj_eq (substrate r1) (substrate r2)) :
  preorder r1 -> preorder r2 -> ne_substrate r1 ->
  (Ex1_2_strong_l (order_product2 r1 r2) p \/
   Ex1_2_strong_r (order_product2 r1 r2) p) ->
  r2 = coarse (substrate r2).
Proof.
move=> p1 p2 [x xr1] cp.
have p3: (preorder (order_product2 r1 r2)) by apply: order_product2_preorder. 
set_extens t => ts.
  apply /setX_P;split; first exact:(proj31 p2 _ ts); substr_tac. 
move/setX_P: ts => [pt ps qs].
set X := ((substrate r1) \times (substrate r2)).
have x1p:inc (J x (P t)) X by rewrite /X; fprops.
have x2p:inc (J x (Q t)) X by rewrite /X; fprops.
have rp: forall s, inc s X -> gle (order_product2 r1 r2) s s.
  by move => s H; apply/(preorder_reflexivity _ p3);rewrite order_product2_sr1.
move: (rp _ x1p) (rp _ x2p) => r11 r22.
have s12: (related p (J x (P t)) (J x (Q t))).
  apply /first_proj_eq_related_P; saw.
have s21: (related p (J x (Q t)) (J x (P t))). 
  apply /first_proj_eq_related_P; saw.
rewrite - pt; case: cp => cp.
  by move: (cp _ _ _ r22 s21) => /order_product2_P [_ _ [_] ]; aw.
  by move: (cp _ _ _ r11 s12) => /order_product2_P [_ _ [_] ]; aw.
Qed.

(** We define here a preorder isomorphism. If [P = f \co phi ], where [phi] is 
the canonical projection then [f] is an isomorphism *)

Lemma Exercise1_2c4 r1 r2 f
   (s := first_proj_eq (substrate r1) (substrate r2))
   (r:= order_product2 r1 r2) :
  function_prop f (quotient s) (substrate r1) ->
  preorder r1 -> preorder r2 -> ne_substrate r2 ->
  f \co (canon_proj s)= first_proj (product (substrate r1) (substrate r2)) ->
  preorder_isomorphism f (quotient_order r s) r1.
Proof. 
rewrite/function_prop; set (E1:= substrate r1); set (E2:= substrate r2). 
move=> [ff sf tf] p1 p2 [z zE2] cp.
have sr: substrate r = E1 \times E2.
  by rewrite /r order_product2_sr1.  
have [es ss] := (first_proj_equivalence E1 E2).
have cpa: f \coP (canon_proj s) by saw; apply: canon_proj_f.
have pr: preorder r by rewrite /r; apply: order_product2_preorder.
have sc: (source (canon_proj s) = E1 \times E2) by aw.
have pqa: preorder_quo_axioms r s by split => //; ue.
have sq: substrate (quotient_order r s) = source f.
  by rewrite substrate_quotient_order.
have aux: forall x, inc x (source f) -> 
  [/\ inc x (quotient s), inc (rep x) (substrate s) & P (rep x) = Vf f x].
  move => x xs.
  have xqs: inc x (quotient s) by rewrite - sf.
  have pa: inc (rep x) (substrate s) by fprops.
  move:(pa) (pa); rewrite ss => pc; rewrite - sc => rsx.
  split => //; move: (compfV cpa rsx); rewrite cp  first_proj_V //.
  by rewrite canon_proj_V // (class_rep es xqs).
have bf: bijection f.
  split; split => //.
    move => x y xs ys sW.
    move:(aux _ xs)(aux _ ys) => [pa b pc] [qa qb qc].
    apply /(related_rr_P es pa qa).
    by apply /first_proj_eq_related_P;split => //; try ue; rewrite pc qc.
  rewrite tf => y ye1.
  have Js: (inc (J y z) (source (canon_proj s))) by ue. 
  have ->: (source f = target (canon_proj s)) by aw. 
  exists (Vf (canon_proj s) (J y z)); fprops.
  by rewrite - (compfV cpa Js) cp first_proj_V //; [ aw| ue].
split => //; [by apply: quotient_is_preorder => //; ue | move=> x y xsf ysf].
move:(aux _ xsf)(aux _ ysf) => [pa b pc] [qa qb qc].
have rx:=(setQ_repi es pa).
split.
move/quotient_orderP => [_ _ h].
  move: (h _ rx) => [w wy /order_product2_P [rpx wp [le1 le2]]].
  have yc := (is_class_pr es wy qa).
  move: (related_rep_class es (inc_in_setQ_sr es wy qa)).
  by rewrite - yc - pc - qc; move /first_proj_eq_related_P => [_ rys <-].
move=> h; apply/quotient_orderP; split => // w wx.
move: (inc_in_setQ_sr es wx pa); rewrite ss => wpr.
move/setX_P: (wpr) => [pw Pw Qw].
have JP: (inc (J (Vf f y) (Q w)) ((substrate r1) \times (substrate r2))).
  apply /setXp_P;split => //; rewrite -/E1 -tf; Wtac.
exists (J (Vf f y) (Q w)).
  rewrite - {2} (class_rep es qa); apply /(class_P es).
  apply /first_proj_eq_related_P; saw; ue.
apply /order_product2_P; saw;split; last by apply: (proj32 p2).
have xc:= (is_class_pr es wx pa).
move:(related_rep_class es (inc_in_setQ_sr es wx pa)).
rewrite -xc; move /first_proj_eq_related_P => [_ _ ->];ue.
Qed.

(** We give here a sufficient condition for the quotient to be an order *)


Lemma Exercise1_2d r s:
  equivalence s -> order r -> substrate s = substrate r ->
  Ex1_2_hC' r s ->
  order (quotient_order r s).
Proof. 
move => es or ss qoa.
have pr:= (order_preorder or).
have pqa: preorder_quo_axioms r s by [].
have [p1 p2 p3] := (quotient_is_preorder pqa).
split => //.
suff sxy: forall x y, related (quotient_order r s) x y ->
   related (quotient_order r s) y x -> sub x y.
  by move=> x y xs ys; apply: extensionality; apply: sxy.
move=> x y /quotient_orderP  [xs ys q1] /quotient_orderP [_ _ q2] t tx.
move: (q1 _ tx) => [z zy tz]; move: (q2 _ zy) => [w wt zw]. 
have tw: (related s t w). 
  by apply /(in_class_relatedP es); exists x; split => //; apply /(setQ_P es).
rewrite (is_class_pr es zy ys);apply /(class_P es); apply: (symmetricity_e es).
exact: (qoa _ _ _ tz zw tw).
Qed.

(** Bourbaki says: there are examples of totally ordered sets [E] with four 
elements such that the quotient is ordered, and none of the two conditions is 
satisfied. We first show that [E/S] is isomorphic to a subset of [E] 
(two classes compare the same as their greatest element). If [a < b < c], the 
equivalence relation that relates [a] and [c], but is otherwise trivial 
satisfies none of the two conditions.*)

Lemma Exercise1_2e1 r s:
  equivalence s -> total_order r -> substrate s = substrate r ->
  finite_set (substrate r) ->
  total_order (quotient_order r s).
Proof.
move => eqs tor ssr fs.
have or := (proj1 tor).
have pr := (order_preorder or).
have [p1 p2 p3] := (quotient_is_preorder (And3 pr eqs ssr)).
pose gr x := (the_greatest (induced_order r x)).
pose A x := (inc (gr x) x /\ forall y, inc y x -> gle r y (gr x)).
have gp: forall x, sub x (substrate r) -> nonempty x -> A x.
  move => x xsr nex.
  have h := (finite_subset_torder_greatest tor (sub_finite_set xsr fs) nex xsr).
  have [pa' pb'] := (iorder_osr or xsr).
  case: (the_greatest_pr pa' h); rewrite -/ (gr x) pb' => pa pb.
  split => // y yx; exact: (iorder_gle1 (pb _ yx)).
have gp1: forall x, inc x (quotient s) -> A x.
  move => x xq; apply: gp (setQ_ne eqs xq).
  move => t tx; rewrite - ssr; apply: (inc_in_setQ_sr eqs tx xq).
have paP: forall x y, related (quotient_order r s) x y  <->
  [/\ inc x (quotient s),inc y (quotient s) &  gle r (gr x) (gr y)].
  move => x y; apply: (iff_trans (quotient_orderP r s x y)).
  split; move=> [pa pb pc];move: (gp1 _ pa) (gp1 _ pb)=> [qa qb][qc qd].
    split => //; move: (pc _ qa) => [z /qd le2 le1]; order_tac.
  split => //t tx; ex_tac; move: (qb _ tx) => le1; order_tac.  
split.
  split => // x y /paP [xq yq le1] /paP [_ _ le2].
  have sv: (gr x) = (gr y) by order_tac.
  move: (gp1 _ xq) (gp1 _ yq) => [xs _] [ys _].
  by rewrite (is_class_pr eqs xs xq)  (is_class_pr eqs ys yq) sv.
rewrite (substrate_quotient_order (And3 pr eqs ssr)) => x y xsr ysr.
move: (proj1 (gp1 _ xsr)) (proj1 (gp1 _ ysr)) => xs ys.
move: (inc_in_setQ_sr eqs xs xsr); rewrite ssr => x1.
move: (inc_in_setQ_sr eqs ys ysr); rewrite ssr => y1.
by case: (proj2 tor _ _ x1 y1) =>h; [left | right]; apply /paP.
Qed.

Lemma Exercise1_2e2 r a b c (E:= substrate r)
  (s := (diagonal E) \cup (doubleton (J a c) (J c a))):
  order r -> glt r a b -> glt r b c ->
  [/\ equivalence s, substrate s = substrate r,
  ~ ( weak_order_compatibility r s) &
  ~ ( Ex1_2_hC' r s)].
Proof.
move => or lab lbc.
have asr: inc a (substrate r) by order_tac.
have csr: inc c (substrate r) by order_tac.
have dp := (diagonal_i_P E); have dpi:= (diagonal_pi_P E).
have gs: sgraph s by move => t /setU2_P [ /dp [] // | /set2_P [] ->]; fprops.
have pa: forall u v, inc (J u v) s -> (inc u E /\ inc v E).
  move => u v;case/setU2_P; first by move/dp; aw; move=> [_ xE <-].
  by case /set2_P => h;rewrite (pr1_def h) (pr2_def h).
have pb: forall t, inc t E -> related s t t.
  by move => t te; apply /setU2_P; left; apply/dpi.
have sr: substrate s = E.
  set_extens t; last by move /pb => h; substr_tac.
  by move /(substrate_P gs);case; move => [y /pa [tE tE']]. 
have sac: related s a c by apply /setU2_P; right; fprops.
have sca: related s c a by apply /setU2_P; right; fprops.
have es: equivalence s.
  split => //; first by red; rewrite sr => t; apply pb.  
    move => x y z yx xz.
    case/setU2_P:(yx); [ by move/dp=> [_ _]; aw => -> | move => h1].
    case/setU2_P:(xz); [ by move/dp=> [_ _]; aw => <- | move => h2].
    case/set2_P: h1 => h1; rewrite ? (pr1_def h1) ? (pr2_def h1);
    case/set2_P:h2 => h2; rewrite ? (pr1_def h2) ? (pr2_def h2);fprops.
  move => x y xy;apply /setU2_P; case/setU2_P: xy. 
    by move/dp;aw; move=> [_ ha <-]; left;apply /dpi.
   case/set2_P => h; rewrite (pr1_def h) (pr2_def h);fprops.
move:(proj2 lab) (proj2 lbc) => nab nbc; move:(nesym nab) => nba.
split => //.
  move => [_ pc]; move: (pc a b c (proj1 lab) sac) => [z].
  case /setU2_P; first by move /dpi => [_ <-] => cb; order_tac.  
  by case /set2_P => /pr1_def.
move => hh; move: (hh a b c (proj1 lab) (proj1 lbc) sac).
by case /setU2_P; [ move /dpi => [_ ] | case /set2_P => /pr2_def].
Qed.

Lemma Exercise1_2e4 r: total_order r -> 
  \3c <=c cardinal (substrate r) ->
  exists a b c,  glt r a b /\ glt r b c.
Proof.
move => [or tor] /cardinal_ge3; rewrite /glt.
move => [a [b [c [ae be ce [ab bc ac]]]]].
case:(tor _ _ ae be) => h1; case: (tor _ _ be ce) => h2; first by exists a,b,c.
    case: (tor _ _ ae ce) => h3; [ exists a,c, b |  exists c, a,b ]; fprops.
  case: (tor _ _ ae ce) => h3; [ exists b,a,c | exists b,c, a]; fprops.
exists c, b, a; fprops.
Qed.

Lemma Exercise1_2e5 r:
  total_order r -> finite_set (substrate r) ->
  \3c <=c cardinal (substrate r) ->
  exists s, 
  [/\ equivalence s, substrate s = substrate r,
    total_order (quotient_order r s),
  ~ ( weak_order_compatibility r s) &
  ~ ( Ex1_2_hC' r s) ].
Proof.   
move => tor fso /(Exercise1_2e4 tor) [a [b [c [ab bc]]]].
move: (Exercise1_2e2 (proj1 tor) ab bc).
set s :=  _\cup  _; move => [es ss pa pb]; exists s;split => //.
by apply:  Exercise1_2e1.
Qed.

(** Consider the equivalence induced by an increasing function [f:E -> F]. 
The second condition is alwats true; the first is equivalent to some condition 
[CC]. If [f = g \co phi] is the canonical decomposition then [g: E/S -> f(E)] 
is an isomorphism iff [CC] and [DD] hold *)


Lemma Exercise1_2f1 r r' f: increasing_fun f r r' ->
  Ex1_2_hC' r (equivalence_associated f).
Proof. 
move => [or or' [ff sr sr'] icf].
move=> x y z xy yz.
move:(icf _ _ xy)(icf _ _ yz) => sa sb.
move/(ea_relatedP ff) => [_ _ sw]; rewrite - sw in sb.
apply /(ea_relatedP ff); rewrite sr;  split => //; order_tac. 
Qed.

Lemma Exercise1_2f2 r r' f: increasing_fun f r r' ->
  (weak_order_compatibility r (equivalence_associated f) <->
  (Ex1_2_hD r f)).
Proof. 
move => [or or' [ff sr sr'] icf].
split.
  move=> [[pr ea sea] ch] x y x' xy x'sf sW.
  have aux: (related (equivalence_associated f) x x').
    apply /ea_relatedP => //; split => //; rewrite sr; order_tac.
  move: (ch _ _ _ xy aux) => [y' /(ea_relatedP ff) [pa pb pc] x'y']. 
  by exists y'.
have [ee se]:=(graph_ea_equivalence ff).
move=> ch; split; first split.
+ by apply: order_preorder.
+ done.
+ by rewrite se.
+ move=> x y y' xy /(ea_relatedP ff)  [xsf ysf sv].
  move: (ch _ _ _ xy ysf sv) => [z [zf y'z sv1]]. 
  exists z=> //; apply /(ea_relatedP ff);split => //; rewrite sr; order_tac.
Qed. 

Lemma Exercise1_2f3 r r' f g (s := (equivalence_associated f)):
  increasing_fun f r r' ->
  composable g (canon_proj s) -> f = compose g (canon_proj s) ->
  (order_morphism g (quotient_order r s) r' 
    <-> (Ex1_2_hD r f  /\ Ex1_2_hD' r r' f)).
Proof. 
move => incf cgf fc.
have qoa:= (Exercise1_2f1 incf).
move: incf => [or or' [ff sr sr'] icf].
have [es ss]:= (graph_ea_equivalence ff).
have sssr: substrate s = substrate r by rewrite ss.
have pr: preorder r by apply: order_preorder.
have qp: forall x, inc x (quotient s)  -> 
   (inc (rep x) (source f) /\ Vf f (rep x) = Vf g x). 
  move=> x xq; move: (rep_i_sr es xq) => rxs.
  split; first by rewrite  - ss.
  move: (canon_proj_V rxs); rewrite class_rep // => cpv.
  have rsc: inc (rep x) (source (canon_proj s)) by aw.
  by rewrite - {2} cpv - compfV // - fc.
have bpP :forall x, inc x (quotient s) -> forall a,
   (inc a x <-> [/\ inc (rep x) (source f), inc a (source f) &
     Vf f (rep x) = Vf f a]).  
  move=> x xq a; split.
    by move=> ax; move: (related_rep_in_class es xq ax); move /(ea_relatedP ff).
  by move=> h;rewrite -(class_rep es xq); apply /(class_P es) /(ea_relatedP ff).
have ax: preorder_quo_axioms r s by split.
split => om.
  have aux: forall y, inc y (source f) ->  [/\ inc (class s y) (quotient s), 
   Vf f (rep (class s y)) = Vf g (class s y) & Vf f (rep (class s y)) = Vf f y].
    move => y ; rewrite  - ss => ys.
    have csyq:= (inc_class_setQ ys);have p2 := proj2 (qp _ csyq).
    by move /(bpP _ csyq): (inc_itself_class es ys) => [_ _ p5].
  have p1: forall x y, inc x (source f) -> inc y (source f) ->
      gle r' (Vf f x) (Vf f y) -> 
      exists y', [/\ inc y' (source f),  gle r x y' & Vf f y = Vf f y']. 
    move=> x y xsf ysf.  
    have xc: (inc x (class s x)) by apply:inc_itself_class=>//;rewrite ss.
        move: (aux _ xsf)(aux _ ysf)  => [csxq p2 p5][csyq p2' p5'].
    move: om => [q1 q2 [q3 q4 q5]].
    rewrite /fiso_prop q4 substrate_quotient_order // => q6P.
    rewrite -p5  p2 -p5' p2' => /(q6P _ _ csxq csyq) /quotient_orderP [_ _ q7].
    move /q7: xc => [u ucy xu]; rewrite - p2'; exists u.
    by move: ucy => /(bpP _ csyq) [q8 q9 q10]. 
 split.
    move => x y x' xy x'sf sW.
    move: (icf _ _ xy); rewrite sW => fxy.
    have yc: (inc y (source f)) by rewrite sr; order_tac.
    apply: p1 x'sf yc fxy. 
  move=> x y xsf ysf leW;move: (p1 _ _  xsf ysf leW) => [x0 [p0 p2' p3]].
  by exists x; exists x0.
move:om=> [CCt DDt].
have oq: (order (quotient_order r s)) by  apply: Exercise1_2d.
have sg: (source g = quotient s) by move: cgf => [_ _ ->]; aw. 
have tg: substrate r' = target g by rewrite - sr' fc; aw.  
have sqo: substrate (quotient_order r s) = source g.
  by rewrite sg substrate_quotient_order.
have icgP: (forall x y, inc x (source g) -> inc y (source g) ->
    (gle (quotient_order r s) x y <-> gle r' (Vf g x) (Vf g y))). 
  rewrite sg;move=> x y xsg ysg.
  move: (qp _ xsg) (qp _ ysg) => [rxs <-][rys <-]; split.
    move /quotient_orderP => [_ _ aux]. 
    move: (aux _ (setQ_repi es xsg)) => [z /(bpP _ ysg) [q1 q2 q3] lerxz].
    by rewrite q3; apply: icf.
  move => h; apply /quotient_orderP; split => // z /(bpP _ xsg) [p4 p5 p6].
  move: (DDt _ _ rxs rys h) => [x' [y' [p1 p2 p3]]].
  rewrite p1 in p6.
  move: (CCt _ _ _ p3 p5 p6) => [t [p7 p8 p9]].
  exists t=> //;apply /(bpP _  ysg); split => //; ue.
have fg //: function g by fct_tac.
Qed.

(** ---- Exercise 1.3: properties of ordinal sum *)


Section Exercise1_3a.
Variables r g: Set.
Definition E13_F:= order_sum r g.
Definition E13_sF:= sum_of_substrates g.
Definition E13_lam := second_proj E13_sF.
Definition E13_S:= equivalence_associated (second_proj E13_sF).
Definition E13_H1:= orsum_ax r g.
Definition E13_H2:=  sgraph g /\ allf g ne_substrate.


(** We know that [order_sum] is an ordering under condition [ E13_H1]. 
Let [E(i)] denote the [i]-th sustbrate and [F(i)] its image in the disjoint 
union [E13_sF]. 
If [ E13_H2] holds, then [F(i)] form a partition of the disjoint union; 
moreover the second projection [Q] (more precisely [E13_lam]) is surjective. *) 


Lemma Exercise1_3a0: function E13_lam.
Proof. by apply: second_proj_f. Qed.

Lemma Exercise1_3a1: sgraph E13_sF.
Proof. 
move=> t /setUb_P [y]; rewrite  /fam_of_substrates ! Lgd => yd.
by rewrite /disjointU_fam LgV; [ case /indexed_P | aw].
Qed.

Lemma Exercise1_3a2: surjection E13_lam.
Proof. 
split; first by apply: Exercise1_3a0.
rewrite /E13_lam {1 2}/second_proj => y; aw =>/(rangeP Exercise1_3a1) [x h]. 
by ex_tac; rewrite second_proj_V //; aw.
Qed.

Lemma Exercise1_3a3: E13_H2 -> domain g = target E13_lam. 
Proof. 
move: Exercise1_3a1 => gE [gg alne]; rewrite /E13_lam /second_proj; aw.
set_extens t. 
  move=> tg;move: (alne _ tg) => [u us]; apply /(rangeP gE).
  by exists u; apply: disjoint_union_pi1.
by move /(rangeP gE) => [x Je]; move: (du_index_pr1 Je); aw; case.
Qed.


Lemma Exercise1_3a3'': equivalence_on E13_S (source E13_lam).
Proof. exact: (graph_ea_equivalence Exercise1_3a0). Qed.

Lemma Exercise1_3a3': substrate E13_S = E13_sF.
Proof.
by rewrite (proj2 Exercise1_3a3'') /E13_lam/ second_proj; aw.
Qed.

Lemma Exercise1_3a4: E13_H1 -> E13_H2 -> increasing_fun E13_lam E13_F r.
Proof.
move=> h1 h2; move:(h1) => [p2 p3 p4]; split => //.
+ exact: (orsum_or h1).
+ split.
  * exact: Exercise1_3a0.
  * by rewrite (orsum_sr h1) /E13_lam /second_proj /E13_F; aw. 
  * by rewrite -(Exercise1_3a3 h2). 
+ move=> x y h3; move: (orsum_gle_id h1 h3).
  move: h3 => /orsum_gleP [xs ys xy] h4.
  rewrite / E13_lam second_proj_V // second_proj_V //.   
Qed.

(** We consider the function [disjointU_function f] that maps [i] to
 [F(i)]; and the associated equivalence (two elements are related if they are 
 in the same [F(i)]). We show that this is the equivalence associated to 
 [E13_lam] and two elements are related if they have the same second 
 projection  *)

Definition disjointU_function f :=
  triple (domain f)(range (disjointU_fam f))(disjointU_fam f).

Lemma disjointU_function_pr f:
  function (disjointU_function f) /\ 
  graph (disjointU_function f) =  (disjointU_fam f).
Proof. 
rewrite /disjointU_function  /disjointU_fam. 
by split; [ apply: function_pr; [ fprops | fprops |  aw] | aw ].
Qed.

Lemma Exercise1_3a5P x y (f := fam_of_substrates g) :
  related (partition_relation (disjointU_function f) (disjointU f)) x y 
   <-> [/\ inc x E13_sF, inc y E13_sF & Q x = Q y].
Proof. 
move: (disjointU_function_pr f) => [p1 p2].
have p3:partition_w_fam (graph (disjointU_function f)) (disjointU f).
  rewrite p2; apply: partition_disjointU; apply: fos_graph.
apply: (iff_trans (isc_rel_P p1 p3 x y)).
rewrite /in_same_coset/Vf/disjointU/disjointU_function; aw.
rewrite /disjointU_fam; split.
  move=> [i [idf]]; rewrite LgV// => /indexed_P [px pxv qx] /indexed_P [py pyv qy].
  rewrite qx qy -px -py; split => //; apply: disjointU_pi; ue.
have ->: domain f = domain g by rewrite /f/fam_of_substrates; aw.
move=> [xsg ysg sq].
move: (du_index_pr1 xsg) (du_index_pr1 ysg)=> [qxd pxs px][_ pys py].
exists (Q x); rewrite /f /fam_of_substrates ! LgV//. 
split => //;apply /indexed_P; split => //; ue. 
Qed.

Lemma Exercise1_3a6P x y:
  related E13_S x y <-> [/\ inc x E13_sF, inc y E13_sF & Q x = Q y].
Proof.
move: Exercise1_3a1 Exercise1_3a0 => gs fl.
have ss: (source (second_proj E13_sF) = E13_sF) by rewrite /second_proj; aw. 
apply: (iff_trans (ea_relatedP fl x y)); rewrite ss.
by split => [] [xs ys]; rewrite !second_proj_V.
Qed.

(** We show that [ E13_S ] is an equivalence, satisfying the two conditions of
 the previous Exercise. Let [ E13_lam = g \co phi ] be the canonical 
 decomposition, where [phi] is the canonical projection of [E13_S]. Then [g] is 
 an order isormorphism (its target is the set of indices [i]). 
 *)

Lemma Exercise1_3a7: equivalence E13_S.
Proof. exact: (proj1 Exercise1_3a3''). Qed.

Lemma indexed_p2 a b c: inc a (b *s1 c) -> Q a = c.
Proof. by move /indexed_P => [_ _]. Qed.

Lemma Exercise1_3a8P a: E13_H2 ->
  (inc a (quotient E13_S) <-> exists2 i,
    inc i (domain g) & a = (Vg (fam_of_substrates g) i) *s1 i).
Proof. 
move: Exercise1_3a7 => es h2.
have df : domain (fam_of_substrates g) = domain g.
   by rewrite /fam_of_substrates;aw. 
have aux: forall i, inc i (domain g) ->
  (Vg (fam_of_substrates g) i = substrate (Vg g i)).
  move=> i idg; rewrite /fam_of_substrates LgV//. 
split.
  move => aq; set y := rep a.
  have ysf: (inc y E13_sF) by rewrite -Exercise1_3a3'; apply: (rep_i_sr es aq).
  move: (disjointU_hi ysf); rewrite df; move => [Qx Px px];ex_tac. 
  move/(setQ_P es): aq => aq.
  set_extens t.
    move => ta; move: (rel_in_class es aq ta) => /Exercise1_3a6P [_ tsf ->].
    by move: (disjointU_hi tsf)=> [Qt Pt pt]; apply /indexed_P. 
  move /indexed_P => [pt Pt Qt]; apply/(rel_in_class2 es aq). 
  apply /Exercise1_3a6P;split => //; rewrite - pt Qt. 
  by apply:disjoint_union_pi1 => //;rewrite - aux.
move=> [i idg]; rewrite (aux _ idg) => ap; apply /(setQ_P es).
have sa: sub a E13_sF.
  rewrite ap => t /indexed_P [pt Pt Qt].
  by rewrite - pt Qt; apply: disjoint_union_pi1.
have ra: inc (rep a) a.
  apply: rep_i; exists (J (rep (substrate (Vg g i))) i); rewrite ap.
  by apply: indexed_pi; apply: rep_i; apply: (proj2 h2).
split; first by rewrite Exercise1_3a3'; apply: sa.
have qa : Q (rep a) = i by rewrite {2} ap in ra; move: (indexed_p2 ra).
set_extens t.
  move => ta; apply /(class_P es) /Exercise1_3a6P;split;fprops.
  by rewrite ap in ta; rewrite (indexed_p2 ta).
move/(class_P es) /Exercise1_3a6P => [pa pb pc]; rewrite ap.
move: (disjointU_hi pb) => [pd pe <-]; rewrite -pc qa.
by apply : indexed_pi; rewrite - aux // -qa pc.
Qed.

Lemma Exercise1_3a9: function (fun_on_quotient E13_S E13_lam).
Proof.
move: Exercise1_3a0 => aux.
move:Exercise1_3a3'' => [sa sb].
by apply: foqc_f.
Qed.

Lemma Exercise1_3a10:  
  (fun_on_quotient E13_S E13_lam) \coP (canon_proj E13_S).
Proof. 
split => //; first by apply: Exercise1_3a9.
  apply: canon_proj_f; apply: Exercise1_3a7.
by rewrite /fun_on_quotient/section_canon_proj; aw.
Qed.

Lemma Exercise1_3a11: 
  E13_lam =  (fun_on_quotient E13_S E13_lam) \co (canon_proj E13_S).
Proof. apply: (canonical_decomposition_surj2 Exercise1_3a2). Qed.

Lemma Exercise1_3a12 x:  E13_H2 ->
  inc x (quotient E13_S) -> exists i,
    [/\ inc i (domain g), x = (Vg (fam_of_substrates g) i) *s1 i &
    Vf (fun_on_quotient E13_S E13_lam) x = i].
Proof. 
move: Exercise1_3a0  Exercise1_3a7 => fl es  h2 xq.
move /(Exercise1_3a8P x h2): (xq) =>  [i idg xp].
have sl:=proj2 Exercise1_3a3''.
ex_tac.
rewrite foqc_V //.
have -> : Vf E13_lam (rep x) = Q (rep x).
  by rewrite /E13_lam second_proj_V // -Exercise1_3a3'; apply: rep_i_sr.
have:(inc (rep x) x) by apply: (rep_in_class es); apply /(setQ_P es).
by rewrite {2} xp; move /indexed_P => [_ _].
Qed.

Lemma Exercise1_3a13: E13_H2 -> bijection (fun_on_quotient E13_S E13_lam).
Proof.
move: Exercise1_3a9 => ffoq h2.
have sfoq: source (fun_on_quotient E13_S E13_lam) = quotient E13_S.
  by rewrite /fun_on_quotient /section_canon_proj; aw.
split; split => //.
  rewrite sfoq => x y xq yq.
  move: (Exercise1_3a12 h2 xq) (Exercise1_3a12 h2 yq).
  by move => [i [_ p1 p2]] [j [_ p3 p4]]; rewrite p2 p4 p1 p3; move => ->.
rewrite sfoq {1} /fun_on_quotient; aw; rewrite -(Exercise1_3a3 h2) => y yd.
set (a:= Vg (fam_of_substrates g) y *s1 y). 
have aq: (inc a (quotient E13_S)) by apply /(Exercise1_3a8P _ h2); ex_tac.
ex_tac.
move: (Exercise1_3a12 h2 aq) => [i [idg p1 ->]].
have h:= (setQ_repi Exercise1_3a7 aq); move: (h); rewrite {2} p1  => h1.
by rewrite -(indexed_p2 h) -(indexed_p2 h1).
Qed.

Lemma Exercise1_3a14: E13_H1 ->  E13_H2 -> 
  [/\ Ex1_2_hC E13_F E13_S, Ex1_2_hC' E13_F E13_S,
  Ex1_2_hD E13_F E13_lam & Ex1_2_hD' E13_F r E13_lam].
Proof. 
move=> h1 h2.
move: (orsum_sr h1); rewrite -/E13_sF -/E13_F => s1.
move: (orsum_or h1) => o1.
have pa: Ex1_2_hC E13_F E13_S.
  move => x y z r1 /Exercise1_3a6P [xs sz qxz].
  have ys: inc y E13_sF by rewrite - s1; order_tac.
  case: (equal_or_not (Q x) (Q y)) => qxy.
    exists z; last by order_tac; rewrite s1.
    apply /Exercise1_3a6P;split => //; ue.
  exists y; first by apply /Exercise1_3a6P.
  apply /orsum_gleP; split => //; left; rewrite -qxz; split; last by exact.
  exact (orsum_gle_id h1 r1).
have pb:Ex1_2_hC' E13_F E13_S.
  move => x y z r1 r2.
  move: (orsum_gle_id h1 r1) (orsum_gle_id h1 r2) => q1 q2.
  move: r1 r2 => /orsum_gleP [_ ys _] _ /Exercise1_3a6P [xs _ sq].
  apply /Exercise1_3a6P; split => //; move: h1 => [or _ _]. 
  rewrite - sq in q2; order_tac.
have ww: source E13_lam = E13_sF by rewrite /E13_lam /second_proj; aw.
rewrite /Ex1_2_hD /Ex1_2_hD' ww.
split => //.
  move=> x y x' => /orsum_gleP  [xs ys lexy] x's.
  have r1: (Vf E13_lam x = Q x) by rewrite /E13_lam second_proj_V.
  have r2: (Vf E13_lam x' = Q x') by rewrite /E13_lam second_proj_V.
  have r3: (Vf E13_lam y = Q y) by rewrite /E13_lam second_proj_V.
  rewrite r1 r2 r3;move=> sq; case: lexy.
     rewrite sq; move=> lt; exists y;split => //; apply /orsum_gleP. 
     by split => //; left.
  move=> [p1 p2]; exists x'; split => //; last by rewrite r2  - sq -p1.
  order_tac; ue. 
move => x y xs ys lxy.
exists x;  case: (equal_or_not (Vf E13_lam x) (Vf E13_lam y)) => h.
  exists x; split => //; order_tac; rewrite orsum_sr //.
exists y; split => //; apply /orsum_gleP; split => //; left.
move: lxy h;rewrite /E13_lam !second_proj_V //.
Qed.

Lemma Exercise1_3a15: E13_H1 ->  E13_H2 -> 
  order_isomorphism  (fun_on_quotient E13_S E13_lam)
  (quotient_order E13_F E13_S) r.
Proof.
move=> h1 h2; move: (Exercise1_3a14 h1 h2) => [pa pb pc pd].
have gg:= Exercise1_3a1.
have oo: (order (order_sum r g)) by fprops.
have bf:= Exercise1_3a13.
suff : (order_morphism (fun_on_quotient E13_S E13_lam)
    (quotient_order E13_F (equivalence_associated E13_lam)) r). 
  by move => [p1 p2 [p3 p4 p5] p6]; split => //; split => //; apply: bf.
by rewrite Exercise1_2f3; [| apply: Exercise1_3a4 =>// | apply: Exercise1_3a10 |
      apply: Exercise1_3a11].
Qed.

End Exercise1_3a.

(** The ordinal sum is associative, not commutative. Associativity has been 
proved in the main text. A example of non-commutatitivity is that [omega+1] and 
[1+omega] are non-equal. We show here that if a sum of two sets has a greatest 
element, then the second one has a greatest element, and give a simple example *)

Lemma orsum2_greatest r r' x:  order r -> order r' -> ne_substrate r' ->
  greatest (order_sum2 r r') x -> greatest r' (P x).
Proof. 
move=> or or' [y ysr] [xsp xgr]. 
have aux: forall z, inc z (substrate r')
   -> (inc (J z C1) (substrate (order_sum2 r r'))).
  by move => z zi; rewrite (orsum2_sr or or'); apply: candu2_prb. 
move: (xgr _ (aux _ ysr)) => /orsum2_gleP; aw; move => [_ p1 p2].
move: p1 => /candu2P [px]; case => [] [pxs qxb].
  by case: p2=> [] [p1 p3];[case: C1_ne_C0| case: p3| case: C1_ne_C0].
split => // x0 x0sr;move /orsum2_gleP:(xgr _ (aux _ x0sr)); aw;move=> [q1 q2].
by have D :=C1_ne_C0; case;case.
Qed. 


Lemma orsum2_greatest' r r' x: order r -> order r' ->
  greatest r' x -> greatest (order_sum2 r r') (J x C1). 
Proof.
move => or1 or2  [pa pb].
have xx:=  (candu2_prb (substrate r)pa).
hnf; rewrite (orsum2_sr or1 or2); split; first exact. 
move => y yd; apply /orsum2_gleP; split ; [exact | exact | ].
move/candu2P: yd => [py]; case; move => [l1 l2].
  constructor 3; aw; split;fprops.
constructor 2; aw; rewrite l2;split;fprops.
Qed.
  
Lemma image_of_greatest r r' f x:
  order_isomorphism f r r' -> greatest r x ->
  greatest r' (Vf f x).
Proof.
move => [or or' [sf tf bf] incf] [xs xg].
rewrite - tf in xs. 
split; first by Wtac; fct_tac. 
rewrite - bf;move => y /(bij_surj sf) [z zsf ->]. 
apply/ (incf _ _ zsf xs);apply: xg; ue.
Qed.

Lemma orsum2_nc: exists r r',
  [/\ order r, order r' & ~ ( (order_sum2 r r') \Is (order_sum2 r' r))]. 
Proof.
move: (diagonal_osr (singleton C0))=> []; set r1 := diagonal _ => or1 sr1.
move: (diagonal_osr (doubleton C0 C1))=> []; set r2 := diagonal _ => or2 sr2.
have ns2: ne_substrate r2.
  have jp: inc (J C0 C0) r2 by  apply /diagonal_pi_P;split;fprops.
  exists C0; substr_tac.
have ng2: forall x, greatest r2 x -> False.
  move => x [_]; rewrite sr2 => h2;case: C0_ne_C1.
  move: (h2 _ (set2_1 C0 C1)) (h2 _ (set2_2 C0 C1)).
  by move /diagonal_pi_P => [_ ->] /diagonal_pi_P [_ ->]. 
have g2: greatest (order_sum2 r2 r1) (J C0 C1).
  apply:(orsum2_greatest' or2 or1); red; rewrite sr1; split;fprops.
  move => x /set1_P ->;  apply/diagonal_pi_P;split;fprops.
exists r2; exists r1;split => //  [] [f isf].
move: (orsum2_greatest or1 or2 ns2 (image_of_greatest isf g2)) => eg.
by case: (ng2 (P (Vf f (J C0 C1)))).
Qed.

(** Conditions under which an ordinal sum is totally ordered, directed, a lattice *)

Definition orsum_ax2 g:= allf g ne_substrate.
Section Exercise13b.
Variables r g: Set.
Hypothesis oa: orsum_ax r g.
Hypothesis oa2: orsum_ax2 g.

Lemma orsum_pr0:
  forall i, inc i (substrate r) -> 
  exists2 y, inc y (Vg (fam_of_substrates g) i) &
    inc (J y i) (sum_of_substrates g).
Proof. 
move=>  i idg.
move: oa => [or sr alo]; rewrite sr in idg.
move: (oa2 idg) => [j js]; exists j; first by rewrite /fam_of_substrates LgV.
by apply: disjoint_union_pi1.
Qed. 

Lemma orsum_pr1: 
  forall i, inc i (domain g) ->
  exists2 y, inc y (Vg (fam_of_substrates g) i) &
    inc (J y i) (substrate (order_sum r g)).
Proof. 
move: (oa) => [_ sr _] i idg; rewrite - sr in idg.
rewrite orsum_sr //; apply: (orsum_pr0  idg).
Qed. 

Lemma orsum_directed:
  (right_directed (order_sum r g) <-> (right_directed r /\
    forall i, maximal r i -> right_directed (Vg g i))).
Proof. 
move: (oa) => [or sr alo].
have os: order (order_sum r g) by fprops.
have srr:= (orsum_sr oa).
split.
  move /right_directedP => [oor h]; split. 
    apply /right_directedP;split => // x y xsr ysr.
    move: (orsum_pr0 xsr) => [x0 p1 p2].
    move: (orsum_pr0 ysr) => [y0 p3 p4].
    rewrite - srr in p2 p4.
    move: (h _ _ p2 p4) => [z [ zx zy]].
    move: (orsum_gle_id oa zx) (orsum_gle_id oa zy); aw=> q1 q2.
    by exists (Q z); split => //; move:(du_index_pr1 zs); rewrite sr; case.
  move=> i []; rewrite sr => isr im.
  apply /right_directedP; split;fprops;move=> x y xsi ysi.
  move: (disjoint_union_pi1 isr xsi)(disjoint_union_pi1 isr ysi) => p1 p2.
  rewrite - srr in p2 p1.
  move: (h _  _ p1 p2) => [z [le1 le2]]. 
  move:(arg2_sr le1); rewrite srr => /du_index_pr1 [p3 p4 p5].
  move: (orsum_gle_id oa le1); aw => /im Qzi.
  move: le1 => /orsum_gleP [_ _];rewrite /order_sum_r Qzi. 
  case; [ by case; aw | aw;move =>  [ _ le1]].
  move: le2 => /orsum_gleP [_ _]; rewrite /order_sum_r Qzi. 
  case; [ by case; aw | aw;move =>  [ _ le2]].
  exists (P z); split => //; ue.
move => [ /right_directedP [_ rr] imr]; apply /right_directedP; split => //.
move=> x y xsr ysr;  rewrite srr in xsr ysr.
move: (du_index_pr1 xsr) (du_index_pr1 ysr) => [Qx Px px][Qy Py py].
rewrite - sr in Qx Qy; move: (rr _ _  Qx Qy) => [z [ Qxz Qyz]].
case: (equal_or_not (Q x) z) => eQxz; case: (equal_or_not (Q y) z) => eQyz.
+ case: (p_or_not_p (maximal r z)) => mz.
  - move: (imr _ mz); move: (proj1 mz); rewrite sr => zs.
    move /right_directedP => [oz etc]. 
    rewrite eQxz in Px;rewrite eQyz in Py.
    move: (etc _ _ Px Py)=> [t [ t1 t2]].
    have aux:inc (J t z) (sum_of_substrates g).
      by apply: disjoint_union_pi1 => //; apply: (arg2_sr t1).
    exists (J t z);split => //; apply /orsum_gleP=> //; 
        rewrite/order_sum_r pr1_pair pr2_pair; split=> //; right;split => //;ue.
  - have [u us zu]: (exists2 u, inc u (substrate r) & glt r z u). 
      ex_middle h; case: mz; split => //; first by ue.  
      move=> t zt; case: (equal_or_not z t) => // nzt.  
      by case: h; exists t=> //; order_tac.
    move: (orsum_pr0 us) => [v v1 v2]; exists (J v u); split;
     apply /orsum_gleP=> //; rewrite /order_sum_r ?eQxz ?eQyz; aw; split;fprops.
+ exists x; split => //; first by  order_tac; rewrite orsum_sr.
  apply /orsum_gleP; split => //; left; rewrite eQxz; split => //.
+ exists y; split => //; last by order_tac;   rewrite orsum_sr.
  apply /orsum_gleP; split => //;left; rewrite eQyz; split => //.
+ move:(arg2_sr Qxz) => zdg.
  move: (orsum_pr0 zdg) => [v v1 v2]; exists (J v z); split;
  apply /orsum_gleP; split => //; left; aw; order_tac.
Qed.

Lemma orsum_total1:
  total_order (order_sum r g) -> (total_order r /\
    forall i, inc i (domain g) -> total_order (Vg g i)).
Proof. 
rewrite /total_order.
move: (oa) => [or sr alo];rewrite orsum_sr // sr.
move=> [ors to]; split.
  split => // x y xdg ydg.
  move: (oa2 xdg) (oa2 ydg) => [a asx][b bsy].
  case: (to _ _ (disjoint_union_pi1 xdg asx) (disjoint_union_pi1 ydg bsy));
    move=> h; move: (orsum_gle2 h); rewrite /glt.
    move => aux;left; case: aux; move=> [res _] //; rewrite res; order_tac; ue.
  move => aux;right; case: aux; move=> [res _] //; rewrite res; order_tac; ue.
move=> i idg; move: (alo _ idg) => lo; split => // => x y xsr ysr; red.
by case: (to _ _ (disjoint_union_pi1 idg xsr) (disjoint_union_pi1 idg ysr));
 move=> h; move: (orsum_gle2 h); case; case => // _ ok; [left | right].
Qed. 

Lemma orsum_total2:
  total_order r ->
  (forall i, inc i (domain g) -> total_order (Vg g i)) ->
  total_order (order_sum r g).
Proof. 
move=> [_ tor] alt; rewrite /total_order.
move: (oa) => [or sr alo]; rewrite orsum_sr //.
rewrite sr in tor.
split =>//; first by  fprops.
move=> x y xsr ysr; move: (du_index_pr1 xsr) (du_index_pr1 ysr).
move=> [Qx Px px][Qy Py py].
case: (equal_or_not (Q x) (Q y)). 
  move =>h; move: (alt _ Qx) => [lor ltor]; rewrite -h in Py.
  case: (ltor _ _ Px Py) => h1;aw ; [left | right]; 
    apply /orsum_gleP;split => //; right; split => //; ue.
move=> nQ; case: (tor _ _ Qx Qy) => h; [left | right];
  apply /orsum_gleP;split => //; left;split; fprops.
Qed.

Lemma orsum_g1 i x i' x': 
  inc (J i x) (sum_of_substrates g) -> inc (J i' x') (sum_of_substrates g) ->
  gle r x x' -> x <> x' -> 
  gle (order_sum r g) (J i x) (J i' x').
Proof.
move=> js1 js2 le1 lt1.
apply /orsum_gleP; split => //; left; saw.
Qed.


Lemma orsum_lattice1:  lattice (order_sum r g) -> lattice r.
Proof. 
move=> lF.
move:(orsum_pr1); set (F:= order_sum r g) => aux.
move: (oa) => [or sr alo].
have oF: order F by rewrite /F; fprops. 
have sF: substrate F = sum_of_substrates g by rewrite /F orsum_sr.
split => //; rewrite sr => x y xsr ysr. 
move: (aux _ xsr)  (aux _ ysr) => [x' x'1 x'2][y' y'1 y'2].
split.
  move: (lattice_sup_pr lF y'2 x'2); rewrite -/F; move=> [le1 le2 le3].
  case: (p_or_not_p (gle r x y))=> lxy. 
    by exists y; apply: sup_comparable.
  case: (p_or_not_p (gle r y x)) => lyx.
    by exists x; rewrite set2_C;  apply: sup_comparable.
  move: (arg2_sr le1); rewrite sF => zs; move:(du_index_pr1 zs) => [Qz Pz pz]. 
  exists (Q (sup F (J y' y) (J x' x))); apply: lub_set2 => //. 
      by move: (orsum_gle_id oa le2); aw. 
    by move: (orsum_gle_id oa le1); aw. 
  move=> t xt yt.
  move: (arg2_sr xt); rewrite sr => /aux [u uVg us]. 
  rewrite sF in x'2 y'2 us.
  have le4: gle F (J x' x) (J u t) by apply: orsum_g1 => //; dneg aa; ue.
  have le5: gle F (J y' y) (J u t) by apply: orsum_g1 => //eyt; case: lxy; ue.
  by move: (le3 _ le5 le4) => le6;  move: (orsum_gle_id oa le6); aw. 
move: (lattice_inf_pr lF y'2 x'2); rewrite -/F; move=> [le1 le2 le3].
case: (p_or_not_p (gle r x y))=> lxy; first by exists x; apply: inf_comparable. 
case: (p_or_not_p (gle r y x)) => lyx.
  by exists y; rewrite set2_C;  apply: inf_comparable.
move: (arg1_sr le1);rewrite sF => zs; move: (du_index_pr1 zs) => [Qz Pz pz].
exists (Q (inf F (J y' y) (J x' x))). 
apply: glb_set2 => //. 
    by move: (orsum_gle_id oa le2); aw. 
  by move: (orsum_gle_id oa le1); aw. 
move=> t xt yt.
move: (arg1_sr xt); rewrite sr; move=> /aux [u uVg us].
rewrite sF in x'2 y'2 us.
have le4: (gle F (J u t) (J x' x)) by apply: orsum_g1 => //eyt; case: lxy; ue.
have le5: (gle F  (J u t) (J y' y)) by apply: orsum_g1 => //ext; case: lyx; ue.
by move: (le3 _ le5 le4) => le6;  move: (orsum_gle_id oa le6); aw. 
Qed.

Let orsum_lattice_H1:= forall i j, inc i (domain g) -> inc j (domain g) ->
    [\/ gle r i j, gle r j i | (exists u v,
      least (Vg g (sup r i j)) u /\
      greatest (Vg g (inf r i j)) v)].

Let orsum_lattice_H2 := forall i x y t,
  inc i (domain g) -> gle (Vg g i) x t -> gle (Vg g i) y t ->
    has_supremum (Vg g i) (doubleton x y).
Let orsum_lattice_H3 := forall i x y t,
  inc i (domain g) -> gle (Vg g i) t x -> gle (Vg g i) t y ->
    has_infimum (Vg g i) (doubleton x y).
Let orsum_lattice_H4 := forall i x y,
  inc i (domain g) ->  inc x (Vg (fam_of_substrates g) i) ->
  inc y (Vg (fam_of_substrates g) i) ->
  (forall t, inc t (Vg  (fam_of_substrates g) i) ->
     ~ (gle (Vg g i) x t /\ gle (Vg g i) y t)) ->
  exists j, [/\ inc j (domain g),
    least (induced_order r (Zo (domain g) (fun k=> glt r i k))) j &
    has_least  (Vg g j)].
Let orsum_lattice_H5 := forall i x y,
  inc i (domain g) ->  inc x (Vg (fam_of_substrates g) i) ->
  inc y (Vg (fam_of_substrates g) i) ->
  (forall t, inc t (Vg (fam_of_substrates g) i) ->
     ~ (gle (Vg g i) t x /\ gle (Vg g i) t y)) ->
  exists j, [/\ inc j (domain g),
    greatest (induced_order r (Zo (domain g) (fun k=> glt r k i))) j &
    has_greatest  (Vg g j)].


Lemma orsum_lattice2: lattice (order_sum r g) -> orsum_lattice_H1.
Proof.
move=> los i j idg jdg.
move: (orsum_lattice1 los)=> lr.  
move:orsum_pr1; set (F:= order_sum r g) => aux.
have oF:order F by rewrite /F; fprops. 
move: (oa) => [or sr alo].
have sF: substrate F = sum_of_substrates g by rewrite /F orsum_sr.
case: (p_or_not_p (gle r i j)); first by in_TP4.
case: (p_or_not_p (gle r j i)); first by in_TP4.
move=> nji nij; constructor 3.
move: (aux _ idg) (aux _ jdg) => [u uVg Ju][v vVg Jv].
move: (lattice_sup_pr los Ju Jv) (lattice_inf_pr los Ju Jv); rewrite -/F.
set (A:= inf F (J u i) (J v j)); set (a:= inf r i j).
set (B:= sup F (J u i) (J v j)); set (b:= sup r i j). 
move=> [p1 p2 p3][p4 p5 p6].
rewrite - sr in idg jdg.
rewrite sF in Ju Jv.
move: (lattice_inf_pr lr idg jdg) (lattice_sup_pr lr idg jdg).
rewrite -/a -/b; move=> [q1 q2 q3][q4 q5 q6].
have Hc: Q A = a.
  have s1: (gle r (Q A) a). 
    move: (orsum_gle_id oa p4) (orsum_gle_id oa p5); aw => s1 s2.
    apply: (q3 _ s1 s2).
  move: (arg1_sr q1); rewrite sr => /aux [y yVg Js].
  rewrite sF in Js.
  have s2: gle F (J y a) (J u i) by apply: orsum_g1 => // eai; case: nij;ue.
  have s3: gle F (J y a) (J v j) by apply: orsum_g1 => // eai; case: nji;ue.
  move: (p6 _  s2 s3) => s4;move: (orsum_gle_id oa s4); aw => s5; order_tac.
have Hd: Q B = b.
  have s1: (gle r b (Q B)). 
    move: (orsum_gle_id oa p1)(orsum_gle_id oa p2); aw => s1 s2.
    apply: (q6 _ s1 s2).
  move: (arg2_sr q4); rewrite sr => /aux [y yVg Js].
  rewrite sF in Js.
  have s2: (gle F (J u i) (J y b)) by apply: orsum_g1 => // eai; case: nji;ue.
  have s3: (gle F (J v j) (J y b)) by apply: orsum_g1 => // eai; case: nij;ue.
  move: (p3 _  s2 s3) => s4;move: (orsum_gle_id oa s4); aw => s5; order_tac.
move: (arg2_sr p2)  (arg1_sr p5); rewrite sF => Bs As.
move: (du_index_pr1 Bs) => [QB PB pB]; rewrite Hd in PB.
move: (du_index_pr1 As) => [QA PA pA]; rewrite Hc in PA.
exists (P B); exists (P A).
rewrite /least /greatest; split; split => //.
  move=> x xs. 
  have J1s: (inc (J x b) (sum_of_substrates g)).
    apply: disjoint_union_pi1=> //; ue. 
  have s1: (gle F (J u i) (J x b)) by apply: orsum_g1 => // ib; case: nji; ue. 
  have s2: (gle F (J v j) (J x b)) by apply: orsum_g1 => // ib; case: nij; ue.
  move: (p3 _  s1 s2) => /orsum_gleP [s3 s4]. 
  case; aw; [  by move => [_ ];rewrite Hd; case | by move => [->] ].
move=> x xs. 
have J1s: (inc (J x a) (sum_of_substrates g)).
apply: disjoint_union_pi1=> //; ue. 
have s1: (gle F (J x a) (J u i)) by apply: orsum_g1 => // ib; case: nij; ue. 
have s2: (gle F (J x a) (J v j)) by apply: orsum_g1 => // ib; case: nji; ue.
move: (p6 _  s1 s2) => /orsum_gleP [s3 s4].
case; aw; [  by move => [_ ];rewrite Hc; case | by move => [->] ].
Qed.

Lemma orsum_lattice3:
  lattice (order_sum r g) -> orsum_lattice_H2.
Proof.
move=> lo i x y t idg le1 le2.
set (F:= order_sum r g).  
have oF:order F by rewrite /F; fprops. 
move: (oa) => [or sr alo].
have sF: substrate F = sum_of_substrates g by rewrite /F orsum_sr.
move: (arg1_sr le1)(arg2_sr le1) (arg1_sr le2).
move=> xs ts ys.
move: (disjoint_union_pi1 idg xs)(disjoint_union_pi1 idg ys).
move: (disjoint_union_pi1 idg ts); rewrite - sF => Jts Jxs Jys.
move: (lattice_sup_pr lo Jxs Jys) => [ple1 ple2 ple3].
have le4: (gle F (J y i) (J t i)) 
   by apply /orsum_gleP;split => //; try ue; right;saw.
have le5: (gle F (J x i) (J t i)) 
   by apply /orsum_gleP;split => //; try ue; right;saw.
move: (ple3 _ le5 le4) => le6.
move: (orsum_gle_id oa ple1); aw => le7.
move: (orsum_gle_id oa le6); aw => le8.
move: (order_antisymmetry or le7 le8) => eq1.
exists (P (sup (order_sum r g) (J x i) (J y i))). 
apply: lub_set2; first by apply: alo.
  move: ple1 =>/orsum_gleP [_ _]; case; first by move => [_]; aw;case.
    by aw; move => [->].
  move: ple2 =>/orsum_gleP [_ _]; case; first by move => [_]; aw;case.
    by aw; move => [->].
move=> u xu yu.
move: (disjoint_union_pi1 idg (arg2_sr xu)) => Jus.
rewrite - sF in Jus.
have le9: (gle F (J x i) (J u i)) 
   by apply /orsum_gleP;split => //; [ue|ue| right;split => //; aw].
have le10: (gle F (J y i) (J u i)) 
   by apply/orsum_gleP;split => //; [ue|ue| right;split => //; aw].
move: (ple3 _ le9 le10).
move /orsum_gleP => [_ _]; case;aw; first by move => [_]; rewrite - eq1.
by move => [->].
Qed. 

Lemma orsum_lattice4:
  lattice (order_sum r g) -> orsum_lattice_H3.
Proof.
move=> lo i x y t idg le1 le2. 
set (F:= order_sum r g).  
have oF:order F by rewrite /F; fprops. 
move: (oa) => [or sr alo].
have sF: substrate F = sum_of_substrates g by rewrite /F orsum_sr.
move: (arg2_sr le1)(arg1_sr le1) (arg2_sr le2).
move=> xs ts ys.
move: (disjoint_union_pi1 idg xs)(disjoint_union_pi1 idg ys).
move: (disjoint_union_pi1 idg ts); rewrite - sF => Jts Jxs Jys.
move: (lattice_inf_pr lo Jxs Jys) => [ple1 ple2 ple3].
have le4: (gle F (J t i) (J y i))
   by apply /orsum_gleP;split => //; try ue; right;saw.
have le5: (gle F (J t i) (J x i))
   by apply /orsum_gleP;split => //; try ue; right;saw.
move: (ple3 _ le5 le4) => le6.
move: (orsum_gle_id oa ple1); aw => le7.
move: (orsum_gle_id oa le6); aw => le8.
move: (order_antisymmetry or le7 le8) => eq1.
exists (P (inf (order_sum r g) (J x i) (J y i))).
apply: glb_set2; first by apply: alo.
  move: ple1 =>/orsum_gleP [_ _]; case; first by move => [_]; aw;case.
    by aw; move => [->].
  move: ple2 =>/orsum_gleP [_ _]; case; first by move => [_]; aw;case.
    by aw; move => [->].
move=> u xu yu.
move: (disjoint_union_pi1 idg (arg1_sr xu)) => Jus.
rewrite - sF in Jus.
have le9: (gle F (J u i) (J x i)) 
  by apply /orsum_gleP;split => //; [ue|ue| right;saw].
have le10: (gle F (J u i) (J y i))
    by apply/orsum_gleP;split => //; [ue|ue| right;saw].
move: (ple3 _ le9 le10). 
move /orsum_gleP => [_ _]; case;aw; first by move => [_]; case; rewrite eq1.
by move => [->].
Qed. 

Lemma orsum_lattice5: lattice (order_sum r g) -> orsum_lattice_H4.
Proof. 
move=> los i x y idg xVs yVs alt.
move: (orsum_lattice1 los)=> lr.  
set (F:= order_sum r  g).  
have aux:forall i, inc i (domain g) -> exists2 y, 
    inc y (Vg (fam_of_substrates g) i) &
    inc (J y i) (substrate F) by  apply: orsum_pr1. 
have oF:order F by rewrite /F; fprops. 
move: (oa) => [or sr alo].
have sF: substrate F = sum_of_substrates g by rewrite /F orsum_sr.
move: xVs yVs;rewrite /fam_of_substrates !LgV// => xVs yVs.
move: (disjoint_union_pi1 idg xVs) (disjoint_union_pi1 idg yVs) => l1 l2.
rewrite - sF in l1 l2.
move: (lattice_sup_pr los l1 l2).
set (Z:=sup  (order_sum r g) (J x i) (J y i)). 
move=> [] /orsum_gleP [_ zs l3] /orsum_gleP [_ _ l4] l5.
move: (du_index_pr1 zs) => [QZ PZ pz].
have l6: (glt r i (Q Z)). 
  move: l3; case; aw; move: l4; case; aw; trivial;move=> [iQ l3] [_ l4]. 
  move:(alt (P Z)); rewrite /fam_of_substrates LgV//.
  rewrite {1} iQ;move=> h; case: (h  PZ); split => //.
have sZ: (sub (Zo (domain g) (glt r i)) (substrate r)).
  rewrite sr; apply: Zo_S.
have z1: inc (Q Z) (Zo (domain g) (glt r i))  by apply: Zo_i.
exists (Q Z); split => //.
  hnf;rewrite iorder_sr //;split => //; move => u /Zo_P [udg iu]; apply /iorder_gle0P => //.
    by apply: Zo_i.
  move:(aux _ udg) => [v vVg Js].
  have l7: (gle F (J x i) (J v u))  
    by apply /orsum_gleP;split => //; try ue; left; aw.
  have l8: (gle F (J y i) (J v u)) 
    by apply /orsum_gleP;split => //; try ue; left; aw.
  by move:(orsum_gle_id oa (l5 _ l7 l8)); aw.
exists (P Z);split => // u us.
move:(disjoint_union_pi1 QZ us) => Js.
have l7: (gle F (J x i) (J u (Q Z))) 
  by apply /orsum_gleP;split => //; try ue; left; aw.
have l8: (gle F (J y i) (J u (Q Z)))  
  by apply /orsum_gleP;split => //; try ue; left; aw.
move: (l5 _ l7 l8) => /orsum_gleP [r1 r2];case =>[] []; aw; trivial.
by move => _; case.
Qed.  


Lemma orsum_lattice6: lattice (order_sum r g) -> orsum_lattice_H5.
Proof. 
move=> los i x y idg xVs yVs alt.
have lr:= (orsum_lattice1 los).
set (F:= order_sum r  g).  
have aux:forall i, inc i (domain g) -> exists2 y, 
    inc y (Vg (fam_of_substrates g) i) &
    inc (J y i) (substrate F) by  apply: orsum_pr1. 
have oF:order F by rewrite /F; fprops. 
move: (oa) => [or sr alo].
have sF: substrate F = sum_of_substrates g by rewrite /F orsum_sr.
move: xVs yVs;rewrite /fam_of_substrates LgV// => xVs yVs.
move: (disjoint_union_pi1 idg xVs) (disjoint_union_pi1 idg yVs) => l1 l2.
rewrite - sF in l1 l2.
move: (lattice_inf_pr los l1 l2).
set (Z:=inf  (order_sum r g) (J x i) (J y i)).  
move => []/orsum_gleP [zs _ l3 ] /orsum_gleP [_ _ l4] l5.
move:  (du_index_pr1 zs) => [QZ PZ pz].
have l6: (glt r (Q Z) i).
  case: l3; [ by aw  | case: l4; [ by aw | aw; move=> [iQ l3] [_ l4]]]. 
  move:(alt (P Z)); rewrite /fam_of_substrates LgV//. 
  rewrite - iQ;move=> h; case: (h PZ); split => //.
have sZ:  (sub (Zo (domain g) (fun k  => glt r k i)) (substrate r)).
  rewrite sr; apply: Zo_S.
have z1: inc (Q Z) (Zo (domain g) (fun k => glt r k i))  by apply Zo_i.
exists (Q Z); split => //.
  red; rewrite iorder_sr //; split => //; move => u /Zo_P [udg iu].
  apply /iorder_gle0P => //; first by apply: Zo_i.
  move:(aux _ udg) => [v vVg Js]. 
  have l7: (gle F (J v u)  (J x i)) 
    by apply /orsum_gleP;split => //; try ue; left; aw.
  have l8: (gle F (J v u)  (J y i))  
    by apply /orsum_gleP;split => //; try ue; left; aw.
  by move: (orsum_gle_id oa  (l5 _ l7 l8)); aw. 
exists (P Z);split => // u us.
move:(disjoint_union_pi1 QZ us) => Js.
have l7: (gle F (J u (Q Z)) (J x i)) 
   by apply /orsum_gleP;split => //; try ue; left; aw.
have l8: (gle F  (J u (Q Z)) (J y i)) 
   by apply /orsum_gleP;split => //; try ue; left; aw.
move: (l5 _ l7 l8); move /orsum_gleP => [r1 r2];case =>[] []; aw; trivial.
by move => _; case.
Qed.

Lemma orsum_lattice:
  (lattice (order_sum r g) <->
  ((lattice r) /\ 
   [/\ orsum_lattice_H1, orsum_lattice_H2, orsum_lattice_H3, orsum_lattice_H4
    & orsum_lattice_H5])).
Proof. 
set (F:= order_sum r g).  
have oF:order F by rewrite /F; fprops. 
move: (oa) => [or sr alo].
split.
  move=> h; split; last split.
  apply: (orsum_lattice1 h). 
  apply: (orsum_lattice2 h).
  apply: (orsum_lattice3 h). 
  apply: (orsum_lattice4 h).
  apply: (orsum_lattice5 h).
  apply: (orsum_lattice6 h).
move=> [h1 [h2 h3 h4 h5 h6]].
have sF: substrate F = sum_of_substrates g by rewrite /F orsum_sr.
split=>//.
rewrite sF;move=> x y xs ys.
move: (du_index_pr1 xs) (du_index_pr1 ys) => [Qx Px px][Qy Py py].
rewrite - sr in Qx Qy.
split.
  move: (lattice_sup_pr h1 Qx Qy); set (a:= sup r (Q x) (Q y)).
  move=> [l1 l2 l3].
  have p1: (forall z, gle F x z -> gle F y z -> gle r a (Q z)).
     move=> z z1 z2; move: (orsum_gle_id oa z2).
     move: (orsum_gle_id oa z1); apply: l3. 
  case: (equal_or_not (Q x) (Q y)) => sq. 
    rewrite - sq in Py; rewrite sr in Qx Qy.
    case: (p_or_not_p (exists2 t, gle (Vg g (Q x)) (P x) t &
        gle (Vg g (Q x)) (P y) t)).
      move=> [t l4 l5]; move: (h3 _ _ _ _ Qx l4 l5) => sd.
      move: (sup_pr (alo _ Qx) Px Py sd).
      set (z:= sup _ _ _); move => [z1 z2 z3].
      have jZs: (inc (J z (Q x)) (substrate F)).
        rewrite sF; apply: disjoint_union_pi1 => //; order_tac.
      exists (J z (Q x)).
      apply: lub_set2.
      + exact.
      + apply/orsum_gleP;split => //;try ue;right; aw => //; ue.
      + apply/orsum_gleP;split => //;try ue;right; aw => //; ue.
      + move => w /orsum_gleP [_ w0 w1] /orsum_gleP [_  _ w2]. 
        apply /orsum_gleP;split => //; first by ue. 
        case: w1 => [] [pa pb]; [ by left; aw; split | right; aw ].
        case: w2; first by move => [_]; case; rewrite - sq.
        move => [->]; ue.
    move=> net.
    have aux: (forall t, inc t (Vg (fam_of_substrates g) (Q x))
        -> ~ (gle (Vg g (Q x)) (P x) t /\ gle (Vg g (Q x)) (P y) t)). 
      move=> t tVQ [ha hb]; case: net; exists t=>//.
    have Px': (inc (P x) (Vg (fam_of_substrates g) (Q x))).
        rewrite /fam_of_substrates LgV//.
    have Py': (inc (P y) (Vg (fam_of_substrates g) (Q x))).
        rewrite /fam_of_substrates LgV//.
    move: (h5 _ _ _ Qx Px' Py' aux) => [w [wdg lew [z [zs lez]]]].
    set  s:=(Zo (domain g) (fun k : Set => glt r (Q x) k)) in lew.
    have Hc:sub s (substrate r) by rewrite sr; apply: Zo_S.
    move: lew; rewrite /least iorder_sr//; move=> [/Zo_P [_] lt0 lew].
    have Js: (inc (J z w) (sum_of_substrates g)). 
      by apply: disjoint_union_pi1. 
    exists  (J z w); apply: lub_set2.
           exact.
         by apply /orsum_gleP; saw; left; aw.
       apply /orsum_gleP; saw; left;aw; ue. 
    move=> t /orsum_gleP [_ ts l4] /orsum_gleP[_ _ l5 ]. 
    apply /orsum_gleP;split => //.
    move: (du_index_pr1 ts) => [Qt Pt pt].
    case: (equal_or_not w (Q t)) => wq.  
       by right; aw;split => //; apply: lez; ue. 
    left; aw;split => //; case: (p_or_not_p (glt r (Q x) (Q t))).
      move=> le3; apply: (iorder_gle1 (lew _ (Zo_i Qt le3))).
    move=> ltxt; case: l4; [ by move => r1 | move=> [r1 r2] ].
    case: l5;  rewrite - sq; [ by move => r3 | move=> [r3 r4] ].
    have Pt': (inc (P t) (Vg (fam_of_substrates g) (Q x))).
      by rewrite /fam_of_substrates LgV// r1.
    by case: (aux _ Pt').
  rewrite sr in Qx Qy.
  move: (h2 _ _ Qx Qy) => h7.
  case: (equal_or_not (Q y) a) => Qya.
    exists y; apply: sup_comparable=> //.
    apply /orsum_gleP;split => //; left; split => //; ue.
  case: (equal_or_not (Q x) a) => Qxa.
    exists x; rewrite set2_C; apply: sup_comparable => //.
    apply /orsum_gleP;split => //; left; split => //; ue.
  case: h7=> h7'.
     have lyy: (gle r  (Q y) (Q y)) by order_tac; ue.
     case: Qya; exact: (order_antisymmetry or l2 (l3 _ h7' lyy)). 
    have lxx: (gle r  (Q x) (Q x)) by order_tac; ue.
    case: Qxa; exact: (order_antisymmetry or l1 (l3 _  lxx h7')).
  move: h7' => [u [v [lea geb]]].
  rewrite -/a in lea; move: lea => [us leu].
  have J3: (inc (J u a) (sum_of_substrates g)). 
      apply: disjoint_union_pi1 => //; rewrite - sr; order_tac.
  exists (J u a); apply: lub_set2.
        exact.
      by apply /orsum_gleP;split => //;left;saw; apply:nesym.
    by apply /orsum_gleP;split => //;left;split;aw => //; apply:nesym.
  move=> t l5 l6; move: (p1 _ l5 l6).
  move: l5 l6 => /orsum_gleP [xsg tsg s1] /orsum_gleP [ysg _ s2] aQ. 
  apply /orsum_gleP;split => //.
  case: (equal_or_not a (Q t)) => naQ; last by left; aw.
  right; aw;split => //; apply: leu; rewrite naQ. 
  by move: (du_index_pr1 tsg) => [_].
move: (lattice_inf_pr h1 Qx Qy); set (a:= inf r (Q x) (Q y)).
move=> [l1 l2 l3].
have p1: (forall z, gle F z x -> gle F z y -> gle r (Q z) a).
   move=> z z1 z2; move: (orsum_gle_id oa z2).
   move: (orsum_gle_id oa z1); apply: l3. 
case: (equal_or_not (Q x) (Q y)) => sq. 
  rewrite - sq in Py; rewrite sr in Qx Qy.
  case: (p_or_not_p (exists2 t, gle (Vg g (Q x)) t (P x) &
        gle (Vg g (Q x)) t (P y))).
    move=> [t l4 l5]; move: (h4 _ _ _ _ Qx l4 l5) => sd.
    move: (inf_pr (alo _ Qx) Px Py sd).
    set (z:= inf (Vg g (Q x)) (P x) (P y)); move => [z1 z2 z3].
    have jZs: (inc (J z (Q x)) (substrate F)).
      rewrite sF; apply: disjoint_union_pi1 => //; order_tac.
    exists (J z (Q x)).
    apply: glb_set2.
          exact.
        apply/orsum_gleP;split => //;try ue;right; aw => //; ue.
      apply/orsum_gleP;split => //;try ue;right; aw => //; ue.
    move=> w /orsum_gleP [w0 _ w1 ] /orsum_gleP [_ _ w2]; 
    apply /orsum_gleP; split => //; first by ue. 
    case: w1; first by move => pa; left; aw.
    move => [pa pb];case: w2; first by move => pc; left; aw; ue.
    move => [pc pd]; right; aw;split => //; rewrite pa; apply: z3 => //; ue.
  move=> net.
  have aux: (forall t, inc t (Vg (fam_of_substrates g)  (Q x) )
        -> ~ (gle (Vg g (Q x)) t (P x) /\ gle (Vg g (Q x)) t (P y))). 
    move=> t tVQ [ha hb]; case: net; exists t=>//.
    have Px': (inc (P x) (Vg (fam_of_substrates g) (Q x))).
      rewrite /fam_of_substrates LgV//.
    have Py': (inc (P y) (Vg (fam_of_substrates g) (Q x))).
      rewrite /fam_of_substrates LgV//. 
  move: (h6 _ _ _ Qx Px' Py' aux) => [w [wdg lew [z [zs lez]]]].
  set  s:=(Zo (domain g) (fun k : Set => glt r k (Q x))) in lew.
  have Hc:sub s (substrate r) by rewrite sr; apply: Zo_S.
  move: lew; rewrite /greatest iorder_sr//; move=> [/Zo_hi lt0 lew].
  have Js: (inc (J z w) (sum_of_substrates g)). 
    apply: disjoint_union_pi1 => //. 
  exists  (J z w); apply: glb_set2.
        exact.
      apply /orsum_gleP; split => //; left;aw;trivial; ue. 
    apply /orsum_gleP; split => //; left;aw; ue. 
  move=> t /orsum_gleP [ts _ l4] /orsum_gleP [_ _ l5]. 
  apply /orsum_gleP; split => //. 
  move: (du_index_pr1 ts) => [Qt Pt pt].
  case: (equal_or_not (Q t) w) => wq.
    by right; aw;split => //; rewrite wq;apply: lez; ue. 
  left; saw; case: (p_or_not_p (glt r (Q t) (Q x))).
  move=> le3; apply: (iorder_gle1 (lew _ (Zo_i Qt le3))).
  move=> ltxt; case: l4; [ by move => r1 | move=> [r1 r2] ].
    case: l5;  rewrite - sq; [ by move => r3 | move=> [r3 r4] ].
  have Pt': (inc (P t) (Vg  (fam_of_substrates g) (Q x))).
    rewrite /fam_of_substrates LgV//; ue.
  case: (aux _ Pt'); split => //; ue.
rewrite sr in Qx Qy; move: (nesym sq) => sq'.
move: (h2 _ _ Qx Qy) => h7.
case: (equal_or_not (Q y) a) => Qya.
   exists y; rewrite set2_C;apply: inf_comparable=> //.
   apply /orsum_gleP;split => //; left; split => //; ue.
case: (equal_or_not (Q x) a) => Qxa.
  exists x;  apply: inf_comparable => //.
  apply /orsum_gleP;split => //; left; split => //; ue.
case: h7=> h7'.
    have lyy: (gle r  (Q x) (Q x)) by order_tac; ue.
      by case: Qxa; exact: (order_antisymmetry or (l3 _ lyy h7') l1).
  have lxx: (gle r  (Q y) (Q y)) by order_tac; ue.
  case: Qya; exact: (order_antisymmetry or (l3 _  h7' lxx) l2). 
move: h7' => [u [v [lea geb]]].
rewrite -/a in geb; move: geb => [us leu].
have J3: (inc (J v a) (sum_of_substrates g)). 
  apply: disjoint_union_pi1 => //; rewrite - sr; order_tac.
exists (J v a); apply: glb_set2.
      exact.
    by apply /orsum_gleP;split => //;left;saw; apply:nesym.
  by apply /orsum_gleP;split => //;left;saw; apply:nesym.
move=> t l5 l6; move: (p1 _ l5 l6).
move: l5 l6 => /orsum_gleP  [xsg tsg s1]  /orsum_gleP  [ysg _ s2] aQ. 
apply /orsum_gleP; split => //.
case: (equal_or_not (Q t) a) => naQ; [right | left]; aw; last by split.
split => //; rewrite naQ;apply: leu;  rewrite -naQ.
by move: (du_index_pr1 xsg) => [_].
Qed.

End Exercise13b.


(** ---- Exercise 1.4 : properties of the least equivalence extending [x] 
and [y] are not comparable (for the ordering [r], on the substrate of [r]).
We denote by [ncr_equiv] the equivalence, by [ncr_component]  the classes *)


Definition not_comp_rel r := fun x y =>
  [/\ inc x (substrate r), inc y (substrate r) &
  (x = y \/ ~ (ocomparable r x y))].

Definition ncr_equiv r :=
  chain_equivalence (not_comp_rel r) (substrate r).
Definition ncr_component r :=
  connected_comp (not_comp_rel r) (substrate r).

Lemma ncr_properties r: order r ->
 [/\ equivalence (ncr_equiv r),
  (substrate  (ncr_equiv r) =  substrate r),
  (forall x, inc x (substrate r) -> class (ncr_equiv r) x = ncr_component r x) &
  (forall x y, not_comp_rel r x y -> related (ncr_equiv r) x y)].
Proof. 
rewrite /ncr_equiv/ncr_component=> or.
have ncre: forall x y, not_comp_rel r x y ->  inc x (substrate r). 
  by move=> x y [res _].  
have ncr: (reflexive_re (not_comp_rel r) (substrate r)).
  move => x; split; [ by move => xsr; split => //; left | by apply: ncre].
have ncs:(symmetric_r (not_comp_rel r)).
  move=> x y [xsr ysr]; case => aux; split => //; [ by left | right].
  by move => [] h; case: aux; [right | left].
move:(chain_equivalence_eq ncr ncs ncre) => [pa pb].
split => //.
+ by apply:  connected_comp_class.
+ by move => x y rxy; apply: setF_pr0.
Qed.

(** Assume that a class is a union of two sets [a] and [b] such that every 
element of [a] is comparable to every element of [b]; then one of the two sets
is empty, or the intersectpion is not empty. We deduce: if [x <= y] and [y] is
equivalent to [y'] then [x <= y'] or  [x] is equivalent to [y] *)

Lemma Exercise1_4a1 r x y: order r ->
  inc x (substrate r) -> inc y (substrate r) ->
  ocomparable r x y  \/ class (ncr_equiv r) x = class (ncr_equiv r) y.
Proof. 
move => or xsr ysr. 
case: (p_or_not_p (ocomparable r x y)) =>h; [by left | right].
move:(ncr_properties or) => [p1 p2 p3 p4].
have: related (ncr_equiv r) x y by apply: p4; split => //; right.
by move /(related_equiv_P p1) => [_ _].
Qed.


Lemma Exercise1_4a2 r y: order r -> inc y (substrate r) ->
  forall a b, a \cup b = class (ncr_equiv r) y ->
    (forall u v, inc u a -> inc v b -> ocomparable r u v) ->
    [\/ a = emptyset, b = emptyset | nonempty (a \cap b)].
Proof. 
move=> or ysr a b uab h.
case: (emptyset_dichot a)=> nea; first by apply: Or31. 
case: (emptyset_dichot b)=> neb; first by apply: Or32.
move : nea neb (ncr_properties or) => [A Aa] [B Bb] [p1 p2 p3 p4].
have uc: classp (ncr_equiv r) (a \cup b).
  rewrite uab;  apply: class_class => //; ue.
have:(related (ncr_equiv r) A B).
  apply /(in_class_relatedP p1); exists (a \cup b); split;fprops.
move /Zo_P; aw; move => [] /setXp_P [Asr Bsr] [x [xc hx tx]].
have ha: (inc (chain_head x) a) by ue. 
have tb: (inc (chain_tail x) b) by ue. 
clear hx tx; apply:Or33.
have [u [v [ua vb uv]]]: exists u v, 
     [/\ inc u a, inc v b & (not_comp_rel r) u v].
  elim:x xc ha tb => u v r1 r2 r3; first by  exists u,v.
  move: r2 r3; simpl; move=> [r0 r2] r3 r4.
  case: (inc_or_not (chain_head v) a); first by move=> r5; apply: r1. 
  have uu: inc u (a \cup b) by fprops.
  set (w := (chain_head v)).
  move=> nwa; exists u, w => //.
  suff: inc w (a \cup b) by case/setU2_P.
  apply: (rel_in_class2 p1 uc).
  move: (rel_in_class p1 uc uu)  (p4 _ _ r0) => pa pb; equiv_tac.
move:  (h _ _ ua vb) uv => aux [_ _]; case => // cv.
exists u; apply: setI2_i => // ; ue.
Qed.

Lemma Exercise1_4a3 r x y y': order r ->
  inc x (substrate r) -> related (ncr_equiv r) y y' -> gle r x y -> 
  related (ncr_equiv r) x y \/ gle r x y'.
Proof.
move=> or xsr ryy' xy.  
move: (ncr_properties or) =>  [p1 p2 p3 p4]. 
set (C:= class (ncr_equiv r) y).
set (A:=Zo C (fun z => gle r x z)).
set (B:=Zo C (fun z => gle r z x)).
have p5: (forall u v, inc u A -> inc v B -> gle r u v \/ gle r v u).
  move=> u v => /Zo_hi r1 /Zo_hi r2; right; order_tac.
case: (p_or_not_p (related (ncr_equiv r) x y)); first by left. 
move=> nxy.
have ysr: (inc y (substrate r)) by apply: (arg2_sr xy).
have uc: (A \cup B = class (ncr_equiv r) y). 
  set_extens t => ts; first by case /setU2_P: ts; move /Zo_P => [].
  have tsr: (inc t (substrate r)).
    rewrite -p2;apply: (sub_class_substrate p1 ts).
  case: (Exercise1_4a1 or xsr tsr). 
    case; first by move=> c1;apply: setU2_1; apply: Zo_i.
    by move=> c2;apply: setU2_2; apply: Zo_i. 
  move=> c3; case: nxy. 
  apply /(class_P p1); rewrite c3; apply /(class_P p1).
  by apply: symmetricity_e =>//;  apply /(class_P p1).
have yC: inc y C by apply /(class_P p1);apply: reflexivity_e => //;  ue.
have yC': inc y' C by apply /(class_P p1).
case: (Exercise1_4a2 or ysr uc p5) => h.
+ empty_tac1 y; apply: Zo_i => //. 
+ move: yC'; rewrite /C -uc; case /setU2_P; first by move /Zo_hi => h'; right.
  by rewrite h=> /in_set0. 
+ move: h => [z] /setI2_P [] /Zo_P [zC l1] /Zo_P [_ l2]; left.
  rewrite (order_antisymmetry or l1 l2).
  by apply: symmetricity_e => //; apply /(class_P p1).
Qed.

(** The equivalence relation is compatible with the order; and the quotient
 is totally ordered *)

Lemma Exercise1_4b1 r x y x' y': order r ->
  related (ncr_equiv r) x x' -> related (ncr_equiv r) y y' ->
  class (ncr_equiv r) x <> class (ncr_equiv r) y ->
  gle r x y -> gle r x' y'.
Proof.
move=>  or rxx' ryy' nsc xy.
move: (ncr_properties or) =>  [p1 p2 p3 p4]. 
have xsr': (inc x' (substrate r)) by  rewrite -p2; substr_tac. 
have ysr': (inc y' (substrate r)) by  rewrite -p2; substr_tac. 
have xsr: (inc x (substrate r)) by  rewrite -p2; substr_tac. 
have ysr: (inc y (substrate r)) by  rewrite -p2; substr_tac.
case: (Exercise1_4a1 or xsr' ysr').
  case => // gle1.
  suff: related (ncr_equiv r) x y.
     by  move /(related_equiv_P p1)=> [_ _ h]; case: nsc.
  case: (Exercise1_4a3 or xsr ryy' xy)=> // rxy'.
  have ex'x: (related (ncr_equiv r) x' x) by apply: symmetricity_e.
  case: (Exercise1_4a3 or ysr' ex'x gle1) => h.
    apply: (transitivity_e p1  rxx'); apply (symmetricity_e p1).
    apply: (transitivity_e p1 ryy' h).
  apply: (symmetricity_e p1).
  have -> //: x = y' by order_tac.
move => sc; case: nsc; apply /(class_eq1 p1).
apply: (transitivity_e p1 rxx').
have h: related (ncr_equiv r) x' y' 
  by apply /(related_equiv_P p1); split => //; ue. 
by apply: (transitivity_e p1 h); apply: (symmetricity_e p1).
Qed.

Lemma Exercise1_4b r: order r ->
  total_order(quotient_order r (ncr_equiv r)).
Proof. 
move => or.
move: (ncr_properties or) => [p1 p2 p3 p4]. 
have sa:(substrate (quotient_order r (ncr_equiv r)) = quotient (ncr_equiv r)).
  rewrite substrate_quotient_order /preorder_quo_axioms; split => //.
  by apply order_preorder.
have oq:(order (quotient_order r (ncr_equiv r))).
  apply: Exercise1_2d => // x y z xy yz xz. 
  case: (p_or_not_p (related (ncr_equiv r) x y)) => // nxy.
  have yy: (related (ncr_equiv r) y y).
    by apply: reflexivity_e =>//; rewrite p2; order_tac.
  have nsc:(class (ncr_equiv r) x <> class (ncr_equiv r) y). 
   dneg sc; apply: symmetricity_e =>//; apply /(related_equiv_P p1);split => //;
     rewrite p2; order_tac.
  move: (Exercise1_4b1 or xz yy nsc xy) => zy.
  rewrite (order_antisymmetry or yz zy) //. 
split => //.
rewrite sa  => x y xq yq.
case: (equal_or_not x y) => nxy; first by rewrite nxy; left; order_tac; ue.
move:(setQ_repi p1 xq) (setQ_repi p1 yq) => rx ry.
have rxs: (inc (rep x) (substrate r)) by rewrite -p2; apply: rep_i_sr.
have rys: (inc (rep y) (substrate r)) by rewrite -p2; apply: rep_i_sr.
have nsc:class (ncr_equiv r) (rep x) <> class (ncr_equiv r) (rep y).
  by dneg bad; move: xq yq => /(setQ_P p1) [_ -> ]  /(setQ_P p1) [_ -> ].
case: (Exercise1_4a1 or rxs rys); last by done.
move:(related_rep_in_class p1) => H.
case => cv;  [left | right]; apply /quotient_orderP; split => //.
  move=> u ux; exists (rep y) => //.
  exact: (Exercise1_4b1 or (H _ _ xq ux) (H _ _ yq ry)  nsc cv).
move=> u ux; exists (rep x) => //.
exact: (Exercise1_4b1 or (H _ _ yq ux) (H _ _ xq rx) (nesym nsc) cv).
Qed.



(** Connected components of a product of two non-empty totally ordered sets.
If one factor is a singleton, then the product is totally ordered, 
connected components are singletons; otherwise all elements of the product, 
with the possible exception of the  greatest and least element form a 
connected component  *)

Lemma Exercise1_4c1 r x: order r -> greatest r x ->
   ncr_component r x = singleton x.
Proof.
move => or  [xsr xge].
move: (ncr_properties or) => [p1 p2 p3 p4]. 
rewrite -(p3 _ xsr); apply set1_pr.
  apply /(class_P p1); apply: reflexivity_e => //; ue.
have xt: forall t, not_comp_rel r t x -> t = x.
  by move => u [q1 q2 h]; case: h; [ move=> -> | case;left; apply: xge ].
move => z /(class_P p1) r1; move: (symmetricity_e p1 r1).
move /Zo_P => [] /setXp_P; aw; move => _ [c [cc  <- tc]].
move: c cc tc.
elim => u v /=; first by move => h1 h2; rewrite h2 in h1; apply: (xt _ h1).
by move=> h1 [h2 h3] h4; rewrite (h1 h3 h4) in h2; apply:  xt.
Qed.

Lemma Exercise1_4c2 r x: order r -> least r x ->
   ncr_component r x = singleton x.
Proof.
move =>  or  [xsr xge].
move: (ncr_properties or) =>  [p1 p2 p3 p4]. 
rewrite -(p3 _ xsr); apply set1_pr.
  apply /(class_P p1); apply: reflexivity_e => //; ue.
have xt: forall t, not_comp_rel r t x -> t = x.
  by move => u [q1 q2 h]; case: h; [ move=> -> | case ; right; apply: xge].
move => z /(class_P p1) => r1; move: (symmetricity_e p1 r1).
move /Zo_P => [] /setXp_P; aw; move => _ [c [cc <- tc]].
move: c cc tc.
elim => u v; simpl; first by move => h1 h2; rewrite h2 in h1; apply: (xt _ h1).
by move=> h1 [h2 h3] h4; rewrite (h1 h3 h4) in h2; apply:  xt.
Qed.

Lemma tor_prop r: {inc substrate r &, forall x y , ocomparable r x y} -> 
  forall x y, inc x (substrate r) -> inc y (substrate r) -> 
  gle r x y \/ glt r y x.
Proof.
move=> tor x y xs ys; case: (tor _ _ xs ys); first by left.
move=> aux; case:(equal_or_not x y) => h; first by left; move: aux;rewrite h.
by right; split => //; apply:nesym.
Qed.
 
Lemma Exercise1_4c3 r r' x y: order r -> total_order r' -> 
  substrate r = singleton x -> inc y (substrate r') ->
  ncr_component (order_product2 r r') (J x y) = singleton (J x y).
Proof.
move=> or [or' tr'] sr ysr'.
set r'':= order_product2 r r'.
have xsr: inc x (substrate r) by rewrite sr; fprops.
have or'': order r'' by apply: order_product2_or.
move: (ncr_properties or'') => [p1 p2 p3 p4]. 
have Jsr: inc (J x y) (substrate  r'') by rewrite order_product2_sr; fprops. 
rewrite -(p3 _ Jsr).
have lexx: gle r x x by order_tac.
have pa:  (substrate r \times substrate r') = substrate r''.
    by rewrite order_product2_sr.
have xt: forall t, not_comp_rel r'' t (J x y) -> t = J x y.
  move => u [q1 q2 h]; case: h; first by move=> ->.
  move: (q1); rewrite -pa // sr; move => /setX_P [] pu /set1_P Pu Qu.
  case: (tr' _ _  Qu ysr'). 
    by move=> h1 h2;case: h2; left; apply /order_product2_P; aw; rewrite pa Pu.
  by move=> h1 h2; case: h2; right; apply /order_product2_P; aw; rewrite pa Pu.
set_extens t; last first.
  move /set1_P ->; apply /(class_P p1); apply: (reflexivity_e p1); ue.
move /(class_P p1) => r1; apply /set1_P;move: (symmetricity_e p1 r1).
move /Zo_hi; aw; move=> [c [cc <- tc]]; move: c cc tc.
elim => u v; simpl; first by move => h1 h2; rewrite h2 in h1; apply: (xt _ h1).
by move=> h1 [h2 h3] h4; rewrite (h1 h3 h4) in h2; apply:  xt.
Qed.

Lemma Exercise1_4c r r' b c b' c' u:
  total_order r -> total_order r' -> 
  glt r b c -> glt r' b' c' ->
  inc u (substrate (order_product2 r r')) ->
   [\/ least (order_product2 r r') u,
       greatest (order_product2 r r') u |
       inc u (ncr_component (order_product2 r r') (J b c'))].
Proof.
move:u;move => w [or tor] [or' tor'] ltbc ltbc' us.
set r'' := (order_product2 r r').
have or'': order r'' by apply: order_product2_or.
move: (ncr_properties or'') =>  [p1 p2 p3 p4]. 
have sr'': substrate  r'' = (substrate r) \times (substrate r').
  rewrite /r'' order_product2_sr //.
have bs:inc b (substrate r) by order_tac.
have bs':inc b' (substrate r') by order_tac.
have cs:inc c (substrate r) by order_tac.
have cs':inc c' (substrate r') by order_tac.
set C:= (ncr_component r'' (J b c')).
have Jas: inc (J b c') (substrate r'') by rewrite sr''; apply /setXp_P. 
have Jbs: inc (J c b') (substrate r'') by rewrite sr''; apply /setXp_P.
have p5: forall x y,  not_comp_rel r'' x y -> inc y C -> inc x C.
  move=> x y h1; rewrite /C -p3 //; move /(class_P p1) => h2.
  apply /(class_P p1) /(transitivity_e p1 h2 (symmetricity_e p1 (p4 _ _ h1))).
have p6: forall x y,  not_comp_rel r'' x y -> inc x C -> inc y C.
   move=> x y h xC;apply: (p5 _ _ _ xC); move: h => [r1 r2 r3]; split => //.
   case: r3 ; first by  move => ->; left.
   move => h; right => h1; case: h; by case: h1 => h1; [right | left].
have np1: forall u v u' v', glt r u v -> glt r' u' v' -> 
   not_comp_rel r'' (J u v') (J v u').
  move => u v u' v' uv uv'; split => //.
  + rewrite sr''; aw; apply: setXp_i; order_tac.
  + rewrite sr''; aw; apply: setXp_i; order_tac.
  + right; case; move / order_product2_P => [_ _] []; aw =>[b1 b2]; order_tac.
have JaC: inc (J b c') C 
   by rewrite /C -p3 //; apply /(class_P p1);apply: reflexivity_e => //; ue.
have JbC: inc (J c b') C by apply: (p6 _ _  (np1 _ _ _ _ ltbc ltbc') JaC).
have p7: forall u, glt r u c -> inc (J u c') C.
  move=> u u1; by apply: (p5 _ _  (np1 _ _ _ _ u1 ltbc') JbC).  
have p8: forall u, glt r b u -> inc (J u b') C.
  move=> u u1; by apply: (p6 _ _  (np1 _ _ _ _ u1 ltbc') JaC).
have p9: forall v, glt r' v c' -> inc (J c v) C.
  move=> v v1; by apply: (p6 _ _  (np1 _ _ _ _ ltbc v1) JaC).  
have p10: forall v, glt r' b' v -> inc (J b v) C.
  move=> v v1; by apply: (p5 _ _  (np1 _ _ _ _  ltbc v1) JbC).
case:(p_or_not_p(exists2 x, inc x (substrate r'') & ~ gle r'' w x)); last first.
   move => bad; apply: Or31; split => //; move=> x xsr.
   case: (p_or_not_p (gle r'' w x)) => // bad1; case: bad; ex_tac.
move=> [pt ptr ptc].
case:(p_or_not_p(exists2 x, inc x (substrate r'') & ~ gle r'' x w)); last first.
   move => bad;  apply: Or32; split => //; move=> x xsr.
   case: (p_or_not_p (gle r'' x w)) => // bad1;case: bad; ex_tac.
move=> [gr grr grc].
apply: Or33.
have ptd: ~(gle r (P w) (P pt) /\ gle r' (Q w) (Q pt)).
   move=> [h1 h2]; move: ptc => /order_product2_P; case; split => //; ue. 
have grd: ~(gle r  (P gr) (P w) /\ gle r'  (Q gr) (Q w)).
   move=> [h1 h2]; move: grc => /order_product2_P; case;split => //; ue. 
move: grr ptr us; rewrite /r'' order_product2_sr//.
move=> /setX_P [pgr Pgr Qgr] /setX_P [ppt Ppt Qpt] /setX_P [pw Pw Qw].
move: (tor_prop  tor)(tor_prop  tor') => to to'.
case: (to _ _ Pw bs)=> q1.
  case: (to' _ _ Qw bs') => q2.
    case: (to _ _ Pw Ppt)=> q3.
      case: (to' _ _ Qw Qpt) => q4; first by case: ptd; split => //.
      have q5: glt r' (Q w) c' by order_tac.
      have q6: glt r' (Q pt) c' by order_tac.
      move: (p9 _ q6) => q7.
      have q8: glt r (P w) c by order_tac.
      by move: (p5 _ _  (np1 _ _ _ _ q8 q4) q7); rewrite pw.
    have q5: (glt r (P w) c) by  order_tac.
    have q6: (glt r (P pt) c) by order_tac. 
    move: (p7 _ q6) => q7.
    have q8: glt r' (Q w) c' by order_tac.
    by move: (p6 _ _  (np1 _ _ _ _ q3 q8) q7); rewrite pw.
   move: (p10 _ q2) => q3.
   have q5: glt r (P w) c by order_tac.
   move: (p7 _ q5) => q6.
   case: (equal_or_not (P w) b) => q4.
     by move: q3; rewrite -q4 pw.
   have q7: glt r (P w) b by split.
   move: (p6 _ _  (np1 _ _ _ _ q7 ltbc') q6) => q8.
   by move: (p5 _ _   (np1 _ _ _ _ q7 q2) q8); rewrite pw.
case: (to _ _ cs Pw)=> q1'.
  case: (to' _ _ cs' Qw) => q2.
    case: (to _ _ Pgr Pw)=> q3.
      case: (to' _ _ Qgr Qw) => q4; first by case: grd; split => //.
      have q5: (glt r' b' (Q w)) by  order_tac.
      have q6: (glt r' b' (Q gr)) by order_tac. 
      move: (p10 _ q6) => q7.
      have q8: glt r b (P w)  by order_tac.
      by move: (p6 _ _  (np1 _ _ _ _ q8 q4) q7); rewrite pw.
    have q5: (glt r b (P w)) by  order_tac.
    have q6: (glt r b (P gr)) by order_tac. 
    move: (p8 _ q6) => q7.
    have q8: glt r' b' (Q w) by order_tac.
    by move: (p5 _ _  (np1 _ _ _ _ q3 q8) q7); rewrite pw.
  move: (p9 _ q2) => q3.
  have q5: glt r b (P w) by order_tac.
  move: (p8 _ q5) => q6.
  case: (equal_or_not (P w) c) => q4.
    by move: q3; rewrite -q4; rewrite pw.
  have q7: glt r c (P w) by split => //; apply:nesym.
  move: (p5 _ _  (np1 _ _ _ _ q7 ltbc') q6) => q8.
  by move: (p6 _ _   (np1 _ _ _ _ q7 q2) q8); rewrite pw.
move: (p7 _ q1') (p8 _ q1)=> q1'' q2.
case: (to' _ _ Qw bs') => q3; last first.
  by move:(p5 _ _   (np1 _ _ _ _ q1' q3) JbC); rewrite pw.
case: (to' _ _ cs' Qw) => q4; last first.
   by move:(p6 _ _   (np1 _ _ _ _ q1 q4) JaC); rewrite pw.
have q5: (gle r' c' b') by order_tac.
order_tac.
Qed.

(** ---- Exercise 1.5: free subsets. A set is free if it contains no 
two comparable elements; two free subsets can be compared  *)

Definition free_subset r X := forall x y, inc x X -> inc y X ->
  gle r x y -> x = y.
Definition free_subsets r:=
  Zo (\Po (substrate r)) (free_subset r).

Definition free_subset_compare r X Y:=
  [/\ inc X (free_subsets r), inc Y (free_subsets r) &
  forall x, inc x X -> exists2 y, inc y Y & gle r x y].
Definition free_subset_order r:= 
  graph_on (free_subset_compare r) (free_subsets r).

Lemma Exercise1_5w r x a: order r -> 
  inc x (free_subsets r) -> inc a x ->
  gle r a a.
Proof.
by move=> or xr ax; order_tac;move: xr => /Zo_P [] /setP_P xsr _; apply: xsr.
Qed.

Lemma Exercise1_5a r: order r -> 
  order_r (free_subset_compare r).
Proof.
move=> or; rewrite /free_subset_compare; split.
+ move=> x y z [xs ys p1][_ zs p2]; split => //.
  move=> a ax; move: (p1 _ ax) => [b biy l1]; move: (p2 _ biy) => [c cy l2].
  ex_tac; order_tac.
+ move=> x y [/Zo_P [_ fs1] /Zo_P [_ fs2] p1] [_ _ p2].
  set_extens t => ts. 
    move: (p1 _ ts) => [z zy le1]; move:(p2 _ zy) => [w wx le2].
    move: (fs1 _ _ ts wx (order_transitivity or le1 le2)) => eq1.
    by rewrite -eq1 in le2;rewrite (order_antisymmetry or le1 le2).
  move: (p2 _ ts)=> [z zy le1]; move: (p1 _ zy)=> [w wx le2].
  move: (fs2 _ _ ts wx (order_transitivity or le1 le2)) => eq1. 
  by rewrite -eq1 in le2; rewrite (order_antisymmetry or le1 le2).
+ move=> x y [xs ys p1]; split => //; split =>//a ax; ex_tac;
  [apply: (Exercise1_5w or xs ax) | apply: (Exercise1_5w or ys ax) ].
Qed.

Lemma fs_order_gleP r x y:
  gle (free_subset_order r) x y <-> free_subset_compare r x y.
Proof.
split; first by move /Zo_hi; aw.
move =>h; apply: Zo_i; last  by aw.
by move: h => [pa pb _]; apply :setXp_i.
Qed.

Lemma fs_order_osr r:
  order r -> order_on (free_subset_order r) (free_subsets r).
Proof.
move=> or; red;rewrite /free_subset_order graph_on_sr //.
  split => //; apply: order_from_rel; apply: Exercise1_5a =>//.
move => a ax; split => // t ts;ex_tac; apply: (Exercise1_5w or ax ts). 
Qed.

Lemma Exercise1_5b r x: order r ->
  inc x (substrate r) -> inc (singleton x) (free_subsets r).
Proof. 
move=> or xsr; apply: Zo_i; first by apply /setP_P; apply: set1_sub.
by move=> u v /set1_P -> /set1_P ->. 
Qed.

Lemma Exercise1_5cP r x y: order r ->
  inc x (substrate r) -> inc y (substrate r) ->
  (gle r x y <-> gle (free_subset_order r) (singleton x) (singleton y)).
Proof. 
move => or xsr ysr.
split.
  move => lxy; apply /fs_order_gleP; split => //; try apply: Exercise1_5b => //.
  move => u /set1_P ->; exists y; fprops.
by move /fs_order_gleP => [_ _ rxy];move:(rxy _ (set1_1 x)) => [z] /set1_P ->.
Qed.

Lemma Exercise1_5d r: order r ->
  order_morphism (Lf singleton (substrate r)  (free_subsets r))
  r (free_subset_order r).
Proof.
move=> or.
have tf: (lf_axiom singleton (substrate r) (free_subsets r)).
  by move=> x xsr; apply: Exercise1_5b.
have [pa pb] :=(fs_order_osr or).
split => //; first by split;aw => //; apply: lf_function. 
hnf; aw;move=> x y xsr ysr; rewrite !LfV//;apply: (Exercise1_5cP or xsr ysr).
Qed.

(** The set of free subsets is totally ordered if and only if the set itself is totally ordered *)

Lemma Exercise1_5e r X: total_order r ->
  inc X (free_subsets r) -> small_set X.
Proof. 
move=>  [_ t] /Zo_P [] /setP_P xs fs x y xX yX. 
by case: (t _ _ (xs _ xX) (xs _ yX)) => aux; [ | symmetry ]; apply: fs.
Qed.

Lemma Exercise1_5f r X Y: order r ->
  inc X (free_subsets r) -> inc Y (free_subsets r) ->
  sub X Y ->  gle (free_subset_order r) X Y.
Proof. 
move=> or Xsf Ysf XY; apply /fs_order_gleP; split => //. 
move=> x xX;move: (XY _ xX) => xY; ex_tac; apply: (Exercise1_5w or Ysf xY). 
Qed.

Lemma Exercise1_5g r: total_order r -> 
  total_order (free_subset_order r).
Proof. 
move=> tor; move: (tor)=> [or tr].
have [pa pb] := (fs_order_osr or).
split => //; rewrite pb => x y xsf ysf.
have ef: (inc emptyset (free_subsets r)). 
  apply: Zo_i; [ by apply:setP_0i | by move=> u _y /in_set0 ].
move: (Exercise1_5e tor xsf) (Exercise1_5e tor ysf) => sx sy.
case: (emptyset_dichot x) => xe.  
  rewrite xe; left; apply:Exercise1_5f; fprops.
case: (emptyset_dichot y) => ye.
  rewrite ye; right; apply: Exercise1_5f; fprops.
move: xe ye => [X Xx] [Y Yy].
move: xsf ysf => /Zo_P [] /setP_P xsr _/Zo_P [] /setP_P ysr _.
move: (xsr _ Xx)(ysr _ Yy) => Xsr Ysr.
have ->: (x = singleton X) by apply: set1_pr => // t tx; apply: sx.
have ->: (y = singleton Y) by apply: set1_pr => // t tx; apply: sy.
by case: (tr _ _ Xsr Ysr) => h; [left | right]; apply/(Exercise1_5cP or).
Qed.

Lemma Exercise1_5h r: order r -> 
  total_order (free_subset_order r) -> total_order r.
Proof.
move=> or tor; split => // x y xsr ysr.
move: tor => [_]; rewrite (proj2 (fs_order_osr or)) => h.
by case: (h _ _  (Exercise1_5b or xsr)  (Exercise1_5b or ysr)) => h1;
   [left | right];apply/Exercise1_5cP.
Qed.

(** ---- Exercise 1.6: Ordering of increasing mappings *)

(** Let [r], [r'] and [r''] be orderings on [E], [F] and [G],
   let [K(E,F)] be the set of mappings [E->F] and
   let [A(E,F)] be the set of increasing mappings [E->F]. 
We first show that [K(E,FxG)] is equipotent to [K(E,F) x K(E,G)]
and this induces a bijection from [A(E,FxG)] onto [A(E,F) x A(E,G)] 
which is an order isomorphism
*)

Definition increasing_mappings r r' :=
  Zo (functions (substrate r) (substrate r'))
  (fun z=> increasing_fun z r r').
Definition increasing_mappings_order r r' :=
  induced_order (order_function (substrate r) (substrate r') r')
  (increasing_mappings r r').


Definition two_projections_increasing r r' r'' :=
  restriction2 (two_projections (substrate r) (substrate r')(substrate r''))
  (increasing_mappings r (order_product2 r' r''))
  ( (increasing_mappings r r') \times
    (increasing_mappings r r'')).


Definition second_partial_map2 r r' r'':=
  Lf (fun f=> restriction2 
    (second_partial_function (substrate r'') (substrate r) (substrate r') f)
    (substrate r) (increasing_mappings r' r''))
  (increasing_mappings (order_product2 r r') r'') 
  (increasing_mappings r (increasing_mappings_order r' r'')).

Section Exercise1_6a.
Variables r r': Set.
Hypotheses (or: order r)(or': order r').

Lemma soimP f:
  inc f (increasing_mappings r r') <->
    ((function_prop f (substrate r) (substrate r'))
    /\ increasing_fun f r r').
Proof. 
split; first by move /Zo_P => [] /functionsP. 
by move  => [pa pd]; apply: Zo_i => //; apply /functionsP.
Qed.

Lemma imo_osr: 
  order_on (increasing_mappings_order r r') (increasing_mappings r r').
Proof.
move: (order_function_osr (substrate r) or'(erefl (substrate r'))) => [pa pb].
apply:(iorder_osr pa); rewrite pb; apply: Zo_S.
Qed.

Lemma imo_gleP f g:
  gle (increasing_mappings_order r r') f g <->
  [/\ inc f (increasing_mappings r r'),
    inc g (increasing_mappings r r') &
    order_function_r (substrate r) (substrate r') r' f g].
Proof.
rewrite /increasing_mappings_order;split.
  move: imo_osr => [or'''  sr0] le1.
  move: (arg1_sr le1) (arg2_sr le1); rewrite sr0 => sr1 sr2. 
  by split => //;  move: (iorder_gle1 le1) => /graph_on_P1 [_ _].
move=> [h1 h2 h3]; apply /(iorder_gle0P _ h1 h2) /graph_on_P1.
by move: h1 h2 => /Zo_S h1 /Zo_S h2. 
Qed.

Lemma imo_incr f g:
   gle (increasing_mappings_order r r') f g ->
   forall i, inc i (substrate r) -> gle r' (Vf f i) (Vf g i).
Proof. by move /imo_gleP => [_ _ [_ _]].  Qed.

End Exercise1_6a.

Section Exercise1_6.
Variables r r' r'': Set.
Hypotheses (or: order r)(or': order r')(or'': order r'').
Let E := substrate r. Let F := substrate r'. Let G := substrate r''.

Lemma Exercise1_6d f:
  increasing_fun f r (order_product2 r' r'') ->
  (increasing_fun (first_projection f E F) r r' /\
    increasing_fun (secnd_projection f E G) r r'').
Proof. 
move=> [_ op [ff sr sor] icf].
rewrite order_product2_sr // in sor.
move: (two_projections_aux  ff sr sor) => [taP taQ fP fQ [WP WQ]].
rewrite /E/increasing_fun /first_projection/secnd_projection; split.
  split => //;[saw | move=> x y xy; rewrite !LfV//; try order_tac].
  by move: (icf _ _ xy) => /order_product2_P [_ _ ][].
split => //; [saw | move=> x y xy; rewrite !LfV//; try order_tac].
by move: (icf _ _ xy) => /order_product2_P [_ _ ][].
Qed. 

Lemma Exercise1_6e: 
  (restriction2_axioms
    (two_projections E F G)
    (increasing_mappings r (order_product2 r' r''))
    ((increasing_mappings r r') \times (increasing_mappings r r''))).
Proof.
move: (two_projections_fb E F G) (@two_projections_ax E F G) => bt t1.
split => //.
+ fct_tac. 
+ rewrite lf_source /increasing_mappings order_product2_sr //;apply: Zo_S.  
+ rewrite lf_target; apply: setX_Slr; apply: Zo_S.
+ move: (bij_function bt) => ff.
  have pa: (sub (increasing_mappings r (order_product2 r' r''))
       (source (two_projections E F G))).
    by move => t; rewrite lf_source  => /Zo_S; rewrite order_product2_sr.
  move=> t /(Vf_image_P ff pa) [u /Zo_P []].
  rewrite order_product2_sr // => aux. 
  move: (aux) => /functionsP [fu su tu].
  move: (two_projections_aux  fu su tu) => [_ _ p1 p2 _] uinc.
  move: (Exercise1_6d uinc) => [i1 i2] ->.
  by rewrite - /two_projections LfV //; apply: setXp_i => //;
       apply : Zo_i => //; apply /functionsP; hnf; rewrite lf_source lf_target.
Qed.

Lemma Exercise1_6f: bijection (two_projections_increasing r r' r'').
Proof.
move: (Exercise1_6e)  (two_projections_fb E F G) => ra [fi fs].
have tpi:=(restriction2_fi fi ra).
split; [ exact | split; first by fct_tac ].
move: ra => [ftp sstp sttp saux].
rewrite corresp_t => y yt.
move: ((proj2 fs) _ (sttp _ yt)) => [x]; rewrite lf_source => xsf wx.
suff xs1: (inc x (increasing_mappings r (order_product2 r' r''))). 
  rewrite corresp_s; ex_tac; rewrite restriction2_V //.
apply: Zo_i => //; first by rewrite order_product2_sr.
move: (xsf) => /functionsP [fx sx tx].
move: (two_projections_aux  fx sx tx)  => [p1 p2 p3 p4 [p5 p6]].
split => //.
    apply: order_product2_or => //.
  rewrite order_product2_sr //.
move=> u v uv; apply /order_product2_P.
have us: (inc u E) by rewrite /E;order_tac.  
have vs: (inc v E) by rewrite /E;order_tac. 
rewrite -tx.
move: (@two_projections_ax E F G) => t1.
move: wx; rewrite /two_projections LfV // => aux.
move:(f_equal P aux) (f_equal Q  aux); aw => q1 q2.
rewrite -(p5 _ us)  -(p5 _ vs) -(p6 _ us)  -(p6 _ vs) -q1 -q2.
move: yt => /setX_P [_ ] /soimP  [_ [_ _ _  ip]] /soimP [_ [_ _ _  iq]]. 
split;[ Wtac | Wtac | split; [ apply: (ip _ _ uv) | apply: (iq _ _ uv) ] ].
Qed.

Lemma Exercise1_6g: 
  order_isomorphism (two_projections_increasing r r' r'')
  (increasing_mappings_order r (order_product2 r' r''))
  (order_product2 (increasing_mappings_order r r') 
    (increasing_mappings_order r r'')). 
Proof. 
have orp: order (order_product2 r' r'') by apply: order_product2_or. 
move: (imo_osr r or') (imo_osr r or'') => [o1 sr1] [o2 sr2].
move: (imo_osr r orp) => [o3 sr3].
split => //; first by apply: order_product2_or => //.
  split => //.
  + by apply: Exercise1_6f. 
  + by rewrite /two_projections_increasing /restriction2 sr3; aw.
  + by rewrite order_product2_sr // sr1 sr2 corresp_t.
hnf;rewrite corresp_s => x y xsi ysi.
move: (xsi) (ysi)=> /(soimP) [[fx sx tx] ix] /(soimP) [[fy sy ty] iy].
move: (@two_projections_ax E F G) => t1.
move: (Exercise1_6e) => ra.
rewrite restriction2_V // restriction2_V //.
rewrite order_product2_sr // in tx ty.
move: (two_projections_aux  fx sx tx)  => [p1 p2 p3 p4 [p5 p6]].
move: (two_projections_aux  fy sy ty)  => [q1 q2 q3 q4 [q5 q6]].
move: ra => []; rewrite lf_source  => ftp sstp sttp saux.
move: (sstp _ xsi) (sstp _ ysi) => xsi' ysi'.
rewrite /two_projections LfV // LfV //.
move: (Exercise1_6d ix) (Exercise1_6d iy).
move: p3 p4 p5 p6 q3 q4 q5 q6.
set (f1 := first_projection x E F).
set (f2 := secnd_projection x E G).
set (f3 := first_projection y E F).
set (f4 := secnd_projection y E G).
move=>  p3 p4 p5 p6 q3 q4 q5 q6 [if1 if2][if3 if4].
split; last first.
  move /order_product2_P => [_ _[] ];rewrite ! pr1_pair ! pr2_pair.
  move /(imo_gleP r or') => [Sf1 Sf3 if13]/(imo_gleP r or'') [Sf2 Sf4 if24].
  apply /(imo_gleP r orp);rewrite order_product2_sr //;split => //; split => //.
  move=> i isr; apply /order_product2_P; rewrite - {1} tx -ty.
  rewrite -(q5 _ isr) - (q6 _ isr) -(p5 _ isr) - (p6 _ isr).
  move: if13 if24 => [_ _  s1] [_ _ s2].
  split; [ Wtac |  Wtac | split; fprops].
move => xx; move: (imo_incr orp xx) => h3.
move /(imo_gleP r orp):xx => [h1 h2 _].
apply /order_product2_P; rewrite sr1 sr2.
have sf1: (source f1 = E) by rewrite /f1 /first_projection; aw.
have sf2: (source f2 = E) by rewrite /f2 /secnd_projection; aw.
have sf3: (source f3 = E) by rewrite /f3 /first_projection; aw.
have sf4: (source f4 = E) by rewrite /f4 /secnd_projection; aw.
have tf1: (target f1 = F) by rewrite /f1 /first_projection; aw.
have tf2: (target f2 = G) by rewrite /f2 /secnd_projection; aw.
have tf3: (target f3 = F) by rewrite /f3 /first_projection; aw.
have tf4: (target f4 = G) by rewrite /f4 /secnd_projection; aw.
have Sf1: (inc f1 (increasing_mappings r r'))  by apply /soimP.
have Sf2: (inc f2 (increasing_mappings r r'')) by apply /soimP.
have Sf3: (inc f3 (increasing_mappings r r')) by apply /soimP.
have Sf4: (inc f4 (increasing_mappings r r'')) by apply /soimP.
split; [by apply setXp_i | by apply setXp_i | aw; split].
   apply /(imo_gleP r or');split => //; split => //.
   move=> i isr; rewrite (p5 _ isr) (q5 _ isr).
   by move: (h3 _ isr) => /order_product2_P [_ _ []].
apply /(imo_gleP r or'');split => //; split => //.
move=> i isr; rewrite (p6 _ isr) (q6 _ isr).
by move: (h3 _ isr) => /order_product2_P  [_ _ []].
Qed.

(** We show that [A(ExF,G)] is isomorphic to [A(E, A (F,G))] *)

Lemma Exercise1_6h f:
  nonempty E -> nonempty F -> increasing_fun f (order_product2 r r') r'' ->
 ( (domain (source f)) = E /\ (range (source f)) = F).
Proof. 
move=> ne1 ne2 [_ _ [_ sf _ ] _].
move: sf; rewrite order_product2_sr//.
by move ->; rewrite (setX_domain _ ne2)(setX_range _ ne1). 
Qed.

Lemma Exercise1_6i f x:
  nonempty E -> nonempty F ->
  increasing_fun f (order_product2 r r') r'' ->
  inc x E -> increasing_fun (second_partial_fun G  F f x) r' r''.
Proof. 
move=> ne1 ne2 incf xsr.
move: (Exercise1_6h ne1 ne2 incf) => [dsf rsf].
move: incf => [op or''' [ff sf tf] incf].
move: sf; rewrite order_product2_sr // => sf.
have ax: inc f (functions (E \times F) G) by apply/functionsP.
move: (spf_f ax xsr) => spf.
split => //; [by split => //; rewrite /second_partial_fun; aw | move=> u v uv].
have us: (inc (J x u) (source f)). 
  by rewrite sf; apply : setXp_i => //; order_tac.
have vs: (inc (J x v) (source f)) 
  by rewrite sf; apply : setXp_i => //; order_tac.
have ur: inc u F by rewrite /F; order_tac.
have vr: inc v F by rewrite  /F; order_tac.
rewrite (spf_V ax xsr ur) (spf_V ax xsr vr); apply: incf.
by apply/order_product2_P; aw; rewrite - sf;split => //; split => //;order_tac. 
Qed.

Lemma Exercise1_6j f:
  nonempty E -> nonempty F ->
  increasing_fun f (order_product2 r r') r'' ->
  (restriction2_axioms (second_partial_function G E F f) E
  (increasing_mappings r' r'')).
Proof.
move=> ne1 ne2 incf.
move: (Exercise1_6h ne1 ne2 incf) => [dsf rsf].
move: (incf) => [op or''' [ff sf tf] icf].
move: sf; rewrite order_product2_sr // => sf.
have ax: inc f (functions (E \times F) G) by apply/functionsP.
move: (spfa_f ax) => spfa.
split => //.
    rewrite lf_source; fprops.
  rewrite lf_target; apply:Zo_S.
have aa: sub E (source (second_partial_function G E F f)). 
  rewrite lf_source; fprops.
move=> t /(Vf_image_P spfa aa) [x xsr ->]. 
move: (Exercise1_6i ne1 ne2 incf xsr) => h.
move: (spf_f ax xsr) => spf.
rewrite (LfV (spfa_axiom ax) xsr); apply /soimP; split => //.
by hnf; rewrite lf_source lf_target.
Qed.

Lemma Exercise1_6k:
  nonempty E -> nonempty F ->
  lf_axiom (fun f=> restriction2 
    (second_partial_function G E F f) E (increasing_mappings r' r''))
  (increasing_mappings (order_product2 r r') r'') 
  (increasing_mappings r (increasing_mappings_order r' r'')).
Proof.
move=> ne1 ne2.
have o1: order (order_product2 r r') by apply: order_product2_or.
move: (imo_osr r' or'') => [o2 sr2].
move=> t /soimP [[ft st tt] int].
move: (Exercise1_6j ne1 ne2 int) => ra.
move: (Exercise1_6h ne1 ne2 int) => [dst rst].
move: st; rewrite order_product2_sr // => st.
have ax: inc t (functions  (E \times F) G) by apply/functionsP.
set g:= restriction2 _ _ _. 
have fg: function g by rewrite /g; apply: (proj31(restriction2_prop ra)).
have sg: source g = E by rewrite /g /restriction2; aw. 
have tg: target g = substrate (increasing_mappings_order r' r'').
  by rewrite sr2 /g /restriction2; aw.
apply /soimP; split => //; split => //.
move => x y xy. 
have xsr: (inc x E) by rewrite /E; order_tac.  
have ysr: (inc y E) by rewrite /E; order_tac. 
rewrite /g restriction2_V // restriction2_V // spfa_V // spfa_V //. 
apply /imo_gleP => //.
move:(Exercise1_6i ne1 ne2 int xsr)(Exercise1_6i ne1 ne2 int ysr).
move=> inc1 inc2; move: (inc1)(inc2).
move => [_ _ [fsx ssx tsx] isx] [_ _ [fsy ssy tsy] isy].
split; [ by apply /soimP | by  apply /soimP |  split => //].
move => i isr; rewrite (spf_V ax xsr isr); rewrite (spf_V ax ysr isr).
have Js: (inc (J x i) (source t)) by  rewrite st; apply /setXp_i.
have Js': (inc (J y i) (source t)) by  rewrite st; apply /setXp_i.
apply: (proj44 int).
apply /order_product2_P;saw; try apply /setXp_i => //. 
split => //; order_tac => //;ue.
Qed.


Lemma Exercise1_6l:
  nonempty E -> nonempty F ->
    bijection_prop (second_partial_map2 r r' r'' )
      (increasing_mappings (order_product2 r r') r'') 
      (increasing_mappings r (increasing_mappings_order r' r'')).
Proof. 
move=> ne1 ne2.
rewrite /second_partial_map2;saw. 
have op:=(order_product2_or or or').
have sop:=(order_product2_sr or or').
apply: lf_bijective.
    by apply: Exercise1_6k. 
  move=> u v /soimP [[fu su tu] iu] /soimP [[fv sv tv] iv] sr.
  apply: function_exten => //; try ue. 
  move: su sv; rewrite sop -/E -/F => su sv x xsu.
  have axu: inc u (functions  (E \times F) G) by apply/functionsP.
  have axv: inc v (functions  (E \times F) G) by apply/functionsP.
  move: (Exercise1_6h ne1 ne2 iu) => [dsu rsu].
  move: (Exercise1_6h ne1 ne2 iv) => [dsv rsv].
  have ssp: (second_partial_function G E F u = second_partial_function G E F v).
    apply: function_exten. 
    + by apply: spfa_f.
    + by apply: spfa_f.
    + by rewrite /second_partial_function; aw; ue. 
    + by rewrite /second_partial_function; aw; trivial; rewrite rsu rsv tu tv.
    + move=> a; rewrite lf_source => au.
     transitivity (Vf (restriction2 (second_partial_function G E F u) E
       (increasing_mappings r' r'')) a); [ | rewrite sr];
        rewrite restriction2_V //; apply: Exercise1_6j => //.
  move: (xsu); rewrite  su; move /setX_P => [px Ps Qr].
  move: (spfa_V axu Ps) (spf_V axu Ps Qr); rewrite px  => <- <-.
  move: (spfa_V axv Ps) (spf_V axv Ps Qr); rewrite px  => <- <-; ue.
move: (imo_osr r' or'') => [o2 sr2].
move=> y /soimP  [[fy sy ty] incy].
have ta: (lf_axiom (fun z => Vf (Vf y (P z)) (Q z) ) (E \times F) G).
  move => t /setX_P; rewrite /E - sy; move=> [prt Pt Qt].
  move: (Vf_target fy Pt); rewrite ty sr2 /G //.
  move /soimP => [[fw sw <-] _]; Wtac; ue.
set (g:= Lf (fun z => Vf (Vf y (P z)) (Q z) ) (E \times F) G).
have fg: function g by apply: lf_function.
have ig: (increasing_fun g (order_product2 r r') r'').
  split => //; first by split;[done | rewrite /g; aw | rewrite /g; aw ].
  move=> u v /order_product2_P [us vs [le1 le2]].  
  rewrite /g LfV // LfV //.
  move: us vs; rewrite - sy => /setX_P [pu Pu Qu] /setX_P [pv Pv Qv].
  move: (Vf_target fy Pu) (Vf_target fy Pv). 
  rewrite ty sr2 //; move/soimP => [[f1 s1 t1] i1]/soimP  [[f2 s2 t2] i2].
  move: i2 => [_ _ [fw sw tw] iw]; move: (iw _ _ le2) => h'.
  have h: (gle r'' (Vf (Vf y (P u)) (Q u)) (Vf (Vf y (P v)) (Q u))).  
    move: incy => [_ _ [f3 s3 t3] i3].
    by move: (imo_incr or'' (i3 _ _ le1) Qu).
  order_tac.
have sg: source g = (E \times F) by rewrite /g;aw.
have sg1: (range (source g) = F) by  rewrite sg setX_range.
have tg: target g = G  by rewrite /g; aw.
have axg: inc g (functions  (E \times F) G) by apply/functionsP.
exists g; first by apply /soimP; split => //; split => //; ue.
apply: function_exten.
- exact.
- exact (proj31 (restriction2_prop (Exercise1_6j ne1 ne2 ig))).
- by rewrite /restriction2; aw. 
- by rewrite /restriction2 ty sr2 //; aw. 
- move => x xs /=. 
rewrite restriction2_V //; [ | by apply: Exercise1_6j | ue ].
have xE: inc x E by rewrite /E - sy.
rewrite spfa_V //.
move: (Vf_target fy xs); rewrite ty sr2 //.
move=> /soimP [[fw sw tw] iw].
apply: function_exten => //.
- by apply: ( spf_f  axg).
- by rewrite /second_partial_fun; aw; ue.
- by rewrite /second_partial_fun;aw; ue.
- rewrite sw; move => i isr /=; rewrite (spf_V axg xE isr) /g LfV//; aw=> //.
  by apply /setXp_i. 
Qed.

Lemma Exercise1_6m:
  nonempty E -> nonempty F ->
  order_isomorphism (second_partial_map2 r r' r'')
  (increasing_mappings_order (order_product2 r r') r'')
  (increasing_mappings_order r (increasing_mappings_order r' r'')).
Proof. 
move=> ne1 ne2.
move: (Exercise1_6l ne1 ne2). 
set f := (second_partial_map2 r r' r''); move=> [bf sf tf].
have ta:= (Exercise1_6k ne1 ne2).
have [o2 sr2]:= (imo_osr r' or'').
have o3:order (order_product2 r r') by apply: order_product2_or.
have [o2' sr2']:= (imo_osr (order_product2 r r') or'').
have [o2'' sr2''] := (imo_osr r o2).
split => //; first by rewrite sr2' sr2''.
move=> x y xsf ysf. 
have sop:= (order_product2_sr or or').
move: (xsf) (ysf); rewrite sf; move /soimP => [[fx sx tx] ix].
move /soimP => [[fy sy ty] iy].
rewrite sop in sx sy.
have axx: inc x (functions  (E \times F) G) by apply/functionsP.
have axy: inc y (functions  (E \times F) G) by apply/functionsP.
have ff: function f by fct_tac.
have u1p: inc (Vf (second_partial_map2 r r' r'') x)
    (target (second_partial_map2 r r' r''))  by Wtac.
have u2p: inc (Vf (second_partial_map2 r r' r'') y)
    (target (second_partial_map2 r r' r'')) by Wtac.
move: (Exercise1_6j ne1 ne2 ix)(Exercise1_6j ne1 ne2 iy) => ta1 ta2.
split.
  move /(imo_gleP _ or'') => [_ _  incx].
  apply /(imo_gleP _ o2);rewrite -tf; split => //.
  rewrite /f LfV //; last (by ue);rewrite LfV //; last (by ue).
  split => //; rewrite ? sr2.
      split => //;rewrite /restriction2; aw; trivial.
      by apply: (proj31 (restriction2_prop ta1)).
    split => //;rewrite /restriction2; aw; trivial.
    by apply: (proj31 (restriction2_prop ta2)).
  move => i isr; rewrite restriction2_V //restriction2_V //.
  rewrite spfa_V // spfa_V //; apply /(imo_gleP _ or'').
  have in1:= (Exercise1_6i ne1 ne2 ix isr).
  have in2 :=(Exercise1_6i ne1 ne2 iy isr).
  move: (in1)(in2) => [_ _ [f1 s1 s'1] i1] [_ _ [f2 s2 s'2] i2].
  split => //; try apply /soimP;split => //. 
  move=> j jsr'.
  rewrite (spf_V axx isr jsr') (spf_V axy isr jsr').
  apply: (proj33 incx); rewrite sop; fprops.
move => h.
apply /(imo_gleP _ or''); rewrite - sf; split => //; hnf; rewrite sop.
split => // i /setX_P [pi Pi Qi].
rewrite - pi; move:(imo_incr o2 h Pi).
rewrite /f LfV //; last (by ue);rewrite LfV //; last (by ue).
rewrite restriction2_V // restriction2_V // spfa_V // spfa_V //.
move => h1; move: (imo_incr or'' h1 Qi). by 
rewrite (spf_V axx Pi Qi) (spf_V  axy Pi Qi).
Qed. 

Lemma Exercise1_6m':
  (increasing_mappings_order (order_product2 r r') r'') \Is
  (increasing_mappings_order r (increasing_mappings_order r' r'')).
Proof.
case: (p_or_not_p (nonempty E /\ nonempty F)) => H.
  move: H => [pa pb]; exists (second_partial_map2 r r' r'').
  by apply: Exercise1_6m.
have esa: (E \times F) = emptyset.
  case: (emptyset_dichot E); first by move => ->; rewrite setX_0l.
  case: (emptyset_dichot F);first by move => ->; rewrite setX_0r.
  by move => n1 n2; case: H. 
have: (substrate (order_product2 r r')) = emptyset.
  by rewrite (order_product2_sr or or').
have: order (order_product2 r r') by apply: order_product2_or.
set r3:= (order_product2 r r').
move => or3 sr3.
case: (imo_osr r' or'');set r2 := (increasing_mappings_order r' r'') => or2 sr2.
have [or4 sr4]:= (imo_osr r3 or'').
have [or5 sr5]:= (imo_osr r or3).
have [or6 sr6]:= (imo_osr r or2).
have ssa:=  functions_empty.
have ssb: forall ra rb, order ra -> order rb -> substrate ra = emptyset ->
  substrate  (increasing_mappings_order ra rb) =
  singleton (empty_function_tg (substrate rb)).
  move => ra rb ora orb h.
  rewrite (proj2 (imo_osr _ orb)) /increasing_mappings h.
  rewrite (ssa (substrate rb)).
  move:(empty_function_tg_function  (substrate rb)) => [wa wb wc].
  set_extens t; first by case /Zo_P.
  move => ta; apply: Zo_i => //; move /set1_P:ta => ->;split => //. 
    split => //;ue.
  move => x y le. 
  have: inc x (substrate ra) by order_tac.
  by rewrite h => /in_set0.
move: (ssb _ _ or3 or'' sr3).
set f0 := (empty_function_tg G); move => ssrc.
have si: singletonp (substrate (increasing_mappings_order r r2)).
  case: (emptyset_dichot E) => h.
    rewrite (ssb _ _ or or2 h).
    by exists (empty_function_tg (substrate r2)).
  case: (emptyset_dichot F) => h1; last by case: H;split => //.
  rewrite sr6.
  move: (ssb _ _ or' or'' h1).
  set f1:= (empty_function_tg G) => sr2'.
  set f := Lf (fun _ => f1) E (substrate r2).
  have ta: lf_axiom (fun _ => f1) E (substrate r2). 
    move => t _ ; rewrite sr2'; fprops.
  have ff: function f by apply: lf_function.
  exists f; apply :set1_pr.
    rewrite /f;apply: Zo_i; first by apply/functionsP;saw.  
    split => //; first by saw.
    move => x y lexy; rewrite /E !LfV//; order_tac;rewrite sr2'; fprops.
  move =>t /Zo_P [] /functionsP [ft st tt] _; rewrite /f. 
  apply: function_exten; aw; trivial; rewrite /E => x xst /=; rewrite LfV//; last by ue. 
  by move: (Vf_target ft xst); rewrite tt sr2' => /set1_P ->.
move: si => [w ws].
have ta: lf_axiom (fun _ => w) (singleton f0) (singleton w).
   move => t _ /=; fprops.
exists (Lf (fun z => w) (singleton f0)(singleton w)).
split => //.
  saw; try ue; apply: lf_bijective.
  + done.
  + by move => u v /set1_P -> /set1_P ->. 
  + move => y /set1_P ->; exists f0;fprops.
move => x y; rewrite lf_source; move => pa pb; aw.
move: pa pb =>  /set1_P -> /set1_P ->;split => h; order_tac.
  rewrite ws !LfV//;fprops.
rewrite ssrc; aww.
Qed.


(** We show that [A(E,F)] is a lattice iff [F] is a lattice by 
considering constant functions  *)

Lemma constant_increasing  y: inc y F ->
    (inc (constant_function E F y) (increasing_mappings r r')).
Proof.
move => yF;move:(constant_prop E yF) => fp; apply /soimP; split => //.
rewrite /E;split => // u v uv. 
rewrite (constant_V yF); last by order_tac.
by rewrite (constant_V yF); order_tac.
Qed.

Lemma constant_increasing1: 
  nonempty E ->
  forall y y', inc y F -> inc y' F ->
    (gle r' y y' <->
    gle (increasing_mappings_order r r')
    (constant_function E F y)
    (constant_function E F y')).
Proof. 
move=>  [u usr] y y' ysr ysr'.
split; last by move => h; move: (imo_incr or' h usr); rewrite !constant_V.
move:(constant_increasing ysr)(constant_increasing ysr') => pa pb.
move:(constant_prop E ysr)(constant_prop E ysr') => pc pd.
move=> yy'; apply /imo_gleP => //;split => //; split => //.
by move => i isr; rewrite ! constant_V.
Qed.

Lemma Exercise1_6n:  nonempty E ->
  (lattice r' <-> lattice (increasing_mappings_order r r')).
Proof.
move=>  ne1; split.
  move:(imo_osr r or') => [pa pb].
  move=> sl; split => //; rewrite pb.
  move=> x y xs ys. 
  move: (xs)(ys) => /soimP [[fx sx tx] ix] /soimP [[fy sy ty] iy].
  have Ha: forall c, inc c E -> (inc (Vf x c) F)  /\  (inc (Vf y c) F).
    move => c cE; rewrite /F -{1} tx - ty;split; apply: Vf_target =>//; ue.
  have ta1: (lf_axiom (fun i=> sup r' (Vf x i) (Vf y i)) E F). 
    move => c cE; move: (Ha _ cE) => [w1 w2].
    move: (lattice_sup_pr sl w1 w2)=> [aux _ _]; rewrite /F; order_tac.
  have ta2: (lf_axiom (fun i=> inf r' (Vf x i) (Vf y i)) E F). 
    move => c cE;  move: (Ha _ cE) => [w1 w2].
    move: (lattice_inf_pr sl w1 w2)=> [aux _ _]; rewrite /F; order_tac.
  set (f1:= Lf (fun i=> sup r' (Vf x i) (Vf y i)) E F).
  set (f2:= Lf (fun i=> inf r' (Vf x i) (Vf y i)) E F).
  have ff1: (function f1) by rewrite /f1; apply: lf_function.
  have ff2: (function f2) by rewrite /f1; apply: lf_function.
  have fp1: function_prop f1 E F by rewrite/f1; saw.
  have fp2: function_prop f2 E F by rewrite/f2; saw.
  have if1:increasing_fun f1 r r'. 
    split => //; rewrite /f1; aw => u v uv.
    have uE: (inc u E) by rewrite /E;order_tac.
    have vE: (inc v E) by rewrite /E;order_tac.
    move:(Ha _ uE)(Ha _ vE) => [uxE uyE] [vxE vyE].
    rewrite !LfV//. 
    move: (lattice_sup_pr sl uxE uyE) (lattice_sup_pr sl vxE vyE).
    move=> [p1 p2 p3] [p4 p5 p6].
    have le1:(gle r'  (Vf x u) (Vf x v)) by apply: (proj44 ix).
    have le2:(gle r'  (Vf y u) (Vf y v)) by apply: (proj44 iy).
    apply: p3; order_tac. 
  have if2:increasing_fun f2 r r'. 
  split => //;  rewrite /f2. 
    move=> u v uv.
    have uE: (inc u E) by rewrite /E;order_tac.
    have vE: (inc v E) by rewrite /E;order_tac.
    move:(Ha _ uE)(Ha _ vE) => [uxE uyE] [vxE vyE].
    rewrite !LfV//;move:(lattice_inf_pr sl uxE uyE) (lattice_inf_pr sl vxE vyE).
    move=> [p1 p2 p3] [p4 p5 p6].
    have le1:(gle r' (Vf x u) (Vf x v)) by apply: (proj44 ix).
    have le2:(gle r' (Vf y u) (Vf y v)) by apply: (proj44 iy).
    apply: p6; order_tac. 
  have sif1: inc f1 (increasing_mappings r r'). 
     rewrite /f1;apply /soimP=> //;saw; saw.
  have sif2: inc f2 (increasing_mappings r r').
     rewrite /f2;apply /soimP=> //;saw; saw.
  move: (imo_osr r or') => [o2 s2].
  have sd:sub (doubleton x y) (substrate (increasing_mappings_order r r')).
    by move=> t; case /set2_P => -> //; rewrite s2. 
  split.
    exists f1; apply /lubP =>//;split.
      split; first by rewrite s2.
      move=> u; case /set2_P => ->; apply /imo_gleP => //;split => //.
        split => //; rewrite /f1; move => i isr; rewrite LfV //.
        by move: (Ha _ isr) => [wxe wye];case: (lattice_sup_pr sl wxe wye).
      split => //;rewrite /f1; move => i isr; rewrite LfV //.
      by move: (Ha _ isr) => [wxe wye];case: (lattice_sup_pr sl wxe wye).
    move=> z [z1 z2].
    move: (imo_incr or' (z2 _ (set2_1 x y))) => inx.
    move: (z2 _ (set2_2 x y)) => /(imo_gleP _ or') [_ p1 [xx fz hh]].
    rewrite /f1; apply /(imo_gleP _ or');split => //;split => //; aw.
    move=> i isr; rewrite LfV //.
    move: (inx _ isr) (hh _ isr) => r1 r2; move:(Ha _ isr) => [xwe ywe].
    by move: (lattice_sup_pr sl xwe ywe)=> [r3 r4]; apply.  
  exists f2; apply /glbP=> //;split. 
    split; first by rewrite s2 //. 
    move=> u; case /set2_P => ->; apply /(imo_gleP _ or');split => //.
      rewrite /f2; saw;try saw.
      move => i isr; rewrite LfV //; move:(Ha _ isr) => [xwe ywe].
      by case: (lattice_inf_pr sl xwe ywe).
    rewrite /f2;saw; try saw; move => i isr; rewrite LfV //. 
    by move:(Ha _ isr) => [xwe ywe];case: (lattice_inf_pr sl xwe ywe).
  move=> z [z1 z2].
  move: (imo_incr or'  (z2 _ (set2_1 x y))) => inx.
  move: (z2 _ (set2_2 x y))  => /(imo_gleP _ or') [p1 p2 [p3 p4 p5]].
  rewrite /f2; apply /(imo_gleP _ or');split => //; saw. 
  move=> i isr; rewrite LfV => //;  move:(Ha _ isr) => [xwe ywe].
  move: (inx _ isr) (p5 _ isr) => r1 r2.
  by move: (lattice_inf_pr sl xwe ywe)=> [r3 r4]; apply.
move=> sl; split; first by exact.
move=> x y xsr ysr.
set (f1:= constant_function E F x).
set (f2:= constant_function E F y).
have f1s: (inc f1 (increasing_mappings r r')) by apply: constant_increasing.
have f2s: (inc f2 (increasing_mappings r r')) by apply: constant_increasing.
move:(proj2 (imo_osr r or')) => sr2.
move: (f1s)(f2s); rewrite - sr2 => f1si f2si.
set (r''':= increasing_mappings_order r r') in *.
have sd:sub (doubleton x y) (substrate r') by move=> t; case /set2_P=> ->. 
move: (ne1) => [t te].
split. 
  move: (lattice_sup_pr sl f1si f2si) => [l1 l2 l3].
  have: (inc  (sup r''' f1 f2) (substrate r''')) by order_tac.
  rewrite  {2} /r''' sr2 =>  /soimP [[fs ss ts] ifs].
  set z := Vf  (sup r''' f1 f2) t.
  have wt: (inc z F) by rewrite /z/F -ts; Wtac; ue.
  have xz: gle r' x z. 
     move: (imo_incr or' l1 te); rewrite {1} /f1 constant_V //.
  have yz: gle r' y z.
    move: (imo_incr or' l2 te); rewrite {1} /f1 constant_V //.
  exists z; apply /lubP => //; split.
    split; [ exact | by move=> u; case /set2_P => ->].
  move=> u [usr um]. 
  set (f4:= constant_function E F u).
  have f4s:(inc f4 (increasing_mappings r r')) by apply: constant_increasing.
  have f14: (gle (increasing_mappings_order r r') f1 f4).
    rewrite /f1/f4 /E/F - constant_increasing1 //; apply: um; fprops.
  have f24: (gle (increasing_mappings_order r r') f2 f4).
    rewrite /f1/f4 /E/F - constant_increasing1 //; apply: um; fprops.
  by move: (imo_incr or' (l3 _ f14 f24) te);rewrite -/r'' -/z /f4 constant_V.
move: (lattice_inf_pr sl f1si f2si) => [l1 l2 l3].
have: (inc  (inf r''' f1 f2) (substrate r''')) by order_tac.
rewrite  {2} /r''' sr2;move /soimP => [[fs ss ts] ifs].
set z := Vf (inf r''' f1 f2) t.
have wt: (inc z F) by rewrite /z/F -ts; Wtac; ue.
have yz: gle r' z y by move: (imo_incr or' l2 te); rewrite {1} /f1 constant_V.
have xz: gle r' z x by move: (imo_incr or' l1 te); rewrite {1} /f1 constant_V.
exists z; apply /glbP => //; split.
  split; [ exact | by move=> u; case /set2_P => ->].
move=> u [usr um]. 
set (f4:= constant_function E F u).
have f4s:(inc f4 (increasing_mappings r r'))  by apply: constant_increasing.
have f14: (gle (increasing_mappings_order r r') f4 f1).
  rewrite /f1/f4 /E/F - constant_increasing1 //; apply: um; fprops.
have f24: (gle (increasing_mappings_order r r') f4 f2).
  rewrite /f1/f4 /E/F - constant_increasing1 //; apply: um; fprops.
by move: (imo_incr or' (l3 _ f14 f24) te); rewrite -/r'' -/z /f4 constant_V.
Qed.

(** we study when [A(E,F)] is totally ordered *)

Lemma Exercise1_6o:  nonempty E ->
  total_order (increasing_mappings_order r r') ->
  total_order r'.
Proof. 
move=>  [t te] [orf torf].
split => // x y xsr ysr.
move: (constant_increasing xsr) (constant_increasing ysr).
rewrite (proj2 (imo_osr r or')) in torf.
by move => p1 p2; case: (torf _ _ p1 p2) => h; move: (imo_incr or' h te); 
  rewrite !constant_V // => h1 ; [left | right].
Qed.

Lemma Exercise1_6p: 
  singletonp F ->
  total_order (increasing_mappings_order r r').
Proof.
move /singletonP => [_ s].
move: (imo_osr r or') => [pa pb].
split => //; rewrite pb => x y xs ys; left; rewrite imo_gleP//; split => //. 
move: xs ys => /soimP [[fx sx tx] ix] /soimP [[fy sy ty] iy].
split => // i isr.
have w1: (inc (Vf x i) F) by rewrite /F -tx; Wtac; ue. 
have w2: (inc (Vf y i) F) by rewrite /F -ty; Wtac; ue.
by rewrite (s _ _ w1 w2); order_tac.
Qed.

Lemma Exercise1_6q: 
  singletonp E -> total_order r' ->
  total_order (increasing_mappings_order r r').
Proof.
move=> [s sr] [orf torf].
move: (imo_osr r or') => [pa pb].
split => //; rewrite pb=> x y xs ys.
move: (xs)(ys) => /soimP [[fx sx tx] ix] /soimP [[fy sy ty] iy].
move: (sx)(sy); rewrite -/E sr=> sx' sy'.
have w1:(inc (Vf x s) F) by rewrite /F -tx; Wtac; ue.
have w2:(inc (Vf y s) F) by rewrite /F -ty; Wtac; ue.
case: (torf _ _ w1 w2) => h; [left | right ];
by apply /imo_gleP => //;split => //; split => // i isr; 
   move: isr; rewrite -/E sr => /set1_P ->.
Qed.

Lemma Exercise1_6r: 
  total_order r -> total_order r' ->
  (exists a b, F = doubleton a b) ->
  total_order (increasing_mappings_order r r').
Proof. 
move=> [_ tor] [_ tor'] [u [v sr']].
case: (equal_or_not u v) => uv.
  by apply: Exercise1_6p => //; rewrite sr' -uv; exists u.
have [a [b [ab aF bF ltab]]]: exists a b, 
  [/\ F = doubleton a b, inc a F, inc b F & glt r' a b].
  have ap: (inc u F) by rewrite  sr'; fprops.
  have bp: (inc v F) by rewrite sr'; fprops.
  case: (tor' _ _ ap bp) => le1.
    exists u, v; split => //; split =>//.
  by exists v, u; rewrite set2_C; split => //; split =>//; apply:nesym.
clear sr' uv u v.
move: (imo_osr r or') => [pa1 pb1].
split => //.
rewrite pb1; move=> x y xs ys; rewrite /ocomparable.
move: (xs)(ys) => /soimP [[fx sx tx] ix] /soimP [[fy sy ty] iy].
have Ha: forall c, inc c E -> (inc (Vf x c) F)  /\  (inc (Vf y c) F).
    move => c cE; rewrite /F -{1} tx - ty;split; apply: Vf_target =>//; ue.
have aux: (forall t, inc t E -> glt r' (Vf x t) (Vf y t) ->
    (Vf x t = a /\ Vf y t = b)).
  move=> t tsr wt; move: (Ha _ tsr) (wt) => [].
  rewrite -/F ab; case /set2_P => -> ; case /set2_P  => -> //;
     [by case | by move => [ha _]; order_tac | by case].
case: (p_or_not_p (exists2 u, inc u E & glt r' (Vf x u) (Vf y u))).
  move=> [u usr uwy]; left.
  apply /imo_gleP => //; split => //; split => // i isr.
  move: (Ha _ isr) => [];rewrite ab; case /set2_P => h1; case /set2_P => h2; 
   rewrite h1 h2;try order_tac => //.
  move: (aux _ usr uwy) => [h3 h4].
  move: ix iy => [_ _ _ ix] [_ _ _ iy].
  by case: (tor _ _ usr isr) => h5; move: (ix _ _ h5) (iy _ _ h5);
     rewrite h2 h3 h4 h1.
move=> neu; right; apply /imo_gleP => //; split => //;split => //.
move=> i isr;move: (Ha _ isr) => [xw yw].
case: (tor' _ _ xw yw) => //.
case: (equal_or_not  (Vf x i) (Vf y i)) =>sw; first by rewrite sw.
by move=> nle; case: neu; ex_tac. 
Qed.

Lemma Exercise1_6s: 
  nonempty E -> nonempty F ->
  (total_order (increasing_mappings_order r r') <->
    [\/ singletonp F,
      (singletonp E /\ total_order r') |
      [/\ total_order r', total_order r &
         exists u v, F = doubleton u v]]).
Proof. 
move=> ne1 ne2.
split;last first.
  case; first by apply: Exercise1_6p.
    by move=> [h1 h2];apply:  Exercise1_6q.
  by move=> [h1 [h2 h3]]; apply: Exercise1_6r.
move => tor; move: (Exercise1_6o ne1 tor) => tor'.
move: (tor') => [_ tor''].
move: (ne2) => [y yF].
case: (equal_or_not F (singleton y))=> Fp; first by constructor 1; exists y. 
move: (ne1) => [z zE].
case: (equal_or_not E (singleton z))=> Ep.
  by constructor 2; split => //;exists z. 
constructor 3.
have [y' yF' yy']: (exists2 y1, inc y1 F & y1 <> y). 
  ex_middle h; case: Fp; set_extens t. 
     case: (equal_or_not t y); first by move => ->; fprops.
     move => ty ts; case: h;ex_tac.
   by move /set1_P => ->.
have [a [b [aF bF ltab]]]: exists a b, [/\ inc a F, inc b F & glt r' a b].
  case: (tor'' _ _ yF yF').
    by move => aux; exists y, y'; split => //; split => //; apply:nesym.
    rewrite /glt;move => aux; exists y', y;split => //.
clear yF yF' Fp  yy' y y'.
set sf:= fun x a b u => Yo (gle r u x) a b.
have sfa: forall x a b, inc a F -> inc b F -> (lf_axiom (sf x a b) E F).
  by rewrite /sf=> x v w vF wF u uE; case: (p_or_not_p (gle r u x)) => h; Ytac0.
have sfb:  forall x  a b, inc a F -> inc b F ->  glt r' a b ->
   (inc (Lf (sf x a b) E F) (increasing_mappings r r')). 
  move => x a' b' aF' bF' latab'; move: (sfa x _ _ aF' bF') => ta.
  move: (lf_function ta) => fb.
  apply /soimP => //;saw; saw; first  saw.
  move=> u v uv.
  have us: (inc u E) by rewrite /E;order_tac.
  have vs: (inc v E) by rewrite /E;order_tac.
  rewrite LfV // LfV // /sf.
  case: (p_or_not_p (gle r u x)) => ux; Ytac0; 
      case: (p_or_not_p (gle r v x)) => vx; Ytac0; try order_tac => //.
  case: ux; order_tac.
have to: (total_order r). 
  split=> //; rewrite -/E => x y xsr ysr.
  move: (sfb x _ _ aF bF ltab) (sfb y _ _ aF bF ltab) => fx fy.
  move: tor => [_]; rewrite (proj2 (imo_osr r or')) => aux; red.
  case: (p_or_not_p (gle r x y)); first by left.
  case: (p_or_not_p (gle r y x)); first by right.
  move=> be1 be2.
  have sfxx: sf x a b x = a by rewrite /sf Y_true //; order_tac.
  have sfyy: sf y a b y = a by rewrite /sf Y_true //; order_tac.
  have sfxy: sf x a b y = b by rewrite /sf Y_false//; order_tac.
  have sfyx: sf y a b x = b by rewrite /sf Y_false//; order_tac.
  move: (sfa x _ _ aF bF)(sfa y _ _ aF bF) => h1 h2.
  case: (aux _ _ fx fy) => h;
    move : (imo_incr or' h xsr)  (imo_incr or' h ysr); 
      rewrite !LfV// sfxx sfyx sfyy sfxy; move=> h3 h4; order_tac.
split => //.
case: (equal_or_not F (doubleton a b)); first by move=> h; exists a,b.
move=> at2.
have at3: exists c, [/\ inc c F, c <> a & c <> b].
  ex_middle at3; case: at2; set_extens t. 
    case: (equal_or_not t a); first by  move => ->; fprops. 
    case: (equal_or_not t b); first by  move => ->; fprops. 
    by move => tb ta ts; case: at3; exists t.
  by case/set2_P => ->.
have [u [v [w [uF vF wF uv vw]]]]: (exists u v w, 
   [/\ inc u F, inc v F, inc w F, glt r' u v & glt r' v w]).  
   move: at3 => [c [cF ca cb]]; case: (tor'' _ _ cF aF)=> lca.
    by exists c, a, b. 
   case: (tor'' _ _ bF cF) => lbc.
      by exists a, b, c; split => //; split => //;apply:nesym.
   by exists a, c, b;  split => //; split => //; apply:nesym.
set (f:= constant_function (substrate r)  F v).
have fs:(inc f (increasing_mappings r r'))  by apply: constant_increasing.
have [z' zE' zz']: (exists2 y1, inc y1 E & y1 <> z). 
  ex_middle h; case: Ep; set_extens t. 
     case: (equal_or_not t z); first by move => ->; fprops.
     move => ty ts; case: h; ex_tac.
   by move /set1_P => ->.
have [i [s [iF sF ltis]]]: exists i s, [/\ inc i E, inc s E & glt r i s].
  move: to => [_ to];case: (to _ _ zE zE').
    by move => aux; exists z, z';split => //; split => //; apply:nesym.
  rewrite /glt; move => aux; exists z', z;split => //.
have ltuv: glt r' u w by order_tac.
move: (sfa i u w uF wF) (sfb i u w uF wF ltuv).
set g:= Lf _ _ _; move=> ta fg.
move: tor => [_]; rewrite (proj2 (imo_osr r or')) => aux.
have p1: Vf f i = v by rewrite /f constant_V.
have p2: Vf f s = v by rewrite /f constant_V.
have p3: Vf g i = u by rewrite /g /sf LfV// Y_true//; order_tac.
have p4: Vf g s = w by rewrite /g /sf LfV // Y_false// => h; order_tac.
case: (aux _ _ fs fg) => h; move: (imo_incr or' h iF)  (imo_incr or' h sF);
  rewrite p1 p2 p3 p4 => p5 p6; order_tac.
Qed. 

End Exercise1_6.

(** ---- Exercise 1.7. 
A function that is both increasing and decreasing is constant iff 
the source is connected for [ocomparable]; this is the case: if the source 
is directed   *)

Definition cr_equiv r :=
  chain_equivalence (ocomparable r) (substrate r).
Definition cr_component r :=
  connected_comp (ocomparable r) (substrate r).

Lemma cr_properties r: order r ->
  [/\ equivalence (cr_equiv r) ,
    (forall x y, ocomparable r x y ->
       (inc x (substrate r)/\ inc y (substrate r))),
    substrate  (cr_equiv r) =  substrate r,
    (forall x, inc x (substrate r) -> class (cr_equiv r) x = cr_component r x) &
    (forall x y, ocomparable r x y -> related (cr_equiv r) x y)].
Proof.
move=> or.
rewrite /cr_equiv /cr_component.
have crs: (forall x y,  ocomparable r x y -> 
 (inc x (substrate r) /\ inc y (substrate r))). 
  by  move=> x y; case; split;  order_tac. 
have rc: (reflexive_re (ocomparable r) (substrate r)).
  by move => x; split ; [ move=> xsr;left  | case=> aux]; order_tac.
have sc: (symmetric_r (ocomparable r)) 
  by move=> x y; case; [right | left].
have crs': (forall x y, ocomparable r x y ->  inc x (substrate r)). 
  by move=> x y xy; move: (crs _ _ xy) => [ok _].
move:(chain_equivalence_eq rc sc crs') => [ha hb].
split => //. 
- by move=> x xsr; apply: connected_comp_class.
- move => x y cr;apply /Zo_P; split.
    by move: (crs _ _ cr) => [xs ys]; apply: setXp_i.
  by aw; exists (chain_pair x y).
Qed.

Lemma Exercise1_7a r x: right_directed r ->
  inc x (substrate r) -> cr_component r x = substrate r.
Proof. 
move /right_directedP => [or rdp]. 
move: (cr_properties or)=> [p1 p2 p3 p4 p5] xsr.
rewrite -(p4 _ xsr);apply: extensionality. 
  rewrite -p3;apply: sub_class_substrate => //. 
move=> t tsr; move: (rdp _ _ xsr tsr) => [z [xz yz]]. 
have r1: (related (cr_equiv r) x z) by apply: p5; left.
have r2: (related (cr_equiv r) t z) by apply: p5; left.
apply /(class_P p1).
apply: (@transitivity_e _ z) => //; apply: symmetricity_e => //.
Qed.

Lemma Exercise1_7b r x: left_directed r ->
  inc x (substrate r) -> cr_component r x = substrate r.
Proof. 
move /left_directedP => [or rdp]. 
move: (cr_properties or)=> [p1 p2 p3 p4 p5] xsr.
rewrite -(p4 _ xsr);apply: extensionality. 
  rewrite -p3;apply: sub_class_substrate => //. 
move=> t tsr; move: (rdp _ _ xsr tsr) => [z [xz yz]]. 
have r1: (related (cr_equiv r) x z) by apply: p5; right.
have r2: (related (cr_equiv r) t z) by apply: p5; right.
apply /(class_P p1); apply: (@transitivity_e _  z) => //. 
by apply: symmetricity_e.
Qed.


Lemma Exercise1_7c r r' f: increasing_fun f r r' ->
  decreasing_fun f r r' -> 
  forall x y, ocomparable r x y -> Vf f x = Vf f y.
Proof.
move=> [or or' [ff sr sr'] incf][_ _ _ decf] x y.
case=> h; move: (decf _ _ h)(incf _ _ h)=> p1 p2; order_tac.
Qed.

Lemma Exercise1_7d r r' f: increasing_fun f r r' ->
  decreasing_fun f r r' -> 
  (exists2 x, inc x (substrate r) & cr_component r x = substrate r) ->
  (constantfp f).
Proof. 
move=> incf decf [x xsr sr1]; set H := (Exercise1_7c incf decf).
move: (incf) => [or or' [ff sr sr'] incf'].
move: (cr_properties or)=> [p1 p2 p3 p4 p5].
split => //.
suff sw': (forall u, inc u (source f) -> Vf f u = Vf f x).
  by move => a b asf bsf; move: (sw' _ asf)  (sw' _ bsf) => -> ->.
move => u; rewrite sr - sr1 -(p4 _ xsr) => /(class_P p1) rxu.
have: related (cr_equiv r) u x by apply: symmetricity_e. 
move /Zo_P => [_]; aw; move => [c [h1 <- <-]].
elim: c h1;first by move => a b; apply: H.
by move=> a c => xx [yy zz]; rewrite -(xx  zz); apply:H.
Qed.

Lemma Exercise1_7e r r': order r -> order r' ->
  (exists u v, [/\ inc u (substrate r'), inc v (substrate r')  & u <>v]) ->
  (exists2 x, inc x (substrate r) & cr_component r x <> substrate r) ->
  exists f, [/\ increasing_fun f r r',  decreasing_fun f r r' &
    ~(constantfp f)].
Proof. 
move=> or or' [u [v [usr' vsr' uv]]] [x xsr nsr].
move: (cr_properties or)=> [p1 p2 p3 p4 p5].
pose f t :=  Yo (inc t (cr_component r x)) u v.
have ta: (lf_axiom f (substrate r) (substrate r')). 
  by move=> t tsr; rewrite /f; Ytac tc. 
set (g:= Lf f  (substrate r) (substrate r')). 
have fg: (function g) by apply: lf_function.
have sg: source g = substrate r by rewrite /g; aw.
have tg: target g = substrate r' by rewrite /g; aw.
have q1:(sub (cr_component r x) (substrate r)).
  by rewrite -(p4 _ xsr) -p3; apply: sub_class_substrate.
have q2: forall y, inc y (cr_component r x) -> Vf g y = u.
  by move=> y yc; rewrite /g LfV // /f; [ Ytac0 | apply: q1].
have q3 y: inc y (substrate r) -> ~(inc y (cr_component r x)) -> Vf g y = v.
  by move=> yc ync; rewrite /g LfV // /f Y_false //.
have ncg: (~ constantfp g).
  move=> [h1 h2]; case: nsr; apply: extensionality => //.
  move=> t tsr; ex_middle bad; rewrite sg in h2.
  have xc: inc x (cr_component r x).
    rewrite -(p4 _ xsr); apply /(class_P p1); apply: reflexivity_e =>//; ue.
  case: uv;move: (h2 _ _ xsr tsr);rewrite (q2 _ xc)(q3 _ tsr bad) //. 
have q4: (forall a b,
    gle r a b -> ((inc a (cr_component r x) <-> inc b (cr_component r x)))).
  move=> a b ab; rewrite - (p4 _ xsr). 
  have cab: (ocomparable r a b) by left.
  move: (p5 _ _ cab)=> rab.
  split; move => /(class_P p1) => h; apply  /(class_P p1).
     by apply: (@transitivity_e _  a). 
  by apply: (@transitivity_e _  b) =>//; apply: symmetricity_e. 
have q5: (forall a b, gle r a b ->  Vf g a = Vf g b). 
  move=> a b ab.
  case: (p_or_not_p (inc a (cr_component r x))) => H.
    by rewrite (q2 _ H); move: H;move/ (q4 _ _ ab) => H; rewrite (q2 _ H).
  have asr: inc a (substrate r) by order_tac.
  have bsr: inc b (substrate r) by order_tac.
  by rewrite (q3 _ asr H); move:H => /(q4 _ _ ab) H;rewrite (q3 _ bsr H).
exists g;split => //; split => //; move=> a b ab;rewrite (q5 _ _ ab); order_tac.
  rewrite -tg; apply: Vf_target => //; rewrite sg; order_tac.
rewrite -tg; apply: Vf_target => //; rewrite sg; order_tac.
Qed.

(** ---- Exercise 1.8: fixed point of [f o g] and [g o f] are isomorphic
*)

Lemma Exercise1_8 r r' f g:
  let A := Zo (substrate r) (fun z => Vf g (Vf f z) = z) in
    let B := Zo (substrate r') (fun z => Vf f (Vf g z) = z) in
      increasing_fun f r r' ->  increasing_fun g r' r ->
      (induced_order r A) \Is (induced_order r' B).
Proof. 
move=>  A B [o1 o2 [ff sf tf] incf][_ _ [fg sg tg] incg].
have p1: (forall x, inc x A -> inc (Vf f x) B). 
  by move=> x /Zo_P [xsr r1]; apply: Zo_i; [Wtac | rewrite r1].
have p2: (forall x, inc x B -> inc (Vf g x) A). 
  by move=> x /Zo_P [xsr r1]; apply: Zo_i ; [Wtac | rewrite r1].
have Ha: source (restriction2 f A B) = A by rewrite / restriction2; aw. 
have Hb: target (restriction2 f A B) = B by rewrite / restriction2; aw. 
have asf: sub A (source f) by rewrite sf; apply: Zo_S.
set (h:=restriction2 f A B).
have ra: (restriction2_axioms f A B).
  split => //.
    rewrite /B -tf; apply: Zo_S.
  by move => t /(Vf_image_P ff asf) [s sa ->]; apply: p1.
have fh: function h by apply: (proj31 (restriction2_prop ra)).
have ih: (injection h). 
  split=> //; rewrite Ha; move => x y xA yA /=.
  rewrite /h restriction2_V // restriction2_V // => eq.
  move: xA yA => / Zo_hi <- /Zo_hi <-; ue.
have sh: (surjection h). 
  split => //; rewrite Ha Hb; move=> y yB. 
  move: (p2 _ yB) => wA.
  ex_tac; move: yB => /Zo_P [ysr ww]; rewrite /h  restriction2_V //.
have As: (sub A (substrate r)) by apply: Zo_S.
have Bs: (sub B (substrate r')) by apply: Zo_S.   
have Ash: A = source h by rewrite /h; aw.
have Bsh: B = target h by rewrite /h; aw.
move: (iorder_osr o1 As) => [pa pb].
move: (iorder_osr o2 Bs) => [pc pd].
exists h; split => //; first by rewrite pb pd; split.
red;rewrite -Ash; move=> x y xA yA.
rewrite /h restriction2_V // restriction2_V //; aw; try apply: p1 => //.
split.
   move =>aux; apply /iorder_gle0P; try  apply: p1 => //. 
   apply: (incf _ _  (iorder_gle1 aux)).
move =>aux; apply /iorder_gle0P => //.
move: (incg _ _ (iorder_gle1 aux)). 
by move: xA yA => /Zo_hi -> /Zo_hi ->.    
Qed.


(** ---- Exercise 1.9 [sup (inf xij) <= inf (sup xij)] *)

Section Exercise1_9.
Variable r: Set.
Hypothesis lr: lattice r.
Let Hf := fun f => [/\ fgraph f, finite_set (domain f), nonempty (domain f) & 
  sub (range f) (substrate r) ].

Lemma lattice_finite_sup_aux f: Hf f ->
  nonempty (range f) /\ finite_set (range f).
Proof.
move=> [fgf fsd ned srf]; split; last by apply: finite_range.
by move: ned => [x xd]; exists (Vg f x); fprops.
Qed.

Lemma lattice_finite_sup4P f: (Hf f) -> forall y, 
  (gle r(sup_graph r f) y <-> (forall z, inc z (domain f) -> gle r (Vg f z) y)).
Proof. 
move => hf y.
move:(lattice_finite_sup_aux hf) => [ne fr].
move: hf=> [fgf fsd ned srf];split.
  move /(lattice_finite_sup3P lr _ fr ne srf) => h z sd; apply: h;  fprops.
move=> h; apply /(lattice_finite_sup3P lr _ fr ne srf).
by move=>  z; move /(range_gP fgf) => [x xdf] ->; apply: h.
Qed.

Lemma lattice_finite_inf4P f :(Hf f) -> forall y,
 (gle r y (inf_graph r f) <-> (forall z, inc z (domain f) -> gle r y (Vg f z))).
Proof.
move => hf y.
move:(lattice_finite_sup_aux hf) => [ne fr].
move: hf=> [fgf fsd ned srf];split.
  move /(lattice_finite_inf3P lr _ fr ne srf) => h z sd; apply: h;  fprops.
move=> h; apply /(lattice_finite_inf3P lr _ fr ne srf).
by move=>  z; move /(range_gP fgf) => [x xdf] ->; apply: h.
Qed.

Lemma lattice_finite_sup5 f:
  (Hf f) ->  inc (sup_graph r f) (substrate r).
Proof.
move: (proj1 lr) => or [fgf fsd ned srf].
have aux: (has_sup_graph r f).
  apply: lattice_finite_sup2 => //;first  by apply: finite_range.
  move: ned => [x xd]; exists (Vg f x); fprops. 
by move: (sup_graph_pr1 or srf aux) => /(lubP or srf) [[pa _] _]. 
Qed.

Lemma lattice_finite_inf5 f:
  (Hf f) -> inc (inf_graph r f) (substrate r).
Proof. 
move: (proj1 lr) => or [fgf fsd ned srf].
have aux: (has_inf_graph r f).
  apply: lattice_finite_inf2 => //; first by apply: finite_range.
  move: ned => [x xd]; exists (Vg f x); fprops. 
by move: (inf_graph_pr1 or srf aux) => /(glbP or srf) [[pa _] _]. 
Qed.

Lemma Exercise1_9 I1 I2 f:
  fgraph f -> domain f = I1 \times I2 ->
  finite_set I1 -> finite_set I2 -> nonempty I1 -> nonempty I2 ->
  sub (range f) (substrate r) ->
  gle r 
  (sup_graph r (Lg I2 (fun j => inf_graph r (Lg I1 (fun i => Vg f (J i j))))))
  (inf_graph r (Lg I1 (fun i => sup_graph r (Lg I2 (fun j => Vg f (J i j)))))).
Proof. 
move=> fgf df fs1 fs2 ni1 ni2 srf.
have or: order r by move: lr => [ok _].
have hb: forall i j, inc i I1 -> inc j I2 -> 
    inc (Vg f (J i j)) (substrate r). 
  move=> i j i1 j2;apply: srf; apply: inc_V_range => //; rewrite df;  fprops.
have Hu: forall b, inc b I2 -> Hf (Lg I1 (fun i  => Vg f (J i b))).
  by move => b bp; split; aww =>t' /Lg_range_P [b' bi1'] ->; apply: hb.
have Hv: forall b, inc b I1 -> Hf (Lg I2 (fun j  => Vg f (J b j))).
  by move => b bp; split;aww =>t' /Lg_range_P [b' bi1'] ->; apply: hb.
have Ha: Hf (Lg I2 (fun j => inf_graph r (Lg I1 (fun i=> Vg f (J i j))))).
  split => //; aww.
  move=>t /Lg_range_P[b bi2] ->; apply: lattice_finite_inf5 => //; aw; fprops.
have Hb: Hf (Lg I1 (fun i => sup_graph r (Lg I2 (fun j => Vg f (J i j))))).
  split => //; aww.
  move=>t/Lg_range_P [b bi2] ->; apply: lattice_finite_sup5 => //; aw; fprops.
apply /lattice_finite_sup4P => //.
aw; move => z zI; rewrite ! LgV//.
apply/(lattice_finite_inf4P Hb); aw => t tI. rewrite LgV//.
apply: (@order_transitivity _ _  (Vg f (J t z))) => //.
  set (fa:= (Lg I1 (fun i => Vg f (J i z)))).
  have Hfa: Hf fa. 
    by rewrite /fa; split;aww => y /Lg_range_P [x xI1] ->; aw; apply: hb.
  have: (gle r (inf_graph r fa) (inf_graph r fa)).
     by order_tac; apply: lattice_finite_inf5.
  have ->: (Vg f (J t z) = Vg fa t). by rewrite /fa; rewrite LgV//.
  by move/(lattice_finite_inf4P  Hfa); apply; rewrite /fa; aw.
set (fb:= Lg I2 (fun j => Vg f (J t j))).
have Hfa: Hf fb. 
  by rewrite /fb; split; aww => y /Lg_range_P [x xI1] ->; apply: hb.
have ->: (Vg f (J t z) = Vg fb z) by  rewrite /fb LgV//.
have: (gle r (sup_graph r fb) (sup_graph r fb)).
  by order_tac; apply: lattice_finite_sup5.
by move /(lattice_finite_sup4P Hfa); apply; rewrite /fb; aw.
Qed.

End Exercise1_9.

Lemma Exercise1_9_a r I1 I2 f
  (rf1 := fun j => Lg I1 (fun i => Vg f (J i j)))
  (rf2 := fun i => Lg I2 (fun j => Vg f (J i j)))
  (inf1 := (fun j => inf_graph r (rf1 j)))
  (sup1 := (fun i => sup_graph r (rf2 i))):
  fgraph f -> domain f = I1 \times I2 ->  sub (range f) (substrate r) ->
  order r ->
  (forall j, inc j I2 -> has_infimum r (range (rf1 j))) ->
  (forall i, inc i I1 -> has_supremum r (range (rf2 i))) ->
  has_supremum r (range (Lg I2 inf1)) ->
  has_infimum r (range (Lg I1 sup1)) ->
  gle r  (sup_graph r (Lg I2 inf1))   (inf_graph r (Lg I1 sup1)).
Proof. 
move => fgf df rf or hi1 hs1 hs2 hi2.
have ra j: inc j I2 ->sub (range (rf1 j)) (substrate r).
  move => jI2 t /Lg_range_P [i iI1 ->]; apply: rf; apply: (inc_V_range fgf).
  by rewrite df; apply: setXp_i.
have rb i: inc i I1 ->sub (range (rf2 i)) (substrate r).
  move => iI1 t /Lg_range_P [j jI2 ->]; apply: rf; apply: (inc_V_range fgf).
  by rewrite df; apply: setXp_i.
have rc j: inc j I2 -> lower_bound r (range (rf1 j)) (inf1 j).
  move => jI2; move: (ra j jI2) => qa.
  by move/(glbP or qa): (infimum_pr1 or (hi1 j jI2)); case.
have rd i: inc i I1 -> upper_bound r (range (rf2 i)) (sup1 i).
  move => iI1; move: (rb i iI1) => qa.
  by move/(lubP or qa): (supremum_pr1 or (hs1 i iI1)); case.
have re j: inc j I2 ->  inc (inf1 j) (substrate r) by move => /rc [].
have r1: sub (range (Lg I2 inf1)) (substrate r).
  by move => t /Lg_range_P [b bI2 ->];  apply: re.
have r2: sub (range (Lg I1 sup1)) (substrate r).
  by move => t /Lg_range_P [b /rd  /proj1 bI1 ->].
move / (lubP  or r1): (supremum_pr1 or hs2) =>[[qa _] qb].
move / (glbP  or r2): (infimum_pr1 or hi2) =>[[qc _] qd].
apply: qb; split; first exact.
move => t /Lg_range_P [j jI2 ->]; apply: qd; split; first by apply: re.
move => s /Lg_range_P [i iI1 ->].
set x := Vg f (J i j).
apply: (@order_transitivity _ _  (Vg f (J i j))) => //.
  apply: (proj2 (rc _ jI2)); apply/Lg_range_P; ex_tac.
apply: (proj2 (rd _ iI1)); apply/Lg_range_P; ex_tac.
Qed.


(** ---- Exercise 1.10: in a lattice [f] is increasing iff
[f(inf(x,y)) <= inf(f(x), f(y))].  We give an example where inequality is strict
 *)

Section Exercise1_10.
Variable r r': Set.
Hypothesis (lr: lattice r) (lr': lattice r').

Lemma Exercise1_10 f: function_prop f (substrate r)(substrate r') ->
  ((increasing_fun f r r') <->
  (forall x y, inc x (substrate r) -> inc y (substrate r) ->
    gle r' (Vf f (inf r x y)) (inf r' (Vf f x) (Vf f y)))).
Proof.
move => [ff sf tf]; split. 
  move=> [or or' _  incf] x y xsr ysr.
  move: (lattice_inf_pr lr xsr ysr) => [Ha Hb _ ]. 
  have p1: (inc (inf r x y) (source f)) by rewrite sf; order_tac.
  rewrite - sf in xsr ysr; move: (incf _ _ Ha) (incf _ _ Hb) => p2 p3.
  move: (Vf_target ff xsr)(Vf_target ff ysr); rewrite tf => w1 w2.
  by apply: (proj33 (lattice_inf_pr lr' w1 w2)). 
move: (lr)(lr') => [or _][or' _] p;split => //.
move=> x y xy.
have xsr: (inc x (source f)) by rewrite sf; order_tac.
have ysr: (inc y (source f)) by rewrite sf; order_tac.
rewrite - sf in p;move: (p _ _ xsr ysr); rewrite (inf_comparable1 or xy). 
move: (Vf_target ff xsr)(Vf_target ff ysr); rewrite tf => w1 w2.
move: (lattice_inf_pr lr' w1 w2) => [_ p1 _ ] p2; order_tac.
Qed.

Lemma Exercise1_10b f: function_prop f (substrate r)(substrate r') ->
  ((increasing_fun f r r') <->
  (forall x y, inc x (substrate r) -> inc y (substrate r) ->
    gle r' (sup r' (Vf f x) (Vf f y)) (Vf f (sup r x y)))).
Proof.
move => [ff sf tf]; split.
  move=> [or or' _ incf] x y xsr ysr.
  move: (lattice_sup_pr lr xsr ysr) => [Ha Hb _ ]. 
  have p1: (inc (sup r x y) (source f)) by rewrite sf; order_tac.
  rewrite - sf in xsr ysr; move: (incf _ _ Ha) (incf _ _ Hb) => p2 p3.
  move: (Vf_target ff xsr)(Vf_target ff ysr); rewrite tf => w1 w2.
  by apply: (proj33(lattice_sup_pr lr' w1 w2)). 
move: (lr)(lr') => [or _][or' _] p;split => //.
move=> x y xy.
move:(arg1_sr xy)(arg2_sr xy); rewrite - sf => xsr ysr.
rewrite - sf in p;move: (p _ _ xsr ysr); rewrite (sup_comparable1 or xy). 
move: (Vf_target ff xsr)(Vf_target ff ysr); rewrite tf => w1 w2.
move: (lattice_sup_pr lr' w1 w2) => [p1 _ _] p2; order_tac.
Qed.

Lemma product2_lattice: lattice (order_product2 r r').
Proof.
move: (lr)(lr') => [or _][or' _].
move: (order_product2_or or or') => or''.
split => //; rewrite  order_product2_sr //.
move=> x y xs ys; move: (xs)(ys)=> /setX_P [px Px Qx] /setX_P [py Py Qy].
move: (lattice_sup_pr lr Px Py) (lattice_inf_pr lr Px Py).
move: (lattice_sup_pr lr' Qx Qy) (lattice_inf_pr lr' Qx Qy).
set ap := (inf r (P x) (P y)); set bp := (sup r (P x) (P y)).
set aq := (inf r' (Q x) (Q y)); set bq := (sup r' (Q x) (Q y)).
move=> [p1 p2 p3][q1 q2 q3][r1 r2 r3][s1 s2 s3].
have b1: inc bp (substrate r) by order_tac.
have b2: inc ap (substrate r) by order_tac.
have b3: inc bq (substrate r') by order_tac.
have b4: inc aq (substrate r') by order_tac.
split.
  exists (J bp bq); apply: lub_set2 => //. 
     apply /order_product2_P; split => //; aww.
   apply /order_product2_P; split => //; aww.
  move=> t /order_product2_P [_ tp [h1 h2]]
   /order_product2_P [_ _ [h3 h4]]; apply /order_product2_P; split;aww.
exists (J ap aq); apply: glb_set2 => //.
     apply /order_product2_P;split=>//;aww.
   apply /order_product2_P; split => //;aww.
  move=> t /order_product2_P [tp  _ [h1 h2]]
   /order_product2_P [_ _ [h3 h4]]; apply /order_product2_P; split;aww.
Qed.


End Exercise1_10.

Definition Exercise1_10_counterexample r r' f:=
  [/\ lattice r, lattice r', function_prop f (substrate r)(substrate r'),
      (increasing_fun f r r') &
  exists x y, [/\ inc x (substrate r), inc y (substrate r) &
    (Vf f (inf r x y))  <> (inf r' (Vf f x) (Vf f y))]].

Lemma Exercise1_10_bis
  (r := order_product2 Nat_order Nat_order) 
  (r':= Nat_order)
  (f := Lf (fun z =>  (P z) +c (Q z)) (Nat \times  Nat) Nat):
   Exercise1_10_counterexample r r' f.
Proof.
move:Nat_order_wor=> [pa sr'].
have l1: lattice Nat_order by apply: total_order_lattice;apply: worder_total.
have l2: lattice r by apply: product2_lattice.
move: (l1)(l2) => [or1 _][or2 _].
have sr: substrate r = Nat \times Nat.
  by rewrite order_product2_sr// -/r' sr'.
rewrite /f - sr.
have ta: lf_axiom (fun z =>  (P z) +c (Q z)) (substrate r) Nat.
  by rewrite sr;move => z /setX_P [_ p1 p2]; apply: NS_sum.
have fp: function_prop (Lf (fun z => P z +c Q z) (substrate r) Nat)
     (substrate r) (substrate r') by split;aw => //;apply: lf_function.
split => //.  
   split => // x y. 
   move /order_product2_P; rewrite -/r' sr' - sr; move=> [xp yp [le1 le2]].
   rewrite LfV // LfV //.
   move: le1 le2 => /Nat_order_leP  [p1 p2 p3] /Nat_order_leP [p4 p5 p6].
   by apply /Nat_order_leP;split => //; fprops; apply: csum_Mlele.
set a :=  (J \1c \0c); set b:= (J \0c \1c).
move: NS0 NS1; rewrite /natp => ns0 ns1.
have asr: inc a (substrate r) by rewrite sr /a; fprops.
have bsr: inc b (substrate r) by rewrite sr /b; fprops.
move: (lattice_inf_pr l2 asr bsr).
set c:= inf r a b.
move => [] /order_product2_P [csr _ []] _ /Nat_order_leP [_ _ p1].
move => /order_product2_P [_ _ []] /Nat_order_leP [_ _ p2]  _ h.
have: c = J (P c) (Q c) by aw; move: csr  => /setX_P [].
move: p1 p2; rewrite /a /b; aw => p1 p2.
rewrite (cle0 p1) (cle0 p2) => cv.
rewrite sr' - sr in csr. 
exists a, b; split => //; rewrite  (LfV ta csr) cv.
rewrite (LfV ta asr) (LfV ta bsr)  !pr1_pair ! pr2_pair.
rewrite (csum0r CS0) (csum0r CS1) (csum0l CS1).
have osr: inc \1c (substrate r') by rewrite sr'; fprops.
by rewrite  inf_comparable1 //; [fprops | order_tac]. 
Qed.

Lemma  Exercise1_10_ter
  (r':= canonical_doubleton_order)
  (r := order_product2 r' r') 
  (f := Lf (fun z => (Yo (z = J C0 C0)) C0 C1) (C2 \times C2) C2):
   Exercise1_10_counterexample r r' f.
Proof.
move: cdo_wor => [cdo sr'].
have l1: lattice r' by apply: total_order_lattice;apply: worder_total.
have l2: lattice r by apply: product2_lattice.
move: (l1)(l2) => [or1 _][or2 _].
have ta: lf_axiom (fun z => (Yo (z = J C0 C0)) C0 C1) (C2 \times C2) C2.
  move => z _; simpl; Ytac ww; fprops.
have sr: substrate r = C2 \times C2.
  by rewrite order_product2_sr// -/r' sr'.
have ff: function f by apply: lf_function.
set c := J C0 C0.
set a := J C0 C1.
set b := J C1 C0.
have nac: a <> c by move => ac; move: (pr2_def ac); fprops.
have nbc: b <> c by move => ac; move: (pr1_def ac); fprops.
have asr: inc a (substrate r) by rewrite sr /a; fprops.
have bsr: inc b (substrate r) by rewrite sr /b; fprops.
have csr: inc c (substrate r) by rewrite sr /c; fprops.
have ic: (inf r a b) = c.
  move: (lattice_inf_pr l2 asr bsr) => [] /order_product2_P
     [itp _ [r1 r2]]  /order_product2_P [_ _ [r3 r4]] _.
  rewrite - (setX_pair itp).
  move: r1 => /cdo_gleP;case.
    move => [-> _]; move: r4 => /cdo_gleP; case; first by move => [-> _].
    by move => [_]; rewrite/b;aw => sv; case: C0_ne_C1.
    by move => [_]; rewrite/b;aw => sv; case: C0_ne_C1.
  by move => [_];rewrite/a; aw => sv; case: C0_ne_C1.
  by move => [_];rewrite/a; aw => sv; case: C0_ne_C1.
have fp: function_prop f (substrate r) (substrate r') by rewrite /f;split; aw.
saw; first split => //.
  move=> x y; move /order_product2_P; rewrite sr'. 
  rewrite /f;move=> [xp yp [le1 le2]]; rewrite !LfV//.
  apply /cdo_gleP => //;Ytac xm; Ytac ym; try in_TP4; case: xm.
  rewrite - (setX_pair xp); move: le1 => /cdo_gleP; case.
  + move => [-> _]; move: le2 => /cdo_gleP; case.
    - by move => [-> _].
    - by move =>[_]; rewrite ym; aw => sv; case: C0_ne_C1.
    - by move =>[_]; rewrite ym; aw => sv; case: C0_ne_C1.
  + by move =>[_]; rewrite ym; aw => sv; case: C0_ne_C1.
  + by move =>[_]; rewrite ym; aw => sv; case: C0_ne_C1.
exists a, b; split => //. 
rewrite sr in asr bsr  csr.
rewrite ic (LfV ta asr)  (LfV ta bsr)(LfV ta csr). 
rewrite -/c; Ytac0; Ytac0; Ytac0.
rewrite  inf_comparable1; [fprops | fprops | order_tac; rewrite sr'; fprops].
Qed.

(** ---- Exercise 1.11: complete lattice*)

(** a set is a  complete lattice if any set has a supremum; it then has an infimum *)

Definition complete_lattice r := order r /\
  forall X, sub X (substrate r) -> (has_supremum r X /\ has_infimum r X).

Lemma Exercise1_9_b I1 I2 r f:
  fgraph f -> domain f = I1 \times I2 ->
  sub (range f) (substrate r) ->
  complete_lattice r-> 
  gle r 
  (sup_graph r (Lg I2 (fun j => inf_graph r (Lg I1 (fun i => Vg f (J i j))))))
  (inf_graph r (Lg I1 (fun i => sup_graph r (Lg I2 (fun j => Vg f (J i j)))))).
Proof. 
move => ha hb hc [or hd].
have H i j:  inc i I1 -> inc j I2 ->  inc (Vg f (J i j)) (substrate r).
  move => qa qb; apply: hc; apply: (inc_V_range ha).
  by rewrite hb; apply: setXp_i.
have qa X:  sub X (substrate r) -> has_supremum r X by case /hd.
have qb X:  sub X (substrate r) -> has_infimum r X by case /hd.
pose R1 j :=  (range (Lg I1 (fun i => Vg f (J i j)))).
pose R2 i := (range (Lg I2 (fun j  => Vg f (J i j)))).
have R1a j: inc j I2 -> sub (R1 j) (substrate r).
  by move => jI2 t /Lg_range_P [i iI1 ->]; apply: H.
have R2a i: inc i I1 -> sub (R2 i) (substrate r).
  by move => iI2 t /Lg_range_P [j jI1 ->]; apply: H.
have ra j: inc j I2 -> has_infimum r ( R1 j).
  by move => ji2; apply: qb; apply: R1a. 
have rb i: inc i I1 -> has_supremum r (R2 i).
  by move => iI1; apply: qa; apply: R2a. 
apply: Exercise1_9_a => //.
- apply: qa =>y /Lg_range_P [j jI2 ->].
  by move/(glbP or (R1a _ jI2)):(infimum_pr1 or (ra j jI2)) => [[ok _] _].
- apply: qb =>y /Lg_range_P [i iI1 ->].
  by move/(lubP or (R2a _ iI1)):(supremum_pr1 or (rb i iI1)) => [[ok _] _].
Qed.


Lemma Exercise1_11a r: complete_lattice r ->
  (has_greatest r /\ has_least r).
Proof. 
move=> [or cl].
have es:(sub emptyset (substrate r)) by fprops.
move: (cl _ es) => [[x xse] [y yie]].
move: xse; rewrite (lub_set0 or) => xse.
move: yie; rewrite (glb_set0 or) => yie.
by split; [ exists y | exists x].
Qed.

Lemma Exercise1_11b r: order r ->  
  (forall X, sub X (substrate r) -> has_supremum r X) ->
  complete_lattice r.
Proof. 
move=> or h; split => //.
move=> X Xsr;split;fprops.
set (Z := (Zo (substrate r) (lower_bound r X))).
have zs: (sub Z (substrate r)) by apply: Zo_S. 
move: (h _  zs) => [x] /(lubP or zs) [[xz ux] leux].
exists x;apply /(glbP or Xsr); split.
  split; first exact.
  move=> y yX; apply: leux; split; first by apply: Xsr.
  by move=> t /Zo_P [_ [_]]; apply.
by move => z zl; apply: ux; apply: Zo_i => //;move: zl =>[ok _].
Qed.

Lemma Exercise1_11h r: order r ->  
  (forall X, sub X (substrate r) -> has_infimum r X) ->
  complete_lattice r.
Proof. 
move=> or h; split => //.
move=> X Xsr;split;fprops.
set (Z := (Zo (substrate r) (upper_bound r X))).
have zs: (sub Z (substrate r)) by apply: Zo_S. 
move: (h _  zs) => [x].
move /(glbP or zs)=> [[xz ux] leux].
exists x; apply /(lubP or Xsr);split.
  split; first exact.
  move=> y yX; apply: leux; split; first by apply: Xsr.
 by move=> t /Zo_hi  [_]; apply.
by move => z zl; apply: ux; apply: Zo_i=> //;move: zl =>[ok _].
Qed.

Lemma Exercise1_11i r:
  complete_lattice r -> complete_lattice (opp_order r).
Proof.
move => [p1 p2].
move: (opp_osr p1) => [q3 q4];split => //;rewrite q4.
move=> X Xs; move: (p2 _ Xs) => [[x p3] [y p4]]; split.
    by exists y; apply/inf_sup_oppP.
by exists x; apply/sup_inf_oppP.
Qed.

Lemma Exercise1_11j r:
  total_order r -> finite_set (substrate r) -> ne_substrate r ->
  complete_lattice r.
Proof.
move => tor fsr nes.
move: (tor) => [or _];apply: Exercise1_11b => // X Xsr.
case: (emptyset_dichot X) => xE.
  move: (finite_set_torder_least tor fsr nes) => [x [xsr xl]].
   exists x; apply /lubP => //; split. 
      by split =>//; rewrite xE => y /in_set0.
   by move => z [ze _]; apply: xl.
move: (sub_finite_set Xsr fsr) => fsx.
move: (finite_subset_torder_greatest tor fsx xE Xsr) => [x []].
rewrite (iorder_sr or Xsr) => xsr xg; exists x; apply /lubP => //; split.
  split => //; [ by apply: Xsr | move => y yX ; exact: (iorder_gle1 (xg _ yX))].
by move => z [sr]; apply.
Qed.

(** When is a product a complete lattice  *)

Lemma Exercise1_11c g: order_fam g ->
  (allf g complete_lattice) ->
  complete_lattice (order_product g).
Proof. 
move=> alo ala.
move: (order_product_osr alo) => [og Ha].
apply: Exercise1_11b => // X Xsr.
set f := Lg (domain g) (fun i => substrate (Vg g i)).
have fgf: fgraph f by rewrite /f; fprops.
have fpri: forall i, inc i (domain g) -> function (pr_i f i).
  move=> i idg;apply: pri_f; rewrite /f; aww.
have pf: productb f = substrate (order_product g) by rewrite Ha.
pose Xi i :=  (Vfs (pr_i f i) X).
have p1: forall i, inc i (domain g) -> sub (Xi i) (substrate (Vg g i)).
  move => i idg; rewrite /Xi.
  have <-: (target (pr_i f i) = substrate (Vg g i)).
     by rewrite /pr_i/f; aw; rewrite LgV//.
  apply: fun_image_Starget1; apply: (fpri _ idg).
set v:= Lg (domain g) (fun i => supremum (Vg g i) (Xi i)).
have v1: forall i, inc i (domain g) -> least_upper_bound (Vg g i)(Xi i)(Vg v i).
  move=> i idg; rewrite /v LgV//;  move: (ala _ idg) => [_ ila].
  by move: (ila _ (p1 _ idg)) => [hs _]; apply: supremum_pr1=> //; apply: alo.
have vs: (inc v (substrate (order_product g))). 
  rewrite Ha; apply /prod_of_substratesP;rewrite /v; split;aww.
  move=> i idg; rewrite LgV//.
  move: (v1 _ idg) => /(lubP  (alo _ idg)(p1 _ idg)).
  rewrite /v LgV//; move => [[ok _] _] //.
exists v; apply /(lubP og Xsr); split.
  split => // y yX; apply /order_product_gleP; rewrite -Ha;split => //.
    by apply: Xsr.
  move=> i idg; move: (v1 _ idg) => /(lubP (alo _ idg)(p1 _ idg)).
  move=> [[p3 p2] _]; apply: p2.
  have yp: inc y (productb f) by rewrite pf; apply: Xsr.
  have idf: inc i (domain f) by rewrite /f; aw.
  apply /(Vf_image_P) => //; first by apply: pri_f.
    by rewrite /pr_i; rewrite lf_source pf.
  rewrite - (pri_V idf yp); ex_tac; apply: W_pr3. 
move => z [zs zu]; apply /order_product_gleP => //; rewrite -Ha;split => //.
move=> i idg; move: (v1 _ idg).
move/ (lubP (alo _ idg)(p1 _ idg));move=> [p2]; apply.
split.
  move: zs; rewrite -pf => /prod_of_substratesP [q1 q2 q3].
 by  move: (q3 _ idg);aw. 
have sX: sub X (source (pr_i f i)) by rewrite /pr_i; aw;ue.
move: (fpri _ idg) => fi.
move=> y /(Vf_image_P fi sX) [u uX ->].
have up: inc u (productb f) by rewrite pf; apply: Xsr.
have idf: inc i (domain f) by rewrite /f; aw.
rewrite (pri_V idf up). 
by move: (zu _ uX) => /order_product_gleP [_ _]; apply.  
Qed.

Lemma Exercise1_11d g: order_fam g ->
  complete_lattice (order_product g) ->
  (allf g complete_lattice).
Proof. 
move=> poa clp i idg; move: (clp) => [p3 p4]. 
move: (order_product_osr poa) => [og Ha].
move: (Exercise1_11a clp)=> [[a [asg _]] _].
move: (asg); rewrite Ha => /prod_of_substratesP [fgfa da vas].
move: (poa _ idg) => o1.
apply: Exercise1_11b => // X Xsr.
set (Y:= Lg (domain g) (fun j=> Yo (j = i) X (singleton (Vg a j)))).
have sYs: (sub (productb Y) (substrate (order_product g))). 
  rewrite Ha /Y; apply: setXb_monotone1 => //; aww.
  move=> j jdg; rewrite ! LgV//; Ytac ji; first ue.
  by move => t; move /set1_P ->; apply: vas.
move: (p4 _ sYs)=> [[y ys] _]; move: ys => /(lubP p3 sYs) [[ys uby] luy].
set f := Lg (domain g) (fun i => substrate (Vg g i)).
have df: domain f = domain g by rewrite /f; aw.
have fgf: fgraph f by rewrite /f; fprops.
have pf: productb f = substrate (order_product g) by rewrite Ha.
exists (Vg y i); apply /lubP => //; split. 
  split. 
    move: ys; rewrite Ha => /prod_of_substratesP [_ q1 q2].
    by move: (q2 _ idg); aw.
  move=> z zX.
  have fs: (inc (Lg (domain g)(fun j=> (Yo (j = i) z (Vg a j)))) (productb Y)).
    apply /setXb_P; rewrite /Y;split;aww.
    move=> j jdg; rewrite !LgV//; Ytac ji; Ytac0 => //; fprops.
  move: (uby _ fs)=> /order_product_gleP [_ _ h].  
  by move: (h _ idg); rewrite LgV//; Ytac0.
move=> z [zs zu].
set w:=  (Lg (domain g)(fun j=> (Yo (j = i) z (Vg a j)))).
have wp: (inc w (productb f)).
  apply /setXb_P; rewrite /w /f; split;aww.
  by move=> j jdg; rewrite !LgV//; Ytac ji; [ ue | apply: vas].  
have ubw: (upper_bound (order_product g) (productb Y) w). 
  split; first by ue.
  move=> t tp; apply /order_product_gleP; split => //; try ue. 
  have pa: fgraph Y by rewrite /Y; fprops.
  move=> j jdg; rewrite /w LgV//.
  move: tp=> /setXb_P; rewrite /Y; aw; move=> [_ p5 p6]. 
  move: (p6 _ jdg); rewrite LgV//.
  Ytac ji; Ytac0; first by rewrite ji;apply: zu. 
  by move /set1_P ->; move: (poa _ jdg) => oj; order_tac; apply: vas.
move: (luy _ ubw) => /order_product_gleP [_ _ h]. 
move: (h _ idg); rewrite /w LgV//; rewrite Y_true //.
Qed.

(** When is an ordinal sum a complete lattice ? *)

Lemma Exercise1_11e r g: 
  orsum_ax r g -> orsum_ax2 g ->
  (complete_lattice (order_sum r g) <->
  [/\ complete_lattice r,
    (forall j, sub j (substrate r) ->
      ~ (exists u, greatest_induced r j u) -> 
      has_least (Vg g (supremum r j))),
    (forall i x, inc i (substrate r) -> sub  x (substrate (Vg g i)) ->
      (exists u, upper_bound (Vg g i) x u) ->  nonempty x ->
      (exists u, least_upper_bound  (Vg g i) x u)) &
    (forall i, inc i (substrate r) ->  
      ~ (has_greatest (Vg g i)) -> 
      exists v, least_induced r (Zo (substrate r) (fun j =>
        glt r i j)) v /\ has_least (Vg g v))]).
Proof. 
move=> oa alne; move: (oa) => [or sr alo].
set (E:= substrate r). 
set F:= sum_of_substrates g.
have ss: substrate (order_sum r g) = F by rewrite orsum_sr.
have org: order (order_sum r g) by fprops.
split => bigh.
  pose k i := rep (substrate (Vg g i)). 
  have kp1: forall i, inc i E -> inc (k i)  (substrate (Vg g i)).
    rewrite /E sr; move=> i idg; apply: (rep_i (alne _ idg)).
  have kp2: forall i, inc i E -> inc (J (k i) i) F. 
     move=> i idg; move: (kp1 _  idg) => ps.
    rewrite /F/sum_of_substrates; apply: disjoint_union_pi1 =>//; ue.
  have p1: (forall j, sub j E -> exists x, 
    [/\ least_upper_bound (order_sum r g) (fun_image j (fun i => J (k i) i)) x,
      inc x F & least_upper_bound r j (Q x) ]).
    move=> j jE; set (Y:= fun_image j (fun i=> J (k i) i)).
    have sYF: (sub Y F).
       move=> t /funI_P [z zj ->]; apply: (kp2 _ (jE _ zj)).  
    move: bigh => [og cl]; rewrite ss in cl; move: (cl _ sYF) => [[x xs] _ ].
    have YS: sub Y (substrate (order_sum r g)) by rewrite ss.
    move:(xs) => /(lubP og YS) [[xs' ux] lux].
    have xF: (inc x F) by ue.    
    exists x; split => //;  apply /(lubP or jE); split; first split.
    + by case: (du_index_pr1 xF); rewrite sr.
    + move=> y yj.
      have pY: (inc (J (k y) y) Y) by apply /funI_P; exists y. 
      by move: (orsum_gle_id oa  (ux _ pY)); aw.
    + move=> z [zs ubz].
      move: (kp2 _ zs)  (kp1 _ zs) => zF aux.
      suff up1 : (upper_bound (order_sum r g) Y (J (k z) z)).
        by move:  (orsum_gle_id oa (lux  _ up1)); aw.
      split; [by ue | move=> y yY; apply  /orsum_gleP;split => // ].
         move : YS yY; rewrite (orsum_sr oa);apply.
      move: yY => /funI_P  [t tJ ->]; red; aw; case: (equal_or_not t z).
        by rewrite sr in zs;move:(alo _ zs)=> ot ->;right;split=> //; order_tac.
      by move => tz; left; split => //; apply: ubz.
  split.
  - apply: Exercise1_11b => //. 
    by move=> X Xsr; move:(p1 _ Xsr) => [x [_ _ xs]]; exists (Q x). 
  - move=> X Xsr ngX; move:(p1 _ Xsr) => [x [lubx xF xs]].
    have sX: (least_upper_bound r X ((supremum r X))).
      by apply: supremum_pr1 => //; exists (Q x).
    rewrite (supremum_unique or sX xs).
    move: xs => /(lubP or Xsr) [[qxs qxl] qxlu].
    have nQX:  (~ inc (Q x) X).
      dneg Qx; exists (Q x); hnf; rewrite iorder_sr//; split => //.
      by move => t tx; apply /iorder_gle0P=> //; apply: qxl.
    exists (P x); split; first by move: (du_index_pr1 xF) => [_].
    move=> t ts.  
    have pF: (inc (J t (Q x)) F) by apply: disjoint_union_pi1 => //; ue.
    set T:= (fun_image X (fun i  => J (k i) i)).
    have sT: sub T (substrate (order_sum r g)).
      by rewrite ss;move=> y /funI_P [z zx ->];apply: kp2; apply: Xsr.
    have u1: (upper_bound (order_sum r g) T (J t (Q x))).
      rewrite /T;split; first (by ue);move=> y /funI_P [z zX ->].
      apply /orsum_gleP;split;fprops;left; aw; split; first by apply: qxl.
      dneg zq; ue.
    move: lubx => /(lubP org sT) [_ aux]; move: (aux _ u1).
    by move => /orsum_gleP  [_ _]; case; [ move=> [_] |]; aw; case.
  - move=> i X iE sX [u [us ub]] [t tX]. 
    have idg: (inc i (domain g)) by ue. 
    set (Xi := X *s1 i). 
    have XiF: sub Xi F.
      move=> v /indexed_P [pv Pq Qv].
      by rewrite -pv Qv; apply: disjoint_union_pi1 =>//; apply: sX.
    have Xs1: sub Xi (substrate (order_sum r g)) by ue.
    move: bigh => [og cl]; rewrite ss in cl; move: (cl _ XiF) => [[x xs] _ ].
    move: xs => /(lubP org Xs1) [[xs xu] xleb].
    move: (xs); rewrite ss => xs1; move: (du_index_pr1 xs1) =>[Qx Px px].
    have si: forall x, inc x X -> inc (J x i) Xi by move=> w; apply:indexed_pi.
    have Qxi: Q x = i.
      have pF: (inc  (J u i) F) by apply: disjoint_union_pi1 =>//.
      have pub: (upper_bound (order_sum r g) Xi (J u i)).
        split;[ ue |move => y yXi ; apply /orsum_gleP; split;fprops; right].
        by move: yXi=> /indexed_P [py Py Qy];rewrite Qy; aw;split=> //;apply ub.
      move: (orsum_gle_id oa (xleb _ pub)).
      move: (orsum_gle_id oa (xu _ (si _ tX))); aw => le1 le2; order_tac.
    exists (P x); apply /(lubP (alo _ idg) sX); split.
      split;[ ue | move=> y yX; move: (xu _ (si _ yX)) =>/orsum_gleP [_ _]].
      by rewrite /order_sum_r Qxi;aw;case; [move=> [_] |]; case.
    move => z [zs zu].
    have pF: (inc (J z i) F) by apply: disjoint_union_pi1. 
    have sz1: (upper_bound (order_sum r g) Xi (J z i)).
      split; [ ue | move=> y yXi; apply /orsum_gleP; split;fprops; right ].
      move: yXi => /indexed_P; aw;move => [pa pb pc];split => //;
      by rewrite pc; apply:zu.
    by move: (xleb _ sz1) => /orsum_gleP [_ _] [] []; rewrite Qxi;aw.
  - move=> i iE nege.
    set (X:= (substrate (Vg g i)) *s1 i). 
    have XF: (sub X F).
      move=> v /indexed_P [pv Pq Qv].
      rewrite - pv Qv; apply: disjoint_union_pi1 =>//; ue. 
    move: bigh => [og cl]; rewrite ss in cl; move: (cl _ XF) => [[x xs] _ ].
    have paa: sub X (substrate (order_sum r g)) by ue.
    move: xs => /(lubP org paa) [[xs xu] xleb].
    move: (xs); rewrite ss => xs1; move: (du_index_pr1 xs1) =>[Qx Px px].
    set (Ii:=Zo E (fun j  => glt r i j)). 
    have QxI:  (inc (Q x) Ii).
      apply /Zo_P; split; [by rewrite /E;ue | split ].
        have k1: inc (J (k i) i) X by apply : indexed_pi; fprops.
        move: (orsum_gle_id oa (xu _ k1)); aw; trivial.
        dneg iqx; exists (P x); split; first by ue.
      move=> y yv.
      have pX: (inc (J y i) X) by  apply :indexed_pi; fprops.
      by move: (xu _ pX) => /orsum_gleP [_ _] [][]; aw; rewrite -iqx.
    have qx1: glt r i (Q x) by move: QxI => /Zo_P[].
    have IE:sub Ii E by apply: Zo_S.
    exists (Q x); split.  
      rewrite  /least_induced/ least iorder_sr //; split => //; move=> v vI1; aw.
      have: (upper_bound (order_sum r g) X  (J (k v) v)).
        split; first by rewrite ss; apply: kp2; apply: IE.
        move=> y yX; apply /orsum_gleP => // ;split;fprops; left; aw.
        by move: yX vI1 => /indexed_P [_ _ ->] /Zo_P [].
      move=> aux; move: (orsum_gle_id oa (xleb _ aux)); aw => h.
      by apply /iorder_gleP.
    exists (P x); split; [ exact |  move => y ys ].
    have p2: (inc (J y (Q x)) F) by apply: disjoint_union_pi1 =>//. 
    have p3: (upper_bound (order_sum r g) X  (J y (Q x))).
      split; first (by ue); move=> z zX; apply/orsum_gleP;split;fprops;left; aw.
      by move: zX => /indexed_P [_ _ ->]. 
    by move: (xleb _ p3) =>/orsum_gleP [_ _] [][];aw.
move: bigh => [hI hII hIII hIV]. 
apply: Exercise1_11b => //.
rewrite ss; move=> X Xsr.
set (j:= Zo E (fun i=> exists2 x, inc x X & i = Q x)).
have jE:  (sub j E) by apply: Zo_S. 
move: hI =>[_ h]; move: (h _ jE) => [ok _]; move: (supremum_pr1 or ok). 
have Xs: sub X (substrate (order_sum r g)) by ue.
case: (p_or_not_p (exists u, greatest_induced r j u)); last first.
  move=> neu; move: (hII _ jE neu).
  set s:= (supremum r j); move=> [v [vs lv]]; move/(lubP or jE)=> [[sE su] slu].
  have nsj: (~ inc s j).
    dneg sj;exists s; hnf; rewrite iorder_sr //; split => //.
    move=> x xj; apply/iorder_gle0P => //.
    by apply: su.
  set (b := J v s). 
  have bf: inc b F by apply: disjoint_union_pi1 => //; ue.
  exists b; apply /(lubP org Xs); split.
    split; [ ue | move=> t tX ; apply /orsum_gleP; split;fprops;left ].
    move: (du_index_pr1 (Xsr _ tX)) => [Qtd _ _].
    have Qtj: inc (Q t) j by apply: Zo_i; [ rewrite /E;ue | ex_tac ].
    move: (su _ Qtj) => aux; rewrite /b; aw; split => //; dneg qts; ue.
  move=> z [zs zu].
  move: (zs); rewrite ss /F => h'; move: (du_index_pr1 h') => [h1 h2 h3].  
  have ub: (upper_bound r j (Q z)).
    split; [ue | move=> y /Zo_P [yE [z' xX ->]]].
    apply: (orsum_gle_id  oa (zu _ xX)).
  apply /orsum_gleP; split => //; case:(equal_or_not (Q b) (Q z)) => qb.
    right; split => //. 
    by rewrite /b; aw; apply: lv; move: h2;rewrite -qb /b; aw.
  by left; split => //; rewrite /b; aw;  apply: slu. 
move => [k]; rewrite /greatest_induced /greatest iorder_sr //; move=> [kj kp].
have kp1: forall x, inc x X -> gle r (Q x) k.
  move=> x xX.
  suff  h1: inc (Q x) j by move: (iorder_gle1 (kp _ h1)).
  apply: Zo_i; last by ex_tac.
  by move: (du_index_pr1 (Xsr _ xX)); rewrite -/E - sr; case.
have Hd:forall z, upper_bound (order_sum r g) X z -> gle r k (Q z).
  move: kj =>  /Zo_P [kE [w wX ->]]. 
  rewrite /upper_bound ss; move => z [zs zu].
  by move: (orsum_gle_id oa  (zu _ wX)).
set (Xj:= Zo (substrate (Vg g k))
    (fun  y=> exists x, [/\ inc x X, y = P x & k = Q x])).
have neXj: nonempty Xj. 
  move: kj => /Zo_P [kE [w wX kw]].
  exists (P w); apply /Zo_P; move: (du_index_pr1 (Xsr _ wX))=> [_ Pw _].
  split; [ue | ex_tac].
case: (p_or_not_p (exists u, upper_bound (Vg g k) Xj u)) => uxi.
  have Xjp: (sub Xj (substrate (Vg g k))) by apply: Zo_S.
  have og: order (Vg g k) by apply: alo; ue.
  move: (hIII _ _  (jE _ kj) Xjp uxi neXj) => [u] /(lubP og Xjp) [[us uu] ule].
  have  pF:(inc (J u k) F) by apply: disjoint_union_pi1 =>//; ue. 
  exists (J u k); apply /(lubP org Xs); split.  
    split; first (by ue); move=> y yX; apply /orsum_gleP; split;fprops.
    move: (kp1 _ yX) => le1.
    red; aw; case: (equal_or_not (Q y) k) => qyk; last by left; split.
    right; rewrite qyk; split => //; apply: uu; apply: Zo_i; last by ex_tac. 
    by move: (du_index_pr1  (Xsr _ yX)) => [Qy Py py];rewrite -qyk.
  move => z zu; move: (Hd _ zu); move: zu =>[zs uz] lkq. 
  apply /orsum_gleP; split => //; first by rewrite -/F - ss. 
  move: (zs); rewrite ss /F => h'; move: (du_index_pr1 h') => [h1 h2 h3].  
  case: (equal_or_not k (Q z)) => kqz; last by left;aw; split.
  right; aw;rewrite -kqz;split =>//; apply: ule; split; first by ue.
  move=> y /Zo_P [ys [x [xX yP kQ]]].
  rewrite yP; move: (uz _ xX) => /orsum_gleP [_ _].
  by rewrite /order_sum_r -kQ - kqz /glt; case; case.
case: (p_or_not_p (exists u, greatest (Vg g k) u)). 
  move=> [u [us ug]]; case: uxi; exists u; split => //.
  by move => y /Zo_P [ys [x [xX yP kQ]]]; apply: ug.
move => ng; move: (hIV  _   (jE _ kj) ng) => [v [lv [x [xs xl]]]].
move: lv; set K:= Zo E _.
have Kr: sub K (substrate r) by rewrite /K; apply: Zo_S.
rewrite /least_induced /least iorder_sr //; move => [] /Zo_P [vE kv] vg.
have pF: (inc (J x v) F) by apply: disjoint_union_pi1 => //; ue.
exists (J x v); apply /(lubP org Xs); split.
  split;[ ue | move=> y yX; apply /orsum_gleP; split;fprops; left ].
  move: (kp1 _ yX) => aux; aw; order_tac.
move=> z zu; move: (Hd _ zu)=> le1;  move: zu =>[zs uz]. 
move: (zs); rewrite ss /F => h'; move: (du_index_pr1 h') => [h1 h2 h3]. 
apply /orsum_gleP;split => //; rewrite /order_sum_r; aw.
have Qzk: inc (Q z) K.
  apply: Zo_i; [rewrite /E;order_tac | split =>//].
  move=> kq; case: uxi; exists (P z); split; first by ue.
  move=> y /Zo_P [ys [t [tX yp kq1]]].
  move: (uz _ tX) => /orsum_gleP [_ _].
  case; rewrite - ? kq1 - kq - ? yp; move => [] //.
have aux := (iorder_gle1 (vg _ Qzk)).
case:(equal_or_not v (Q z))=> h4; [ right;split => //;apply: xl; ue | by left].
Qed.

(** When is the set of increasings mappings a complete lattice ? *)

Lemma Exercise1_11f r r': order r -> order r' -> 
  nonempty (substrate r) ->
  complete_lattice (increasing_mappings_order r r') -> complete_lattice r'.
Proof. 
move => or or' nes clf; apply: Exercise1_11b =>//. 
set (E:= substrate r); set (E':=substrate r').
move: (imo_osr r or') => [oim sr1].
move=> X XE'.
set (Y:= Zo (substrate (increasing_mappings_order r r'))
    (fun f => exists2 y, inc y X &
      f = constant_function E E' y)).
have Ys: (sub Y (substrate (increasing_mappings_order r r'))) by apply: Zo_S. 
move: clf => [_ clf']; move: (clf' _ Ys)=> [[f fs] _].  
move:fs => /(lubP oim Ys).
rewrite {1} /upper_bound sr1.  
move => [] [] /soimP [[ff sf tf] incf] fg fge.
move: (nes) => [x xE]. 
set (u:= Vf f x). 
have uE' : (inc u E') by rewrite /E' /u; Wtac. 
exists u; apply /(lubP or' XE'); split. 
  split => // y yE; move:(XE' _ yE) => yE'.
  set (g:= constant_function E E' y).
  have gy: (inc g Y). 
    apply: Zo_i; [by rewrite sr1; apply: constant_increasing | ex_tac].
  move: (fg _ gy) => /(imo_gleP _ or') [_ _].
  by move=> [[p1 p2 p3] [p4 p5 p6] p7]; move: (p7 _ xE);rewrite /g constant_V.
move=> z [zs zu].
set (g:= (constant_function E E' z)). 
have gs: inc g (increasing_mappings r r') by apply: constant_increasing.
have aux: (upper_bound (increasing_mappings_order r r') Y g).
  split; first by rewrite sr1. 
  move=> y /Zo_P [ys [v vX ->]].
  by rewrite -/g  - constant_increasing1//; [ apply: zu | apply:XE'].
move: (fge _ aux) => /(imo_gleP _ or') [_ _] [[p1 p2 p3] [p4 p5 p6] p7]. 
move: (p7 _ xE);rewrite /g constant_V //.
Qed.

Lemma Exercise1_11g r r': order r -> order r' -> 
  complete_lattice r' -> complete_lattice  (increasing_mappings_order r r').
Proof. 
move=> or or' clr; move: (imo_osr r or') => [ori pb].
apply: Exercise1_11b => //; rewrite pb.
set (E:=substrate r); set (E':=substrate r').
move=> X Xsi.
set (img:= fun x => fun_image X (fun f => Vf f x)).
have se: (forall x, inc x E -> sub (img x) E'). 
  move=> x xE t /funI_P [z zX ->].
  move: (Xsi _ zX) => /soimP [[fz sz tez] iz].
  rewrite /E' -tez; apply: Vf_target => //; ue.
set (f:= fun x=> supremum r' (img x)).
have  fp1: (forall x, inc x E -> least_upper_bound r' (img x) (f x)).
  move=> x xE; apply: supremum_pr1 => //.
  exact: (proj1 ((proj2 clr) _ (se _ xE))). 
have ta: (lf_axiom f E E'). 
  by move=> t tE; move: (fp1 _ tE) => /(lubP or' (se _ tE)) [[ti _] _]. 
have ff: (function (Lf f E E')) by apply: lf_function.
have ffj:function_prop (Lf f E E') (substrate r) (substrate r') by saw.
have ffi: (inc (Lf f E E') (increasing_mappings r r')).
  apply /soimP; split => //;saw => x y xy.
  move:(arg1_sr xy)(arg2_sr xy); rewrite -/E => xE yE.
  rewrite /f LfV // LfV //.
  move: (se _ xE) (se _ yE) => a1 a2.
  move:(fp1 _ xE)(fp1 _ yE)=> /(lubP or' a1) [_ p2] /(lubP or' a2)[[h1 h2] _].
  apply: p2; split=>//; move=> t /funI_P [z zX ->].
  have wi: (inc (Vf z y) (img y)) by apply /funI_P; exists z.
  move: (h2 _ wi) => le1.
  move: (Xsi _ zX) => /soimP [_ [_ _ _ df]]; move: (df _ _ xy)=> le2; order_tac.
have Xs: sub X (substrate (increasing_mappings_order r r')) by  rewrite pb. 
exists (Lf f E E'); apply /(lubP ori Xs); split.
  split; first by rewrite pb.
  move=> y yX;move: (Xsi _ yX) =>/soimP [pa incy].
  apply /imo_gleP => //; split; fprops; split; fprops.
  move=> i isr; rewrite LfV//; move: (se _ isr)=> sei.
  move:(fp1 _ isr) => /(lubP or' sei) [[_ fiu] _]; apply: fiu.    
  apply /funI_P;ex_tac.
move=> z []; rewrite pb=> zs zu; apply /imo_gleP => //; split => //. 
move:zs => /soimP [fpy incy]; split => // i ise; rewrite LfV //.
move: (se _ ise)=> sei; move: (fp1 _ ise) => /(lubP or' sei) [h1 h2].
move:(fpy) => [fy sy ty].
apply: h2; split; first  Wtac.
move=> y /funI_P [t tX ->]; apply: (imo_incr or' (zu _ tX) ise).
Qed.

Lemma tarski1 r f: complete_lattice r -> increasing_fun f r r ->
   complete_lattice (induced_order r (fixpoints f)).
Proof.
move => [or clr][_ _ [ff sf tf] incf].
set fif := fixpoints f.
have fs: sub fif (substrate r) by rewrite/fif/fixpoints sf;  apply: Zo_S.
move: (iorder_osr or fs) => [oa sra].
apply Exercise1_11b => //; rewrite iorder_sr //.
move => X xf; move: (sub_trans xf fs) => xsr.
move: (supremum_pr1 or (proj1 (clr _ xsr))).
set w := (supremum r X); move /(lubP or xsr) => [[pa pb] pc].
have ta: inc w (source f) by rewrite sf.
have ra: gle r w (Vf f w).
   apply: pc; split; first by  rewrite - tf; Wtac.  
   by move => y yx;  move: (xf _ yx) => /Zo_P [_ <-];  apply: incf; apply: pb.
set B := Zo (substrate r) (fun t => gle r w t /\ gle r (Vf f t) t).
have bsr: sub B (substrate r) by apply: Zo_S.
move: (infimum_pr1 or (proj2 (clr _ bsr))).
set z := (infimum r B); move /(glbP or bsr) => [[qa qb] qc].
have rb: lower_bound r B (Vf f z). 
   split; first by rewrite - tf; Wtac.
   move => y yb; move: (qb _ yb) => yz; move: (incf _ _ yz) => sa.
   move: yb => /Zo_hi  [_] sb; order_tac.
move: (qc _ rb) => rc; move: (incf _ _ rc) => rd. 
have re: gle r w (Vf f z).  
  have h: lower_bound r B w by split; [ order_tac | move => y /Zo_hi []].
  by move: (incf _ _ (qc _ h)) => h1; order_tac.
have rf: inc (Vf f z) B by  apply: Zo_i; [ order_tac | split => //].
move: (qb _ rf) => rg.
have rh:  Vf f z = z by order_tac.
have ri: inc z fif by apply: Zo_i => //; rewrite sf;order_tac.
have pd: (substrate (induced_order r fif)) = fif by rewrite iorder_sr.
have pe: sub X (substrate (induced_order r fif)) by ue.
exists z; apply /(lubP oa pe); split.
  split; first by rewrite pd. 
  move => y yx; apply /iorder_gle0P => //; first by apply: xf.
  move: (pb _ yx) => yw; rewrite -rh; order_tac.
move => t []; rewrite pd => sa sb; apply /iorder_gle0P => //.
move: (fs _ sa) => sc.
apply: qb; apply: Zo_i => //; split.
  apply: pc;split;[by apply: fs | move => s sy; exact: (iorder_gle1 (sb _ sy))].
by move /Zo_P: sa => [_ ->]; order_tac.
Qed.

(** ---- Exercise 1.12: example of complete lattice *)

Lemma Exercise1_12 E f: function_prop f E E ->
  complete_lattice (sub_order (Zo (\Po E) (fun X =>  sub (Vfs f X) X))).
Proof. 
move=> [ff sf tf]; set F:=Zo _ _. 
move: (sub_osr F) => [or sra].
apply: Exercise1_11b =>// X; rewrite sra => XF.
have fp: sub F (\Po E) by apply: Zo_S. 
have XP: sub X (\Po E) by apply: sub_trans fp.
have uE: sub (union X) E.
  by move=> t /setU_P [y ty yX]; move: (XP _ yX) => /setP_P; apply.
exists (union X); apply: (setU_sup1 fp XF); apply: Zo_i; first by apply /setP_P.
have pa: sub (union X) (source f) by ue.
move=> u /(Vf_image_P ff pa) [v vu ->].
move: vu => /setU_P [y ty yX]; apply /setU_P;ex_tac.
move: (XF _ yX) => /Zo_P [_]; apply; apply /(Vf_image_P ff); last by ex_tac.
by rewrite sf; move: (XP _ yX) => /setP_P.
Qed.

(** ---- Exercise 1.13: Closures. We assume [f] increasing, 
   [ x <= f(x)] and [f(f(x))= f(x) ]. Let [F] be the set of fix-points of [f]. It satisfies some properties and uniquely defines [f]. We consider the case: 
where the set is a lattice or a complete lattice *)


Definition closure  f r := 
  [/\ increasing_fun f r r,
  (forall x, inc x (substrate r) -> gle r x (Vf f x)) &
  (forall x, inc x (substrate r) -> Vf f (Vf f x) = Vf f x)].

Definition upper_bounds F r x := Zo F (fun y => gle r x y).

Section Exercise1_13.
Variables r f: Set.
Hypothesis cf: closure f r.

Lemma Exercise1_13d x y:  lattice r ->
  inc x (substrate r) -> inc y (substrate r) -> 
  Vf f (sup r x y)  = Vf f (sup r (Vf f x) (Vf f y)).
Proof.
move: cf => [icf c1 c2] lr xsr ysr.
move: (icf) => [or or' [ff sf tf] incf].
move: (icf); rewrite Exercise1_10b // => aux; move: (aux _ _ xsr ysr).
have wxs: inc (Vf f x) (substrate r) by rewrite - tf; Wtac.
have wys: inc (Vf f y) (substrate r) by rewrite - tf; Wtac.
move: (lattice_sup_pr lr wxs wys) => [p1 p2 _].
move: (order_transitivity or (c1 _ xsr) p1) => p3.
move: (order_transitivity or (c1 _ ysr) p2) => p4.
move: (lattice_sup_pr lr xsr ysr) => [_ _ aux2].
move: (aux2 _ p3 p4).
set z :=  sup r x y; set T:= (sup r (Vf f x) (Vf f y)).
move => p5 p6; move: (incf _ _ p5)  (incf _ _ p6); rewrite c2; last order_tac.
move=> p7 p8; order_tac.
Qed.


Lemma Exercise1_13c E (F := fixpoints f) : complete_lattice r ->
   sub E F -> inc (infimum r E) F.
Proof.
move: cf=> [icf c2 c3] [_ lr] EF.
move: (icf) => [or or' [ff sf tf] incf].
have sF: (sub F (substrate r)) by rewrite - sf; apply: Zo_S.  
have sE: (sub E (substrate r)) by apply: (sub_trans EF). 
move: (lr _ sE) => [_ hi]; move: (infimum_pr1 or hi).
set (y:= infimum r E); move /(glbP or sE)=> [[yE ylb] yglb].
have wy: (inc (Vf f y) (substrate r)) by rewrite - tf; Wtac.
apply: Zo_i; first (by ue); apply: (order_antisymmetry or); last by apply: c2.
apply: yglb;  split => //; move=> u uE; move: (incf _ _ (ylb _ uE)). 
by move: (EF _ uE) => /Zo_hi ->.
Qed.

Lemma Exercise1_13a x (F := fixpoints f): 
  inc x (source f) -> least (induced_order r (upper_bounds F r x)) (Vf f x).
Proof. 
move: cf => [icf c1 c2] xsf.
move: icf => [or or' [ff sf tf] incf].
have wfl: (inc (Vf f x) (upper_bounds F r x)).
  apply: Zo_i; last by apply: c1; ue.
  apply: Zo_i; [ by rewrite sf - tf; Wtac | apply: c2; ue].
have ssr: (sub (upper_bounds F r x) (substrate r)).
   apply: (@sub_trans F) ;[ apply: Zo_S | rewrite - sf;apply: Zo_S].
rewrite /least iorder_sr //; split => //.
move=> y ysu; apply /iorder_gle0P => //.
move: ysu => /Zo_P [] /Zo_P [ysf Wy] xy; move: (incf _ _ xy); rewrite Wy //.
Qed.

End Exercise1_13.


Lemma Exercise1_13b r G (ir := fun x => induced_order r (upper_bounds G r x))
  (g := Lf (fun x => the_least (ir x)) (substrate r) (substrate r)):
  order r -> sub G (substrate r) ->
  (forall x, inc x (substrate r) ->  has_least (ir x)) ->
  (closure g r /\  (G = fixpoints  g)).
Proof.
move => or Gsr gu.
set (E:= substrate r).
have Ha:forall x, inc x E -> sub (upper_bounds G r x) E.
  move=> x xE; apply: sub_trans Gsr=> //; apply: Zo_S.
pose h x := the_least (ir x).
have pg: forall x,  inc x E -> least (ir x) (h x).
   move=> x xst; apply: the_least_pr; last by apply: gu.
   by apply: (proj1 (iorder_osr or _)); apply: Ha.
have Hc:forall x y, inc x E -> inc y G -> gle r x y -> gle r (h x) y.
  move=> x y xE yG xy; move: (pg _ xE)=> [].
  rewrite/ir iorder_sr//;last by apply: Ha. 
  have ys: inc y (upper_bounds G r x) by apply: Zo_i.
  by move=> aa bb; move: (iorder_gle1 (bb _ ys)).
have Hd:forall x, inc x E -> [/\ inc (h x) E, inc (h x) G & gle r x (h x)].
  move=> x xE; move: (pg _ xE)=> [p1 p2].
  move: (Ha _ xE) => s1; move: p1; rewrite/ir.
  rewrite iorder_sr//; move /Zo_P=> [q1 q2];split;fprops.
have He:forall x, inc x G -> (h x) = x. 
  move=> x xG; move: (Gsr _ xG) => xE. 
  have xs: gle r x x by order_tac.
  move: (proj33 (Hd _ xE)) (Hc _ _ xE xG xs) => le2 le1; order_tac.
have ta: lf_axiom h E E by move=> t tE; case: (Hd _ tE).
have gv: (forall x, inc x E -> Vf (Lf h E E) x = h x)
  by move => x xE; rewrite LfV//. 
have fp:function_prop (Lf h E E) (substrate r) (substrate r). 
   by saw; apply: lf_function. 
split.
  split.
    split => //; aw=> x y xy.
    have xE: inc x E by rewrite /E; order_tac.
    have yE: inc y E by rewrite /E; order_tac.
    rewrite (gv _ xE)(gv _ yE); move: (Hd _ yE) => [p1 p2 p3].
    apply: Hc => //; order_tac.
    by move=> x xE; rewrite (gv _ xE); case: (Hd _ xE).
  move=> x xE; move: (Hd _ xE) => [p1 p2 p3].
  by rewrite (gv _ xE) (gv _ p1); apply: He.
rewrite /g;set_extens t.
  move => tG; move: (Gsr _ tG)=> tE; apply : Zo_i => //; aw; trivial.
  by rewrite LfV//; apply: He.
move => /Zo_P []; rewrite lf_source => te; rewrite LfV// => <-.
by move: (Hd _ te) => [_ ok _].
Qed.


(** ----  Exercise 1.14. Let [R] be a graph on [A x B]. For a subset [X] of [A],
 let [ rho(X) ] the set of elements of [B] related to all elements of [X]. 
For a subset [Y] of [B], let [ sigma(Y) ] the set of elements of [A] related 
to all elemenrts of [Y].  These mappings are decreasing, and the composition is 
a closure  
 *)

Lemma Exercise1_14 A B R
  (rho := fun X => Zo B (fun y => forall x,inc x X -> inc (J x y) R))
  (sigma := fun Y => Zo A (fun x => forall y, inc y Y -> inc (J x y) R))
  (fr:=Lf rho (\Po A) (\Po B))
  (fs:= Lf sigma (\Po B) (\Po A))
  (iA := subp_order A)
  (iB := subp_order B):
  sub R (A \times B) ->
  [/\ decreasing_fun fr iA iB, decreasing_fun fs iB iA,
      closure (compose fs fr) iA & closure (compose fr fs) iB].
Proof. 
move=> sR.
have ta: (lf_axiom rho (\Po A) (\Po B)). 
  move=> t ts; apply /setP_P; apply: Zo_S.
have tb: (lf_axiom sigma (\Po B) (\Po A)). 
  move=> t ts; apply /setP_P; apply: Zo_S.
have tc: forall t, sub t A -> sub (rho t) B.
  by move=> t /setP_P ta1; apply /setP_P; apply: ta.
have td: forall t, sub t B -> sub (sigma t) A.
  by  move=> t /setP_P ta1; apply /setP_P; apply: tb.
have ffr: (function fr) by apply: lf_function.
have ffs: (function fs) by apply: lf_function.
have c1: (fs \coP fr) by split => //; rewrite /fs/fr; aw.
have c2: (fr \coP fs) by split => //; rewrite /fs/fr; aw.
have fc1: (function (fs \co fr)) by fct_tac. 
have fc2: (function (fr \co fs)) by fct_tac.
have i1: (forall u v,  sub u v -> sub (rho v) (rho u)).
   move=> u v uv t => /Zo_P [pa pb]; apply: Zo_i => //; fprops.
have i2: (forall u v,  sub u v -> sub (sigma v) (sigma u)).
   move=> u v uv t  => /Zo_P [pa pb]; apply: Zo_i => //; fprops.
have i3: (forall u v,  sub u v -> sub (sigma (rho u)) (sigma (rho v))).
  by move=> u v uv; apply: i2; apply: i1.
have i4: (forall u v,  sub u v -> sub (rho (sigma u)) (rho (sigma v))).
  by move=> u v uv; apply: i1; apply: i2.
move: (subp_osr A) (subp_osr B)=> [oA sA] [oB sB].
have pa:decreasing_fun fr iA iB.
  split => //; rewrite /fr; aw; first by saw.
  move=> x y /subp_gleP [xA yA xy]; rewrite !LfV//; try apply /setP_P => //.
  apply /subp_gleP;split;fprops.
have pb:decreasing_fun fs iB iA.
  split => //; rewrite /fs;aw ; first by saw.
  move=> x y /subp_gleP [xA yA xy]; rewrite ! LfV//; try apply /setP_P => //.
  apply /subp_gleP;split;fprops.
have Ha: forall x, sub x A -> sub x (sigma  (rho x)).
  move=> x xA t tx; apply: Zo_i; first by apply: xA.  
  by move=> y /Zo_P [yB h]; apply: h.
have Hb: forall x, sub x B -> sub x (rho (sigma x)).
  move=> x xA t tx; apply:Zo_i; first by apply: xA.  
  by move=> y /Zo_P [yB h]; apply: h.
have ic1: (increasing_fun (fs \co fr) iA iA).
  split => //; rewrite /fr/fs; first by saw.
  move=> x y /subp_gleP [xA yA xy].
  have sa: inc x (\Po A) by apply /setP_P.
  have sb: inc y (\Po A) by apply /setP_P.
  rewrite !compfV//; aw; trivial;rewrite (LfV ( c := x)) // (LfV ( c := y)) //.
  rewrite ! LfV//; try apply: ta => //.
  apply /subp_gleP;split;fprops.
have ic2: (increasing_fun (fr \co fs) iB iB).
  split => //; rewrite /fr/fs; aw; first by saw.
  move=> x y /subp_gleP  [xA yA xy].
  have sa: inc x (\Po B) by apply /setP_P.
  have sb: inc y (\Po B) by apply /setP_P.
  rewrite !compfV//; aw; trivial; rewrite (LfV ( c := x)) // (LfV ( c := y)) //.
  rewrite ! LfV//; try apply: tb => //.
  apply /subp_gleP;split;fprops.
split => //; split => //.
+ move=> x; rewrite sA => xA; move: (xA); move /setP_P => xA'.
  rewrite /fr  compfV//;aw; trivial; rewrite LfV// /fs LfV//; last by apply: ta.
  apply /subp_gleP;split => //;[ by apply: td; apply: tc | by apply: Ha].
+ rewrite sA;move=> x xA; set y := Vf (fs \co fr) x. 
  move: (xA) => /setP_P xA'.
  have xs: inc x (source fr) by rewrite /fr; aw.
  have yv: (y  = sigma (rho x)). 
    by rewrite /y compfV // /fr LfV// /fs LfV//; apply: ta.
  have yA: sub y A by rewrite yv;apply: td; apply: tc.
  move : (yA) => /setP_P => yA'.
  have ys: inc y (source fr) by rewrite /fr; aw.
  rewrite compfV// /fr LfV// /fs LfV//; last by apply: ta.
  suff ->: (rho y = rho x) by symmetry. 
  by rewrite yv;apply: extensionality;
     [apply: i1; apply: Ha | apply: Hb; apply: tc].
+ move=> x; rewrite sB => xB; move: (xB); move /setP_P => xB'.
  have xx: inc x (source fs) by rewrite /fs; aw.
  rewrite compfV// /fs LfV// /fr LfV//; last by apply: tb.
  apply /subp_gleP;split => //;[ by apply: tc; apply: td | by apply: Hb].
+ rewrite sB;move=> x xB; set y := Vf (fr \co fs)x. 
  move: (xB) => /setP_P xB'.
  have xs: inc x (source fs) by rewrite /fs; aw.
  have yv: (y  = rho (sigma x)). 
    by rewrite /y compfV// /fs LfV// /fr LfV//; apply: tb.
  have yB: sub y B by rewrite yv;apply: tc; apply: td.
  move : (yB) => /setP_P => yB'.
  have ys: inc y (source fs) by rewrite /fs; aw.
  rewrite compfV // /fs LfV// /fr LfV//; last by apply: tb.
  suff ->: (sigma y = sigma x) by symmetry. 
  by rewrite yv;apply: extensionality;
     [apply: i2; apply: Hb | apply: Ha; apply: td].
Qed.


(** ---- Exercise 1.15. 
Let [sigma(X)] and [rho(X)] be the set of lower and upper bounds of [X]. Let
[f = sigma o rho] this is a closure. The set of fix-points is a complete 
lattice (ordered by inclusion) and is called the completion.
 *)


Definition up_bounds r X :=
  Zo (substrate r)(fun z => upper_bound r X z).
Definition lo_bounds r X :=
  Zo (substrate r)(fun z => lower_bound r X z).
Definition uplo_bounds r X := lo_bounds r (up_bounds r X).
Definition completion r:= 
  Zo (\Po(substrate r)) (fun z => z = uplo_bounds r z).
Definition completion_order r := sub_order (completion r).

Lemma Exercise1_15a1 r A B: sub A B ->
  sub (up_bounds r B) (up_bounds r A).
Proof. 
move => AB t /Zo_P [tsr [_ p2]]; apply /Zo_i => //.
by split=> //; move=> y yA; apply: p2; apply: AB.
Qed. 

Lemma Exercise1_15a2 r A B: sub A B ->
  sub (lo_bounds r B) (lo_bounds r A).
Proof. 
move => AB t /Zo_P [tsr [_ p2]]; apply /Zo_i => //.
by split=> //; move=> y yA; apply: p2; apply: AB.
Qed.

Lemma Exercise1_15a3 r A B: sub A B ->
  sub (uplo_bounds r A) (uplo_bounds r B).
Proof. by  move=>  AB; apply: Exercise1_15a2; apply: Exercise1_15a1. Qed.

Lemma Exercise1_15a4 r A: sub A (substrate r) ->
  sub A (uplo_bounds r A).
Proof. 
move=> Asr t tA; move: (Asr _ tA)=> tsr;apply: Zo_i => //.
by split => //; move=> y /Zo_hi  [_]; apply.
Qed.

Lemma Exercise1_15a5 r A: sub A (substrate r) ->
  lo_bounds r (up_bounds r (lo_bounds r A)) = (lo_bounds r A).
Proof. 
move=> Asr; apply: extensionality. 
  apply: Exercise1_15a2; move=> t tA; move: (Asr _ tA) => tsr;apply: Zo_i =>//.
  by split => //; move=> y /Zo_hi [_]; apply.
apply: Exercise1_15a4; apply: Zo_S.
Qed.

Lemma Exercise1_15a6 r A: sub A (substrate r) ->
  uplo_bounds r (uplo_bounds r A) = (uplo_bounds r A).
Proof. 
move=> Asr; rewrite /uplo_bounds Exercise1_15a5 /up_bounds//.
apply: Zo_S.
Qed.

Lemma Exercise1_15a7 r A: sub A (substrate r) ->
  inc (uplo_bounds r A) (completion r).
Proof. 
move=> Asr; apply: Zo_i; first by apply /setP_P; apply: Zo_S.
by rewrite Exercise1_15a6. 
Qed.

Lemma Exercise1_15a8 r A: sub A (substrate r) ->
  inc (lo_bounds r A) (completion r).
Proof. 
move=> Asr; apply: Zo_i; first by apply /setP_P; apply: Zo_S. 
rewrite /uplo_bounds Exercise1_15a5 //.
Qed.

Section Exercise1_15.
Variable r:Set.
Hypothesis or: order r.

Lemma Exercise1_15a9 x y:
  inc x (substrate r) -> inc y (substrate r) ->
  (lo_bounds r (singleton x) = lo_bounds r (singleton y)) ->
  x = y.
Proof.
move=> xsr ysr h.
have /Zo_hi  [_ p1]  : (inc x (lo_bounds r (singleton y))).
  by rewrite -h; apply: Zo_i => //; split => // u /set1_P ->; order_tac.
have /Zo_hi [_ p2] : (inc y (lo_bounds r (singleton x))).
  by rewrite h; apply: Zo_i => //; split => // v /set1_P ->; order_tac.
move: (p2 _ (set1_1 x)) (p1 _ (set1_1 y)) => q1 q2; order_tac.
Qed.

Lemma Exercise1_15aux: order_on (completion_order r)(completion r).
Proof.
rewrite/order_on/completion_order; split; fprops.
by rewrite (proj2(sub_osr _)).
Qed.

Lemma Exercise1_15a10 e:
  least r e ->
  least (completion_order r) (singleton e).
Proof.
move=> [es le].
have [oc sr] :=  Exercise1_15aux.
have sse: (sub (singleton e) (substrate r)) by move => t /set1_P ->.
have se: inc (singleton e) (completion r).
  apply: Zo_i; first by apply /setP_P.
  apply: extensionality; first by apply: Exercise1_15a4. 
  move=> t /Zo_P [tsr [_ h]]; apply /set1_P.
  apply: (order_antisymmetry or); last by apply: le.
  by apply: h; apply: Zo_i => //; split => // y /set1_P ->; order_tac.
red; rewrite sr; split => //.
move=> x xr; apply /sub_gleP;split => // s /set1_P ->.
move: xr => /Zo_P [] /setP_P h ->; apply: Zo_i => //.
by split => //; move=> y => /Zo_P [ ysr _]; apply: le. 
Qed.

Lemma Exercise1_15a11: 
  ~ (has_least r) ->
  least (completion_order r) emptyset.
Proof. 
move=> nle.
have [oc sr] :=  Exercise1_15aux.
have te: inc emptyset (completion r). 
  apply: Zo_i; first by apply /setP_P; fprops.
  symmetry;apply /set0_P; move=> y; dneg yu; exists y.
  move: yu => /Zo_P [ysr [_ yp]]; split => //.
  move=> x xst; apply: yp;apply: Zo_i=> //; split => //.
  by move=> t /in_set0. 
red;rewrite sr; split => // x xsr;apply /sub_gleP;split;fprops.
Qed.

Lemma Exercise1_15a12 : has_least (completion_order r).
Proof. 
case: (p_or_not_p (has_least r)).
  by move=> [e le]; exists  (singleton e); apply:  Exercise1_15a10. 
by exists emptyset; apply: Exercise1_15a11. 
Qed.

Lemma Exercise1_15a13: greatest (completion_order r) (substrate r).
Proof.
have sc: (inc (substrate r) (completion r)).
  apply: Zo_i; first by aw; apply :setP_Ti.
  apply: extensionality; [ apply: Exercise1_15a4; fprops | apply: Zo_S].
red; rewrite /completion_order; rewrite (proj2 (sub_osr _)).
by split => // x xr; apply /sub_gleP;split => //; move: xr =>/Zo_P [] /setP_P.
Qed.

Lemma Exercise1_15a14 X: sub X (completion r) ->
  least_upper_bound (completion_order r) X (uplo_bounds r (union X)).
Proof.
move=> Xc.
have [oc sr] :=  Exercise1_15aux.
set (v := uplo_bounds r (union X)). 
have vc:inc v (completion r).
  apply: Exercise1_15a7 => t /setU_P [y ty yX]. 
  by move: (Xc _ yX) => /Zo_P [] /setP_P ysr _; apply: ysr.
move: (Xc);rewrite - sr => Xc';apply /(lubP oc Xc'); split.
  split; first (by ue); move=> y yX; rewrite /completion_order; aw. 
  apply /sub_gleP;split => //; first by apply:Xc.
  by move:(Xc _ yX) =>  /Zo_P [ysr] ->; apply: Exercise1_15a3; apply: setU_s1.
move=> z []; rewrite sr => zc h; rewrite /completion_order; aw.
move: zc => /Zo_P [] /setP_P zr ->; rewrite /v.
apply /sub_gleP;split;fprops; first by apply: Exercise1_15a7.
apply: Exercise1_15a3 => t /setU_P [y ty yX].
by move: (h _ yX) =>  /sub_gleP [_ _]; apply.
Qed.

Lemma Exercise1_15a15 X: sub X (completion r) ->  nonempty X ->
  greatest_lower_bound (completion_order r) X
  (uplo_bounds r (intersection X)).
Proof.
move=> Xc neX.
have [oc sr] :=  Exercise1_15aux.
set (v := uplo_bounds r (intersection X)). 
have vc: (inc v (completion r)).
  move: neX => [x xX]; move: (Xc _ xX) =>/Zo_P [] /setP_P xsr _.
  apply: Exercise1_15a7 => t ti; move: (setI_hi ti xX); apply: xsr.
move: (Xc);rewrite - sr => Xc';apply /(glbP oc Xc'); split.
  split; first (by ue); move=> y yX; rewrite /completion_order; aw.
  move:(Xc _ yX) => /Zo_P [] /setP_P ysr ->.
  apply  /sub_gleP;split => //; first by  apply : Exercise1_15a7.
  by apply: Exercise1_15a3; apply :setI_s1.
move=> z []; rewrite sr => zc h; apply  /sub_gleP; split => //.
move: zc => /Zo_P [] /setP_P zr ->.
apply: Exercise1_15a3 => t tz; apply: (setI_i neX).
by move => y yX; move: (h _ yX) => /sub_gleP [_ _]; apply.
Qed.

Lemma Exercise1_15a16: complete_lattice (completion_order r).
Proof.
apply: Exercise1_11b; first by rewrite /completion_order; fprops. 
rewrite {1} /completion_order (proj2(sub_osr _)).
by move=> X Xsr; exists (uplo_bounds r (union X)); apply:Exercise1_15a14.
Qed.


(** [x -> sigma (singleton x)] is an order isomorphism of [E] into a subset of its completion *)

Definition lobs z := lo_bounds r (singleton z).


Lemma Exercise1_15a17:
  lf_axiom lobs (substrate r) (substrate (completion_order r)).
Proof. 
move=> t tsr; rewrite /completion_order  (proj2(sub_osr _)).
by apply: Exercise1_15a8; apply: set1_sub.
Qed.

Lemma Exercise1_15a18a x:
  inc x (substrate r) -> inc x (lobs x).
Proof.
by move=> xsr; apply: Zo_i => //; split => //;move=> u /set1_P ->; order_tac.
Qed.

Lemma Exercise1_15a18: 
  order_morphism (Lf lobs (substrate r) (substrate (completion_order r)))
  r (completion_order r).
Proof. 
move: (Exercise1_15a17).
rewrite /order_morphism/completion_order (proj2(sub_osr _)) => ta.
split => //; first by fprops.
  saw;apply: lf_function => //.
hnf; aw;move=> x y xsr ysr; rewrite !LfV//; split.
  move => xy; apply /sub_gleP;split;fprops.
  move=> t /Zo_P [tsr [_ ts]]; apply :Zo_i => //.
  move: (ts _ (set1_1 x)) => tx.
  split => // u /set1_P ->; order_tac.
move /sub_gleP => [_ _ h]; move: (h _ (Exercise1_15a18a xsr)).
move/Zo_hi => [_]; apply; fprops.
Qed.

Lemma Exercise1_15a19 X x:
  sub X (substrate r) -> least_upper_bound r X x ->
  least_upper_bound  (completion_order r) (fun_image X lobs) (lobs x).
Proof.
move=> Xsr /(lubP or Xsr) [[xX xu] xlu].
have Yc: (sub (fun_image X lobs) (completion r)). 
  move=> y /funI_P [z zX ->]; apply: Exercise1_15a8.
  by move=> t /set1_P ->; apply: Xsr.
suff : uplo_bounds r (union (fun_image X lobs)) = lobs x.
  move=> <-;apply: (Exercise1_15a14 Yc).
apply: extensionality.
  move: (Exercise1_15a5 (set1_sub xX)); rewrite -/(lobs x).
  move => <-; apply: Exercise1_15a3. 
  move=> u /setU_P [y uy /funI_P [z zX slb]].
  move: uy; rewrite slb; move /Zo_P => [usr [_ ulb]].
  move: (ulb _ (set1_1 z)) (xu _ zX) => le1 le2.
  apply: Zo_i=> //; split => //; move => v /set1_P ->; order_tac.
move=> u => /Zo_P[usr [_ leu]]; move: (leu _ (set1_1 x)).
move=> ux; apply: Zo_i => //; split => //. 
move=> y /Zo_P  [ysr [_ yu]].
suff: (gle r x y) by move=> xy; order_tac. 
apply: xlu; split => // v vX; apply: yu.
apply: (@setU_i _ (lo_bounds r (singleton v))).
  by apply: Exercise1_15a18a => //; apply: Xsr.
apply /funI_P; ex_tac.
Qed.

Lemma Exercise1_15a20  X x:
  sub X (substrate r) -> greatest_lower_bound r X x ->
  greatest_lower_bound  (completion_order r) (fun_image X lobs) (lobs x).
Proof.
move=> Xsr /(glbP or Xsr) [[xX xu] xlu].
set Y:= fun_image X lobs.
have Yc: (sub Y (completion r)). 
  move=> y /funI_P [z zX ->]; apply: Exercise1_15a8.
  by move=> t /set1_P ->; apply: Xsr.
have oc: order (completion_order r) by rewrite /completion_order; fprops.
have sr: substrate  (completion_order r) = completion r.
  by rewrite /completion_order (proj2(sub_osr _)).
case: (emptyset_dichot Y) => ye.
  have xE: (X = emptyset). 
    apply /set0_P => u uX; case: (in_set0 (x:=lo_bounds r (singleton u))).
    rewrite -ye; apply /funI_P; ex_tac.
    have -> : lobs x = substrate r. 
    apply: extensionality; first by apply: Zo_S.
    move=> t tsr; apply: Zo_i =>//; split => //;move=> y /set1_P ->; apply: xlu.
    by split => //; rewrite xE; move=> u /in_set0.
    rewrite ye glb_set0 //; exact: Exercise1_15a13.
suff : lobs x = uplo_bounds r (intersection Y).
  move=> ->;apply: (Exercise1_15a15 Yc ye).
have p1: (sub (lobs x) (intersection Y)). 
  move=> u ut; apply: setI_i =>// y /funI_P [z zX slb].
  move: ut =>  /Zo_P [usr [_ aux]]; move: (aux _ (set1_1 x)) => leux.
  rewrite slb; apply: Zo_i => //; split => //; move=> v /set1_P ->.
  move: (xu _ zX) => xz; order_tac.
apply: extensionality.
  move: (Exercise1_15a5 (set1_sub xX)).
  by rewrite -/(lobs x);move => <-; apply: Exercise1_15a3. 
move=> u /Zo_P  [usr [_ leu]]. 
apply: Zo_i => //; split =>//y /set1_P ->; apply: xlu; split => //.
move=> v vX; move: (Xsr _ vX) => vs; apply: leu; apply: Zo_i => //;split => //.
have aux: (inc (lo_bounds r (singleton v)) Y) by apply/funI_P;ex_tac.
move=> w wi; move: (setI_hi wi aux) => /Zo_P [wsr[_ q]].
apply: (q _ (set1_1 v)).
Qed.


Lemma Exercise1_15b1 X:
  sub X (substrate r) -> 
  least_upper_bound (completion_order r) (fun_image X lobs) (uplo_bounds r X).
Proof.
move=> Xsr.
set Y:= fun_image X _ .
have Yc: (sub Y (completion r)). 
  move=> y /funI_P [z zX ->]; apply: Exercise1_15a8.
  by move=> t /set1_P ->; apply: Xsr.
suff: (uplo_bounds r (union Y) = uplo_bounds r X).
  by move <-; apply: Exercise1_15a14.
set_extens t; move /Zo_P => [tsr [_ tp]]; apply: Zo_i => //; split => //;
    move=> y /Zo_P [ysr [_ uy]]; apply: tp; apply: Zo_i => //; split => // u. 
  move /setU_P => [v vy] /funI_P [z zX vp].
  move: vy; rewrite vp => /Zo_P [usr [_ aux]].
  move: (aux _ (set1_1 z)) (uy _ zX) => le1 le2; order_tac.
move => ux;apply: uy; apply: (@setU_i _ (lo_bounds r (singleton u))).
  apply: (Exercise1_15a18a  (Xsr _ ux)).
apply /funI_P; ex_tac.
Qed.

End Exercise1_15.

Lemma Exercise1_15c r: total_order r ->
  total_order (completion_order r).
Proof. 
move: (sub_osr (completion r)) => [pa pb] [or tor].
split => //; rewrite pb => x y xc yc.
have aux: (forall x a b, inc x (completion r) -> 
    inc a x -> gle r b a -> inc b x). 
  move=> v a b /Zo_P [vsr hv].
  rewrite hv => /Zo_P [asr [_ lb]] ab; apply: Zo_i; first by order_tac.
  split; [ by order_tac | move=> w wl; move: (lb _ wl) =>  aw; order_tac ].
case: (p_or_not_p (sub x y)) => h; [left | right];
   apply /sub_gleP;split => //.
move => t ty; ex_middle tx; case: h; move=> z zx; ex_middle zy.
have tsr: inc t (substrate r) by move: yc =>/Zo_P [] /setP_P ysr _; apply: ysr.
have zsr: inc z (substrate r) by move: xc =>/Zo_P [] /setP_P ysr _; apply: ysr.
case:  (tor _ _ tsr zsr) => ctz. 
  case: tx; exact: (aux _ _ _  xc zx ctz).
exact: (aux _ _ _  yc ty ctz).
Qed.

Lemma Exercise1_15b2
  (E := tripleton \0c \1c \2c)
  (r1 := diagonal E \cup doubleton (J \0c \2c) (J \1c \2c))
  (r2 := Nint_cco \0c \2c)
  (f := identity E):
  [/\ [/\ order r1, substrate r1 = E &
     completion r1 = 
     (doubleton (singleton \0c) (singleton \1c)) \cup (doubleton emptyset E)],
   complete_lattice r2, substrate r2 = E,
   increasing_fun f r1 r2 &
   ~(exists g, 
     [/\  (increasing_fun g (completion_order r1) r2),
     (forall t, inc t E -> Vf f t = Vf g (lo_bounds r1 (singleton t)))&
     (forall Z, sub Z (completion r1) ->
       Vf g (supremum (completion_order r1) Z) = 
       supremum r2 (Vfs g Z))])].
Proof.
set goal1 := [/\ _, _  & _].
set goal := [/\ _, _ , _ , _ & _].
have diag1: forall t, inc t E -> inc (J t t) (diagonal E).
  move => t te; apply /diagonal_pi_P; split => //.
have gr1: sgraph r1.
   move => t; case/setU2_P; first by move => /diagonal_i_P [].
   case /set2_P => ->; fprops.
have r1_gle: forall a b, inc (J a b) r1 ->
   [\/ (a = b /\ inc a E), (a = \0c /\ b = \2c) | (a = \1c /\ b = \2c)].
   move => a b; case /setU2_P. 
     by move /diagonal_pi_P => [pa pb]; constructor 1; split.
   case /set2_P =>h; rewrite  (pr1_def h) (pr2_def h); in_TP4.
have r1_refl: forall t, inc t E -> inc (J t t) r1.
   by move => t te; apply /setU2_P; left; apply: diag1.
have sr1: substrate r1 = E.
  set_extens t; last by move => /r1_refl tt; substr_tac.
  case/(substrate_P gr1) => [] [y yi]; case: (r1_gle _ _ yi); case=> //.
  + by move => -> _;  apply /set3_P; in_TP4.
  + by move => -> _;  apply /set3_P; in_TP4.
  + by move => ->.
  + by move => _ ->;  apply /set3_P; in_TP4.
  + by move =>_ -> ;  apply /set3_P; in_TP4.
have or1: order r1.
  split => //.
      red;rewrite sr1 //.
    move => y x z; rewrite /related => ta tb.
    case: (equal_or_not x y); [by move => -> | move => xny].
    case: (equal_or_not y z); [by move => <-| move => ynz].
    apply /setU2_P; right; apply /set2_P.
    case: (r1_gle _ _ tb) =>[] [yv hh'];first (by case: ynz); rewrite hh'.
      by case: (r1_gle _ _ ta) =>[] [hh yv'] => //;rewrite hh; [left | right].
    case: (r1_gle _ _ ta) =>[] [hh yv'];first (by case: xny); rewrite hh;fprops.
  move => x y; rewrite /related => ta tb.
  case: (r1_gle _ _ ta); first (by move => [-> _]); move => [ta1 ta2].
    case: (r1_gle _ _ tb); first (by move => [<- _]); move => [tb1 tb2].
       by rewrite ta1 tb1.
       by rewrite ta2 tb2.
    case: (r1_gle _ _ tb); first (by move => [<- _]); move => [tb1 tb2].
       by rewrite ta2 tb2.
       by rewrite ta1 tb1.
move: NS2 => bs2.
move: clt_12 => lt12.
have le12:= proj1 lt12.
have E0: inc \0c E by apply /set3_P; in_TP4.
have E1: inc \1c E by apply /set3_P; in_TP4.
have E2: inc \2c E by apply /set3_P; in_TP4.
pose rho := up_bounds r1.
pose sigma:= lo_bounds r1.
set d01 := doubleton \0c \1c;set d02 := doubleton \0c \2c. 
set d12 := doubleton \1c \2c.
set s0 := singleton \0c;set s1 := singleton \1c;set s2 := singleton \2c.
have rho1: forall x, sub x E -> inc \2c (rho x).
  move => x xE; apply /Zo_P; rewrite sr1; split => //; split; first by ue.
  move => y yx;apply /setU2_P.
  move: (xE _ yx) =>/ set3_P; case => ->;[right | right | left ]; fprops.
have rho2: rho emptyset = E.
  set_extens t; first by move => /Zo_P []; rewrite sr1.
  by rewrite - sr1; move => te; apply : Zo_i => //; split  => // y /in_set0.
have rho3: forall x, sub x E -> inc \2c x ->  rho x = s2.
  move => x xE x2; apply: set1_pr; first by apply: rho1.
  move => z /Zo_P; rewrite sr1; move =>[ te [_ ts]]; move: (ts _ x2) => h. 
  case: (r1_gle _ _ h) => [][] //. 
have rho4: rho d01 = s2.
  apply: set1_pr; first by apply: rho1; move => s /set2_P [] ->.
  move => z /Zo_P []; rewrite sr1; move => pa [_ pb].
    case/set3_P:pa => tv //.
      move: (pb _ (set2_2 \0c \1c)) => aux. 
      move: (r1_gle _ _ aux); rewrite tv.
      case=>[] [ha hb] //; by case: card1_nz.
   move: (pb _ (set2_1 \0c \1c)) => aux. 
   move: (r1_gle _ _ aux); rewrite tv. 
   by case => [] [] //; move => h _; case: card1_nz.
have rho5: rho s0 = d02.
  rewrite /d02;set_extens t; last first.
    case /set2_P => ->; last by apply: rho1; apply: set1_sub.
    apply: Zo_i; [ue | split; [ ue | move => s /set1_P ->]].
    by rewrite - sr1 in E0; order_tac.
  move /Zo_P => [ta [_ tb]]; move: (tb _ (set1_1 \0c)) => aux. 
  case: (r1_gle _ _ aux);first (move => [-> _]; fprops); move => [_ ->]; fprops.
have rho6: rho s1 = d12.
  rewrite /d12;set_extens t; last first.
    case /set2_P => ->; last by apply: rho1; apply: set1_sub.
    apply: Zo_i; [ue | split; [ ue | move => s /set1_P ->]].
    by rewrite - sr1 in E1; order_tac.
  move => /Zo_P [ta [_ tb]]; move: (tb _ (set1_1 \1c)) => aux.
  case: (r1_gle _ _ aux);first (move => [-> _]; fprops);move => [_ -> ]; fprops.
have sig1:  forall x, sub x E -> inc \1c x ->
    (~ inc \0c (sigma x) /\ ~ inc \2c (sigma x)).
  move => x xe x1; split; move /Zo_P=> [ta [_ tb]].
     case: (r1_gle _ _ (tb _ x1)); move => [h1 h2];
       [by case: card1_nz |by case: (proj2 lt12) |by case: (proj2 lt12) ].
   by case: (r1_gle _ _ (tb _ x1)) => [] [h1 h2]; case: (proj2 lt12).
have sig2:  forall x, sub x E -> inc \0c x ->
    (~ inc \1c (sigma x) /\ ~ inc \2c (sigma x)).
  move => x xe x1; split; move /Zo_P => [ta [_ tb]].
    case: (r1_gle _ _ (tb _ x1)); move => [h1 h2]; 
      first  (by case: card1_nz); by case: card2_nz.
   by case: (r1_gle _ _ (tb _ x1))=> [] [h1 h2]; case: card2_nz.
have sig0: forall x, sub (sigma x) E.
  by move => x t /Zo_P; rewrite  sr1;case.
have sig3: sigma E = emptyset.
  apply /set0_P=> t ts.
  move: (sig1 _ (@sub_refl E) E1) => [pa pb].
  move: (sig2 _ (@sub_refl E) E0) => [pc _].
  by move: (sig0 _ _ ts) => /set3_P [] ta;
      [case: pa | case: pc | case: pb ];  rewrite - ta.
have sig4: sigma d12 = s1.
  have sdE: sub d12 E by move => t /set2_P [] ->.
  move: (sig1 _ sdE (set2_1 \1c \2c)) => [ta tb].
  apply: set1_pr.
    apply: Zo_i; [ by rewrite sr1 | split; first by rewrite sr1].
    move => y; case/set2_P => ->; first by apply: r1_refl.
    apply /setU2_P; right; fprops.
  move=> t ts; move: (sig0 _ _ ts)=> /set3_P [] //H; [ case: ta| case: tb]; ue.
have sig5: sigma d02 = s0.
  have sdE: sub d02 E by move => t /set2_P [] ->.
  move: (sig2 _ sdE (set2_1 \0c \2c)) => [ta tb].
  apply: set1_pr.
    apply: Zo_i; [ by rewrite sr1 | split; first by rewrite sr1].
    move => y;case/set2_P => ->; first by apply: r1_refl.
    apply /setU2_P; right; fprops.
  move=> t ts; move:(sig0 _ _ ts)=> /set3_P [] //H; [ case: ta | case: tb]; ue.
have sig7: sigma s0 = s0.
   have sdE: sub s0 E by move => t /set1_P  ->.
   move: (sig2 _ sdE (set1_1 \0c)) => [ta tb].
   apply: set1_pr.
      apply: Zo_i; [ by rewrite sr1 | split; first by rewrite sr1].
      by move => y /set1_P ->;  apply: r1_refl.
  move => t ts; move:(sig0 _ _ ts) => /set3_P [] //tz;[case: ta |case: tb];ue.
have sig8: sigma s1 = s1.
   have sdE: sub (singleton \1c) E by move => t /set1_P ->.
   move: (sig1 _ sdE (set1_1 \1c)) => [ta tb].
   apply: set1_pr.
     apply: Zo_i; [ by rewrite sr1 | split; first by rewrite sr1].
     by move => y /set1_P ->; apply: r1_refl.
   move=> t ts; move:(sig0 _ _ ts)=> /set3_P [] // h; [case: ta | case: tb]; ue.
have sig6: sigma s2 = E.
  apply: extensionality => // t tE; apply /Zo_P; rewrite/lower_bound sr1. 
  split => //; split => // y /set1_P ->;move: tE => /set3_P;case. 
      move => ->; apply /setU2_P; right; fprops.
    by move => ->; apply /setU2_P; right; fprops.
  by move => ->; apply: r1_refl.
have cpr1: completion r1 = doubleton s0 s1 \cup doubleton emptyset E.
  set_extens t.
  move /Zo_P => [] /setP_P; rewrite sr1 /uplo_bounds.
    move => tE; rewrite -/rho -/sigma => ts; apply /setU2_P; move: ts.
    case: (p_or_not_p (inc \2c t)) => t2.
      move: (rho3 _ tE t2) ->; rewrite sig6 => ->; right; fprops.
    case: (inc_or_not \1c t) => t1; case: (inc_or_not \0c t) => t0.
    + suff ta: t = d01 by rewrite {2} ta rho4 sig6 => ->; right; fprops.
        set_extens s; last by case/set2_P => ->.
        move => st; case/set3_P: (tE s st) => h; rewrite h; fprops.
        by case: t2; ue.
    + suff ta: t = s1 by rewrite {2} ta rho6 sig4 => ->; left; fprops.
        apply: set1_pr => // s st; case/set3_P: (tE _ st) => sa //.
            case: t0; ue.
          case: t2; ue.
    + suff ta: t = s0 by rewrite {2} ta rho5 sig5; move ->; left; fprops.
      apply: set1_pr => // s st; case /set3_P: (tE _ st) => si //.
        case: t1; ue. 
      case: t2; ue.
    + suff ta: t = emptyset by rewrite{2} ta rho2 sig3;move=> ->; right;fprops.
       apply /set0_P => s st;case/set3_P: (tE _ st) => si;
        [case: t0; ue |case: t1; ue | case: t2; ue].
  move => h; apply /Zo_P; rewrite sr1 /uplo_bounds -/rho.
  case/setU2_P: h; case/set2_P => ->. 
  + split; [ by apply /setP_P;apply: set1_sub | by rewrite rho5 ].
  + split; [ by apply /setP_P; apply: set1_sub | by rewrite rho6 ].
  + split; [ apply /setP_P;fprops | by rewrite rho2 ].
  + split; [ apply /setP_P;fprops |by rewrite  (rho3 _  (@sub_refl E) E2)].
have gal1T: goal1 by split.
have tor2: total_order r2.
  move: (proj1(Ninto_wor \0c \2c)); apply: worder_total.
move: (proj1 tor2) => or2.
have sr2': Nintcc \0c \2c = E.
   set_extens t. 
     move /(NintcP NS2)=> ts.
     case: (equal_or_not t \2c) => nt2; first by rewrite nt2.
     by case: (clt2 (conj ts nt2)) => ->.
   move => h; apply /(NintcP NS2).
   case/set3_P: h => ->;fprops; exact: (proj1 clt_02).
have sr2: substrate r2 = E by rewrite (proj2(Ninto_wor \0c \2c)).
have r2_gleP: forall x y, gle r2 x y <-> [/\ inc x E, inc y E & x <=c y].
  move => x y; by move: (Ninto_gleP \0c \2c x y); rewrite sr2'.
have cl2: complete_lattice r2.
  apply: Exercise1_11j => //; rewrite /ne_substrate sr2; last by ex_tac.
  by rewrite - sr2'; apply finite_Nintcc.
have icf: increasing_fun f r1 r2.
  split => //. 
    rewrite /f sr1 sr2; apply: identity_prop.
  move => x y le1.
  rewrite idV; last by rewrite - sr1; order_tac.
  rewrite idV; last by rewrite - sr1; order_tac.
  have xE: inc x E by rewrite - sr1; order_tac.
  have yE: inc y E by rewrite - sr1; order_tac.
  apply /r2_gleP; split => //; move: (r1_gle _ _ le1); case.
       move => [-> _]; apply: cleR; case/set3_P: yE; move => ->; fprops. 
    move: xE; rewrite - sr2' => le2.
     move => [-> ->]; fprops; apply: (proj1 clt_02).
    move => [-> ->]; fprops.
split => // [] [g [incrg cpgf cgs]].
move: (cpgf _ E0); rewrite /f (idV E0) -/sigma sig7 => g0.
move: (cpgf _ E1); rewrite /f (idV E1) -/sigma sig8 => g1.
move: (cpgf _ E2); rewrite /f (idV E2) -/sigma sig6 => g2.
set Z := doubleton s0 s1.
have Zd: sub Z (completion r1).
    rewrite cpr1; apply: sub_set2; apply /setU2_P; left; fprops.
move: (esym (cgs _ Zd)).
move: incrg => [_ _ [fg srcg trgg _]].
move: (proj2 (sub_osr (completion r1))) => hh.
have zg1: sub Z (substrate (completion_order r1)) by ue.
have ->:  (Vfs g Z) = d01.
  have esg: sub Z (source g) by ue.
  set_extens t.
     move /(Vf_image_P fg esg)=> [u uz ->]; move:uz => /set2_P; case => ->; ue.
  case/set2_P => ->; apply /(Vf_image_P fg esg).
      rewrite /Z;exists s0; fprops. 
   rewrite /Z;exists s1; fprops.
have ->: supremum r2 d01 = \1c.
  apply: sup_comparable1 => //; apply /r2_gleP;split; fprops;apply: cle_01.
suff h: supremum (completion_order r1) Z = E by rewrite h -g2;exact: card_12.
move: (Exercise1_15a16 r1) => [oc h];  move: (h _ zg1) => [hs _].
move: (supremum_pr oc zg1 hs).
set z := supremum _ _; move => [[za zb] zc].
move: za; rewrite hh => zr1.
move /sub_gleP: (zb _ (set2_1 s0 s1)) => [_ _ ta].
move /sub_gleP: (zb _ (set2_2 s0 s1)) => [_ _ tb].
move: (ta _ (set1_1 \0c)) => z0.
move: (tb _ (set1_1 \1c)) => z1.
move: zr1; rewrite cpr1; case/setU2_P; case /set2_P => zt.
+ by move:z1; rewrite zt => /set1_P bad; case: card1_nz.
+ by move:z0; rewrite zt => /set1_P bad; case: card1_nz.
+ by move:z1; rewrite zt => /in_set0.
+ done.
Qed.


  
(** ---- Exercise 1.16 Distributive lattices, see main text *)


(** ---- Exercise 1.17 Boolean lattices *)

Definition complement_pr r x y x' :=
 [/\ inc x' (substrate r), sup r x x' = y & inf r x x' = the_least r].

Definition relatively_complemented r:=
  [/\ lattice r, has_least r &
  (forall x y, gle r x y -> exists x', complement_pr r x y x')].

Definition boolean_lattice r:=
  [/\ relatively_complemented r, has_greatest r &
  distributive_lattice3 r].

Definition the_complement r x y:=
   select (complement_pr r x y) (substrate r).

Definition standard_completion r x :=
  the_complement r x (the_greatest r).

Lemma least_greatest_pr1 r a: boolean_lattice r ->
  inc a (substrate r) ->
 [/\ sup r (the_least r) a = a,
    inf r a (the_greatest r) = a,
    inf r (the_least r) a = (the_least r) &
    sup r a (the_greatest r) = (the_greatest r)].
Proof.
move=>  [[[or _] el _] eg _] asr.
move: (least_greatest_pr or) => [h1 h2 h3 h4];split; fprops.
Qed.


Lemma Exercise1_17a r x y:  relatively_complemented r ->
  distributive_lattice3 r -> gle r x y -> 
  exists! x', complement_pr r x y x'.
Proof. 
move => [lr el ec] dl3 xy; move: (lr) => [or _].
apply /unique_existence; split.
  by move:(ec _ _ xy) => [z za];exists z.
move=> u v [us su iu][vs sv iv].
move:(lattice_props lr).
set (E:= substrate r). 
move => [sE [iE [sixy [isxy [sxyz [ixyz [sxx [ixx [sxyx ixyx]]]]]]]]].
move:(arg1_sr xy) (arg2_sr xy) => xE yE.
move: (dl3 _ _ _ us xE vs). 
rewrite (inf_C r u x) (sup_C r u x) iu iv su sv.
move: (least_greatest_pr or) => [p1 _ _ _];rewrite ! (p1 el _  (iE _ _ vs us)).
move: (lattice_sup_pr lr xE us)(lattice_sup_pr lr xE vs)=> [_ h2 _][_ h3 _].
move: (lattice_sup_pr lr vs us) => [q1 q2 q3].
move: h2 h3; rewrite su sv; move=> h2 h3; move: (q3 _ h3 h2) => h4.
rewrite (inf_C r y _) (inf_C r y _) ! (inf_comparable1 or  h4) => infs.
move: (lattice_inf_pr lr vs us); rewrite infs; move => [r1 r2 r3].
move: (order_transitivity or q1 r2)(order_transitivity or q2 r1) => h5 h6.
order_tac.
Qed.

Lemma the_complement_pr r x y:
  relatively_complemented r -> distributive_lattice3 r -> gle r x y ->
  complement_pr r x y (the_complement r x y).
Proof. 
move => pa pb pc.
move: (Exercise1_17a pa pb pc) => /unique_existence [[z zv] pe].
have pf: exists2 x0, inc x0 (substrate r) & complement_pr r x y x0.
  by exists z => //; case: zv.
have pg: singl_val2 (inc^~ (substrate r)) (complement_pr r x y).
  by move => a b qa qb qc qd; apply: pe.
exact: (proj1(select_pr pf pg)).
Qed.

Lemma scompl_pr r x:
  boolean_lattice r -> inc x (substrate r) ->
  complement_pr r x (the_greatest r) (standard_completion r x).
Proof.
move=>  [rr eg dl3] xsr; move: (rr) => [[or _] _ _].
apply:the_complement_pr => //.
exact: (proj2(the_greatest_pr or eg) _ xsr).
Qed.

Lemma scompl_unique r x y:
  boolean_lattice r -> inc x (substrate r) ->
  complement_pr r x (the_greatest r) y ->
  y = standard_completion r x.
Proof.
move=>  blr xsr h1.
move: (scompl_pr blr xsr) => h2.
move: blr => [bl1 bl2 bl3].
move: (bl1) => [[or _] _ _].
move: (proj2 (the_greatest_pr or bl2) _ xsr) => xg.
by move: (Exercise1_17a bl1 bl3 xg) => /unique_existence [_]; apply.
Qed.

Lemma scomplI r x:
  boolean_lattice r -> inc x (substrate r) ->
  standard_completion r (standard_completion r x) = x.
Proof. 
move=> blr xsr; move: (scompl_pr blr xsr). 
rewrite /complement_pr sup_C inf_C ;move  => [ysr ym yq].
symmetry; apply: scompl_unique => //.
Qed.

Lemma scompl_mon r x y:
  boolean_lattice r -> gle r x y ->
  gle r (standard_completion r y) (standard_completion r x).
Proof.
move=> blr xy.
move: (arg1_sr xy) (arg2_sr xy) => xE yE.
move: (scompl_pr blr xE) (scompl_pr blr yE).
move=> [aE supa infa] [bE supb infb].
move: (blr) => [[lr _ _] eg dl3];move: (lr) => [or _].
move:(lattice_props lr).
set (E:= substrate r).
move => [sE [iE [sixy [isxy [sxyz [ixyz [sxx [ixx [sxyx ixyx]]]]]]]]].
set (a:= standard_completion r x).
set (b:= standard_completion r y).
set (c := inf r a b). 
have iyc: (inf r y c = the_least r). 
  rewrite /c (inf_C r a b) (ixyz _ _ _ yE bE aE) infb.  
  by move: (least_greatest_pr1 blr aE)=> [_ _ ok _].
move: (sE _ _ yE aE) => yaE. 
have syc: sup r y c = sup r y a. 
  rewrite/c (proj32 (distributive_lattice_prop2 lr)) //.
  rewrite supb;exact: (proj42 (least_greatest_pr1 blr yaE)).
move: (proj2 (the_greatest_pr or eg) _ yaE)=> le1.
have : (gle r (sup r x a) (sup r y a)).
  by rewrite sup_C (sup_C r y a); apply: sup_monotone.
rewrite supa => le2; rewrite (order_antisymmetry or le1 le2) in syc.
move: (iE _ _ aE bE) => cE.
have yc: c = standard_completion r y by apply: scompl_unique.
move: (lattice_inf_pr lr aE bE) => [ac _ _]; rewrite -/c yc in ac; exact ac.
Qed.

Lemma Exercise1_17b r: boolean_lattice r ->
  order_isomorphism (Lf (standard_completion r) (substrate r)(substrate r))
  r (opp_order r).
Proof. 
move=> blr.
have ta: (lf_axiom (standard_completion r) (substrate r) (substrate r)).
  by move=> t tsr; move: (scompl_pr blr tsr) => [ok _].
move: (blr) => [[[or _] _ _ ] _ _].
move: (opp_osr or) => [pa pb].
split => //.
  saw; try ue; apply: lf_bijective =>//.
    move=> u v uE vE ss; rewrite -(scomplI blr uE) -(scomplI blr vE) ss //.
  by move => u uE; move: (ta _ uE) => h; ex_tac; rewrite  (scomplI blr uE). 
red; aw;move=> x y xE yE; rewrite !LfV//; split.
  by move => h; apply /opp_gleP; apply: scompl_mon.
move /opp_gleP; rewrite -{2} (scomplI blr xE) -{2} (scomplI blr yE).
by apply: scompl_mon.
Qed.

Lemma Exercise1_17c A:
  boolean_lattice (subp_order A) /\ 
    (forall x, inc x (\Po A) ->
      standard_completion (subp_order A) x = A -s x).
Proof.
move: (subp_osr A) => [];set (r:=subp_order A) => or sr.
have ha:= setP_0i A.
have lee: (least r emptyset).
  split; first by rewrite sr.
  move=> x; rewrite /r sr => h; apply /sub_gleP;split;fprops.
have el: has_least r by exists emptyset. 
have thel: (the_least r = emptyset) by apply: the_least_pr2.
move: (setP_Ti A) => hh. 
have geA: (greatest r A).
  red; rewrite sr /r; split => // s sp.  
  apply /sub_gleP;split => //; apply /setP_P => //.
have eg: has_greatest r by exists A.
have theg: (the_greatest r = A) by apply: the_greatest_pr2.
move: (sup_inclusion (A:=A)) => les.
move: (inf_inclusion (A:=A)) => ges.
have lr: lattice r by apply: setP_lattice.
have le1: (forall x y, inc x (\Po A) -> inc y (\Po A) ->
    sup r x y = x \cup y).
  move=> x y /setP_P xA /setP_P yA; symmetry. 
  by apply: (supremum_pr2 or); apply: les.
have ge1: (forall x y, inc x (\Po A) ->inc y (\Po A) ->
    inf r x y = x \cap y).
  move=> x y /setP_P xA /setP_P yA; symmetry. 
  by apply: (infimum_pr2 or); apply: ges.
have rc: forall x y, sub x y -> sub y A ->
    [/\ inc  (y -s x) (substrate r), sup r x  (y -s x) = y &
      inf r x  (y -s x) =  the_least r].
  move=> x y xy yA. 
  have xA:inc x (\Po A) by apply /setP_P;apply: sub_trans yA.
  have cA: inc (y -s x) (\Po A).
    by apply /setP_P; move=> t /setC_P [ty _]; apply: yA.
  rewrite sr le1 // ge1 // thel; split;fprops.
    move /setI2id_Pr: xy => {1} <-; exact: setI2_Cr.
  by apply /set0_P => t /setI2_P [tx] /setC_P [_] ntx.
have iuA: forall x y, inc x (\Po A) -> inc y (\Po A) -> 
   (inc (x \cup y) (\Po A) /\ inc (x \cap y) (\Po A)).
  move => x y /setP_P xa /setP_P ya; split; apply/setP_P => t.
    by case/setU2_P; fprops.
    move /setI2_P => [tx ty]; fprops.
have dl3: (distributive_lattice3 r).
  apply /(distributive_lattice_prop3 lr).
  move=> x y z; rewrite sr => xA yA zA.
  move:(proj2 (iuA _ _ yA zA)) (proj1 (iuA _ _ xA yA)) => iyzA uxyA.
  rewrite (ge1 _ _ yA zA) (le1 _ _ xA yA) (le1 _ _ xA iyzA) (ge1 _ _ zA uxyA). 
  apply /sub_gleP.
  split; [ apply (proj2(iuA _ _ zA uxyA)) | apply (proj1(iuA _ _ xA iyzA)) |].
  move=> t /setI2_P [tz]; case/setU2_P => tx; first by apply /setU2_P; left.
  by apply /setU2_P; right; fprops. 
have rc1:relatively_complemented r. 
  split => //; move=> x y /sub_gleP [xA yA xy].
  by exists (y -s x); apply: rc => //; apply /setP_P.
have bl: boolean_lattice r by split => //.
split => // x xa; move : (xa) => /setP_P xA.
have sAA: sub A A by fprops.
symmetry;apply: scompl_unique =>//; try ue.  
by red; rewrite theg; apply: rc.
Qed.

Lemma Exercise1_17d r x y: boolean_lattice r ->
  inc x (substrate r) ->  inc y (substrate r) ->
  let ys := (standard_completion r y) in 
  [/\ inf r y (sup r ys x) = inf r y x,
  sup r y (inf r ys x) = sup r y x,
  inf r ys (sup r y x) = inf r ys x &
  sup r ys  (inf r y x) = sup r ys x].
Proof. 
move=> blr xsr ysr ys.
move: (blr) => [[lr _ _] _ dl3]; move: (lr) => [or _].
move: (scompl_pr blr ysr); rewrite -/ys; move=> [ys1 ys2 ys3].
move: (distributive_lattice_prop2 lr) => [_ ok1 ok2].
rewrite ((ok1 dl3) _ _ _ ysr ys1 xsr) ((ok1 dl3) _ _ _ ys1 ysr xsr).   
rewrite ((ok2 dl3) _ _ _ ysr ys1 xsr) ((ok2 dl3) _ _ _ ys1 ysr xsr).   
rewrite (sup_C r ys y) (inf_C r ys y) ys2 ys3.
move:(lattice_props lr) =>/=; move => [sE [iE _]]; split.
by case: (least_greatest_pr1 blr (iE _ _ ysr xsr)).
by rewrite inf_C;move: (least_greatest_pr1 blr (sE _ _ ysr xsr))=> [_ ].
by case: (least_greatest_pr1 blr (iE _ _ ys1 xsr)).
by rewrite inf_C;move: (least_greatest_pr1 blr (sE _ _ ys1 xsr)) => [_].
Qed.

Lemma Exercise1_17e r x y: boolean_lattice r -> complete_lattice r ->
  inc y (substrate r) -> sub x (substrate r)->
  inf r y (supremum r x) 
   = supremum r (fun_image x (fun z => inf r y z)).
Proof.
move=> blr [or clr] ysr xsr.
move: (blr) => [[lr _ _] _ _].
move: (clr _ xsr) => [hsx _].
move: (supremum_pr1 or hsx) => /(lubP or xsr) [[sxs sxu] sxp].
move: (lattice_inf_pr lr ysr sxs).
set (v:= inf r y (supremum r x)); move => [p1 p2 p3].
set Y:= fun_image x _.
have sY: sub Y (substrate r).
  move => t /funI_P [z zx ->].
  move:(lattice_inf_pr lr ysr (xsr _  zx)) => [h _ _]; order_tac.
move: (clr _ sY) => [hsy _].
move: (supremum_pr1 or hsy) => /(lubP or sY).
set (u:= supremum r Y);move=> [[sus syu] syp].
set ys:= (standard_completion r y).
have leuv: gle r u v.
  apply: syp; split; first (by order_tac); move=> t /funI_P [z zx ->]. 
  move:(lattice_inf_pr lr ysr (xsr _  zx)) => [h1 h2 h3]. 
  apply: p3 => //; move: (sxu _ zx) => zs; order_tac.
have le1: gle r u y by order_tac.
have <-:(inf r y (sup r ys u) = u). 
  by rewrite (proj41 (Exercise1_17d blr sus ysr)) inf_C; apply: inf_comparable1.
rewrite /v - (proj41 (Exercise1_17d blr sxs ysr)).
apply: f_equal.
move: (proj31 (scompl_pr blr ysr)); rewrite -/ys=> q1.
move: (lattice_sup_pr lr q1 sxs) (lattice_sup_pr lr q1 sus). 
set z:= (sup r ys u); set z' :=(sup r ys (supremum r x)).
move=>[r1 r2 r3] [r4 r5 r6].
apply: (order_antisymmetry or).
  apply: r3; first (by exact); apply: sxp; split; first by order_tac.
  move => t tx.
  have iyt: inc (inf r y t) Y by apply /funI_P; ex_tac.
  move: (sup_monotone lr q1 (syu _ iyt)).
  move: (Exercise1_17d blr (xsr _ tx) ysr) =>[_ _ _ aux ].
  rewrite /ys aux -/ys -/z => le4.
  move: (lattice_sup_pr lr q1  (xsr _ tx)) => [_ le5 _]; order_tac.
apply: r6; first (by exact); apply: syp; split; first by order_tac.
move=> t /funI_P [s sx ->].
have le2:=(proj32 (lattice_inf_pr lr ysr (xsr _ sx))).
have le3 := (proj32 (lattice_sup_pr lr q1 sxs)). 
apply: (order_transitivity or le2 (order_transitivity or  (sxu _ sx) le3)).
Qed.

(** ---- Exercise 1.18. Example of a complete lattice that is not distributive 
  but relatively complemented *)

Definition intersection_partition2 u v :=
   (intersection_covering2 u v) -s1 emptyset.

Lemma disjoint_pr1 a b:
  (forall x, inc x a -> inc x b -> a = b) ->
  (disjointVeq a b).
Proof. 
move=> h; case: (equal_or_not a b); first by left.
move=> nab;right;apply: disjoint_pr; move=> u ua ub; case: nab; apply: h ua ub.
Qed.

Lemma intersection_is_partition2 u v x:
  partition_s u x -> partition_s v  x ->
  partition_s (intersection_partition2 u v) x.
Proof.
move=> ux vx; rewrite /intersection_partition2. 
split; first split; last by move => t /setC1_P/proj2/nonemptyP.
  set_extens t.
    move=> /setU_P [y ty] /setC1_P [] /setI_covering2_P  [a [b [au bv yv]]] _.
    move: ux => [[<- _] _]; apply /setU_P; ex_tac.
    by move: ty; rewrite -yv; move /setI2_P => [ta _].
  move=> tx; move: tx (tx); move: ux vx => [ [ {2} <- _] _] [[<- _] _].
  move => /setU_P [y1 ty1 y1u] /setU_P [y2 ty2 y2u].
  have ti: inc t (y1 \cap y2) by apply: setI2_i.
  apply /setU_P;exists (y1 \cap y2) => //. 
  apply/setC1_P; split; first by apply /setI_covering2_P; exists y1, y2.
  by apply/nonemptyP; exists t.
move=> a b /setC1_P [] /setI_covering2_P [a1 [b1 [a1u b1v]]] <- _
  /setC1_P [] /setI_covering2_P [a2 [b2 [a2u b2v]]] <- _.
apply: disjoint_pr1 => w /setI2_P [w1 w2] /setI2_P [w3 w4]. 
move:(proj2 (proj1 ux)) (proj2 (proj1 vx)) => ha hb.
have ->: a1=a2 by case: (ha _ _  a1u a2u) => // h1; empty_tac1 w.
have -> //: b1=b2 by case:(hb _ _ b1v b2v) => // d1; empty_tac1 w.
Qed.

Lemma intersection_p2_comm u v: 
  (intersection_partition2 u v) = (intersection_partition2 v u).
Proof.
set_extens t; move /setC1_P => [] /setI_covering2_P [a [b [au bv it]]] net;
  apply /setC1_P; split => //; apply /setI_covering2_P; 
  by exists b, a; rewrite setI2_C. 
Qed.

Lemma intersection_is_sup2_a u v x:
  partition_s u x -> partition_s v  x ->
  gle (coarser x) u (intersection_partition2 u v).
Proof.
move=> pu pv; apply /coarser_gleP; split => //.
  by apply: intersection_is_partition2.
move=> y /Zo_P [] /setI_covering2_P [a [b [au bv h]]] _.
ex_tac; rewrite -h;apply: subsetI2l.
Qed.

Lemma intersection_is_sup2 u v x:
  partition_s u x -> partition_s v  x ->
  least_upper_bound (coarser x)(doubleton u v)(intersection_partition2 u v).
Proof. 
move=> pu pv;apply: lub_set2.
      apply: (proj1 (coarser_osr _)).
    by apply: intersection_is_sup2_a.
  by rewrite intersection_p2_comm; apply: intersection_is_sup2_a.
move=> t /coarser_gleP [_ pt c1] /coarser_gleP [_ _ c2].
apply /coarser_gleP;split => //;first by apply intersection_is_partition2.
move=> A At; move: (c1 _ At)(c2 _ At) => [b bu Ab] [c cv Ac].
have sA: sub A (b \cap c) by move=> w wA;apply: setI2_i; fprops. 
exists (b \cap c) => //; apply: Zo_i. 
  apply /setI_covering2_P; exists b, c; split => //.
move: ((proj2 pt) _ At)  => [w /sA wA] /set1_P wne; empty_tac1 w.
Qed.

Lemma intersection_is_sup2_b E u v:
   partition_s u E -> partition_s v E ->
   sup (coarser E) u v = (intersection_partition2 u v).
Proof.
move: (coarser_osr E) => [pa pb] pu pv.
have i2 :=(intersection_is_sup2 pu pv).
have hs: (has_supremum (coarser E) (doubleton u v)).  
  by exists (intersection_partition2 u v).
have sd: (sub (doubleton u v) (substrate (coarser E))). 
  by move => t; rewrite pb;case/set2_P => ->; apply /partitionsP.
by apply: (supremum_unique pa (supremum_pr1 _ hs) i2).
Qed.

Definition intersection_partition f :=
  (fun_image (productb f) intersectionb) -s1 emptyset.

Lemma intersection_is_partition f x:
  fgraph f ->  (allf f (partition_s ^~ x)) ->
  nonempty (domain f) ->
  partition_s (intersection_partition f) x.
Proof. 
move=> fgf alp nedf; move: (nedf) => [w wdf].
split; last by  move=> a /setC1_P [_] /nonemptyP.
rewrite /intersection_partition; split.
  set_extens t.
      move=> /setU_P [y ty] /setC1_P [] /funI_P [z zp h] _.
      move: (alp _ wdf) => [[pu1 pu3] pu2].
      move: zp => /setXb_P [fgz df VV]; rewrite -df in wdf.
      have aux: inc t (Vg z w) by rewrite h in ty; apply: (setIb_hi ty wdf).
      rewrite -pu1; apply /setU_P; exists (Vg z w) => //; apply: VV; ue.
    move => tx; apply /setU_P.
  pose g u := select (inc t) (Vg f u).
  have gp u: inc u (domain f) -> inc t (g u) /\ inc (g u) (Vg f u).
    move=> udf; move:(alp _ udf) tx =>[[<- aa] bb] /setU_P [z z1 z2].
    apply: select_pr; [ ex_tac | move => v1 v2 ha hb hc hd].
    move: (aa v1 v2 ha hc); case => //; rewrite /disjoint=> dd; empty_tac1 t.
  set (h:= Lg (domain f) g). 
  have tih:(inc t (intersectionb h)).  
    apply: setIb_i.
      exists (J w (Vg h w)); apply: fdomain_pr1; rewrite /h; aww.
    move=> i; rewrite /h Lgd => idf; move: (gp _ idf) => [res _]; rewrite LgV//.
  have hp:(inc h (productb f)).
    apply /setXb_P; rewrite /h;aw; split;fprops;move=> i idf; rewrite LgV//.
    exact: (proj2(gp _ idf)). 
  exists (intersectionb h) => //; apply /setC1_P; split. 
      apply /funI_P;ex_tac.
  move=> he; move: tih; rewrite he; case/in_set0.
move => a b /setC1_P [] /funI_P [z1 z1p] -> _
     /setC1_P [] /funI_P  [z2 z2p] -> _.
apply: disjoint_pr1 => y yi1 yi2.
move: z1p z2p => /setXb_P [fg1 dz1 VV1] /setXb_P [fg2 dz2 VV2].
apply: f_equal; apply: fgraph_exten => //; [ue | move=> i idf /=].
rewrite -dz1 in VV1.
move: (VV1 _ idf)(setIb_hi yi1 idf) => p1 p2.
rewrite -dz2 in VV2; rewrite dz1 -dz2 in idf.
move: (VV2 _ idf) (setIb_hi yi2 idf)=> p3 p4.
rewrite dz2 in idf.
case:(proj2 (proj1 (alp _ idf)) _ _ p1 p3) => // di; empty_tac1 y.
Qed.

Lemma intersection_is_sup_a f x y:
  fgraph f -> (allf f (partition_s ^~ x)) ->
  inc y (range f) ->
  gle (coarser x) y (intersection_partition f).
Proof.
move=> fgf alp  /(range_gP fgf) [z zdf ->].
have ne: nonempty (domain f) by exists z.
apply /coarser_gleP; split;fprops; first by apply: intersection_is_partition.
move=> a /setC1_P [] /funI_P [t zt h] _.
move: zt => /setXb_P [fgt dt VV]; move: (VV _ zdf) => aux.
ex_tac; rewrite h; move=> w wi; apply: (setIb_hi wi); ue.
Qed.

Lemma intersection_is_sup f x:
  fgraph f ->  (allf f (partition_s ^~ x))  ->
  nonempty (domain f) ->
  least_upper_bound (coarser x) (range f) (intersection_partition f).
Proof.
move=> fgf alp nef.
move: (intersection_is_partition fgf alp nef) => ip.
move: (coarser_osr x)  => [pa pb].
have aux: forall u, inc u (substrate (coarser x)) <-> partition_s u x.
  by move=> u; rewrite pb; apply:partitionsP. 
have aux2: sub (range f) (substrate (coarser x)).
  by move => t /(range_gP fgf) [u udf] ->; apply/aux;apply: alp.
apply /(lubP pa aux2).
split; first by split;[ apply/aux | move=> y; apply: intersection_is_sup_a].
move=> z [];rewrite aux => pzx zle.
apply /coarser_gleP;split => // t tz.
pose g u := select (sub t) (Vg f u).
have gp u: inc u (domain f) -> sub t (g u) /\ inc (g u) (Vg f u).
  move=> udf;move: (zle _ (inc_V_range fgf udf)). 
  move/coarser_gleP => [aa bb h]; move: (h _ tz) => [zz za zb].
  apply: select_pr; first ex_tac.
  move => v1 v2 /= ha hb hc hd.
  move: (proj2 pzx _ tz) => [w wt]. 
  case: ((proj2 (proj1 aa)) v1 v2 ha hc) => //.
  rewrite /disjoint=> dd; empty_tac1 w.
have ai: (sub t (intersectionb (Lg (domain f) g))). 
  move=> v vt; apply: setIb_i.
    move: nef => [y ydf]; exists (J y (Vg (Lg (domain f) g) y)).
    apply: fdomain_pr1; aww. 
  by aw; move=> i idf; rewrite LgV//; apply: (proj1 (gp _ idf)).
exists (intersectionb (Lg (domain f) g)); last by exact.
apply /setC1_P; split; last first.
  move: (proj2 pzx _ tz) => [b bt]; move=> ie; empty_tac1 b.
apply /funI_P.
exists (Lg (domain f) g) => //; apply /setXb_P; split => //;aw; fprops.
by move=> i idf; rewrite LgV//; case: (gp _ idf).
Qed.

Lemma Exercise1_18a E:  complete_lattice (coarser E).
Proof. 
move: (coarser_osr E) => [coE soE].
apply: (Exercise1_11b coE).
have aux: forall u, inc u (substrate (coarser E)) <-> partition_s u E.
  by move=> u; rewrite soE; apply/partitionsP. 
move=> X XsE;case: (emptyset_dichot X) => neX; last first.
  set (f := identity_g X). 
  have fgf: (fgraph f) by apply: identity_fgraph.
  have rf: (range f = X) by apply: identity_r.
  have df: (domain f = X) by apply: identity_d.
  rewrite -df in neX; rewrite -rf.
  exists (intersection_partition f);apply: (intersection_is_sup fgf _ neX).
  by rewrite/allf df /f => u uX; rewrite (identity_ev uX); move/aux:(XsE _ uX).
rewrite neX. 
case: (emptyset_dichot E) => Ee.
  have pE: (partition_s emptyset E).
    split; last by move=> a /in_set0.
    split; [by rewrite Ee setU_0 |  by move=> a b /in_set0 ].
  exists emptyset; rewrite lub_set0 //; split;first by apply/ aux.
  move => x /aux xE; apply /coarser_gleP; split => //; move=> t tx.
  move:(proj2 xE _ tx) => [w wt].
  move: (proj1(proj1 xE)); rewrite Ee => p1; empty_tac1 w; union_tac.
exists (least_partition E).
rewrite lub_set0 //; split. 
  by apply/ aux; apply: least_is_partition.
move=> x /aux px; apply/coarser_gleP; split => //.
  by apply: least_is_partition.
move=> a ax; exists E; first by rewrite /least_partition; fprops.
by  rewrite - (proj1(proj1 px)); apply: setU_s1.
Qed.

(** This set is not distributive if there are at least three elements *)
Lemma Exercise1_18b E: \3c <=c (cardinal E) -> 
  ~ (distributive_lattice1 (coarser E)).
Proof.
move /cardinal_ge3 => [x [y [z [xE yE zE [xy xz yz]]]]].
set (o:= tripleton x y z); set (F:= E -s o).
have oz: inc z o by apply /set3_P; in_TP4.
have oy: inc y o by apply /set3_P; in_TP4.
have ox: inc x o by apply /set3_P; in_TP4.
have xnF: ~ (inc x F) by move /setC_P => [_]; case. 
have ynF: ~ (inc y F) by move /setC_P => [_]; case.
have znF: ~ (inc z F) by move /setC_P => [_]; case.
have Ha: forall x, singleton x <> emptyset by move => u se; empty_tac1 u.

pose with_F u :=  (u +s1 F) -s1 emptyset.
have wf1: (forall u, ~ (inc emptyset u) -> F = emptyset -> with_F u = u).
  by move=> u nsu Fe; rewrite /with_F Fe; apply: setU1_K.
have wf2: (forall u, ~ (inc emptyset u) -> F <> emptyset -> with_F u = u +s1 F).
  move=> u une Fne; apply: setC1_eq => /setU1_P; case; fprops.
have oe: (sub o E) by move=> t /set3_P;case => ->.
have wfp: (forall u, partition_s u o -> partition_s (with_F u) E). 
  move=> u [[p1 p3] p2]; split; last by move=> a /setC1_P  [_] /nonemptyP.
  split.
    set_extens t.
      move /setU_P=> [a ta]; case/setC1_P; case /setU1_P => h _. 
         apply: oe; rewrite -p1; union_tac.
       by move: ta; rewrite h => /setC_P [].
      move=> tE; case: (inc_or_not t o).
        rewrite -p1 => /setU_P [v tv vu]; apply /setU_P; exists v =>//.
        apply /setC1_P;split; first by apply /setU1_P; left. 
        move=> ve;empty_tac1 t.
      move => to; have tF: inc t F by apply /setC_P.
      apply /setU_P; exists F => //; apply /setC1_P;split;fprops.
      move=> Fe;empty_tac1 t.
  move=> a b /setC1_P [] /setU1_P; case=> aa ane.
    move /setC1_P => [] /setU1_P; case=> bb bne; first by apply: p3.
    right; apply: disjoint_pr => v va vb.
    move: vb; rewrite bb => /setC_P [_]; case; rewrite -p1; union_tac.
  move /setC1_P => [] /setU1_P; case => bb bn; last by rewrite aa; left.
  right; apply: disjoint_pr => v vb va.
  move: vb; rewrite aa => /setC_P [_]; case; rewrite -p1; union_tac.
pose pa3 a b c := doubleton (singleton a) (doubleton b c).
have pa3p: (forall a b c, (singleton a) \cup (doubleton b c) = o ->
  partition_s (pa3 a b c) o).
  move => a b c H; split; last first.
    move=> u  /set2_P; case=> ->; [apply: set1_ne |  apply: set2_ne].
  have H1: disjoint (singleton a) (doubleton b c).
    apply: disjoint_pr => u /set1_P eq1; move: H; rewrite eq1 => e1 e2.
    have: sub o (doubleton b c).
      by rewrite - e1 => t /setU2_P; case => // /set1_P ->.
    move/sub_smaller; rewrite (cardinal_tripleton xy xz yz) => ha. 
    case: (cleNgt (cleT ha (cardinal_doubleton b c)) (cltS NS2)).
  split => // u v /set2_P [] -> /set2_P [] ->; try (by left); right => //.
  by apply: disjoint_S.
set (Px:= with_F (pa3 x y z)). 
set (Py:= with_F (pa3 y x z)). 
set (Pz:= with_F (pa3 z x y)). 
have pox: partition_s (pa3 x y z) o.
  apply: pa3p;rewrite setU2_C. 
  set_extens t;case/set3_P => ->; apply/set3_P; in_TP4.
have poy: partition_s (pa3 y x z) o.
  apply: pa3p; rewrite setU2_C.
  set_extens t;case/set3_P => ->; apply/set3_P; in_TP4.
have poz: partition_s (pa3 z x y) o by apply: pa3p; rewrite setU2_C. 
have ppx: partition_s Px E by apply: wfp; apply: pox.
have ppy: partition_s Py E by apply: wfp; apply: poy.
have ppz: partition_s Pz E by apply: wfp; apply: poz.
move: (coarser_osr E)  => [oce pb].
have auxP: forall u, inc u (substrate (coarser E)) <-> partition_s u E.
  by move=> u; rewrite pb; apply: partitionsP. 
have Pxr: inc Px (substrate (coarser E)) by apply/auxP. 
have Pyr: inc Py (substrate (coarser E)) by apply/auxP.
have Pzr: inc Pz (substrate (coarser E)) by apply/auxP.
set (alpha:= with_F(greatest_partition o)).
set (omga:= with_F(least_partition o)).
have ppa: (partition_s alpha E) by apply: wfp; apply: greatest_is_partition.
have ppo: (partition_s omga E).
  by apply: wfp; apply: least_is_partition; exists z. 
have lr: lattice (coarser E).
  move: (Exercise1_18a E) => [cl1 cl2].
  by split => // u v uE vE;apply:cl2; move=> t /set2_P [] ->.
have or: order (coarser E) by move: lr => [ok _].
move=> bad; move: (bad Px Py Pz Pxr Pyr Pzr).
have one: o <> emptyset by move => h; empty_tac1 z.
have op1:forall u, partition_s u o -> gle (coarser E) omga (with_F u).
  move=> u pu; apply /coarser_gleP; split;fprops.
  move=> a /setC1_P [] /setU1_P; case => h ae.
    exists o => //. 
      by apply /setC1_P; split => //; apply /setU1_P; left; apply/set1_P.
    by move: pu => [[pu1 pu3] pu2]; rewrite -pu1; apply: setU_s1.
  exists a;fprops; apply /setC1_P;split => //;rewrite h; fprops.
have oPx: gle (coarser E) omga Px by apply: op1.
have oPy: gle (coarser E) omga Py by apply: op1.
have oPz: gle (coarser E) omga Pz by apply: op1.
have Hb: forall u v, doubleton u v <> emptyset by move => u uv h; empty_tac1 u.
have ->: (inf (coarser E) Py Pz = omga).
  move: (lattice_inf_pr lr Pyr Pzr) => [e1 e2 e3].
  move: (arg1_sr e1) => /auxP infp.
  move: e1 => /coarser_gleP [_ _ cc].
  have d1Py: inc (doubleton x z) Py.
    by apply /setC1_P;split; fprops;apply /setU1_P; left; apply /set2_P; right.
  move: e2 (cc _ d1Py)=> /coarser_gleP [_ _ cc2] [s1 p1 p2].
  have d2Py: inc (doubleton x y) Pz.
    by apply /setC1_P;split;fprops; apply /setU1_P; left; apply /set2_P; right.
  move: (cc2 _ d2Py)=> [s2 p3 p4].
  case: (proj2 (proj1 infp) _ _ p1 p3) => s1s2;last by empty_tac1 x.
  apply: (order_antisymmetry or); last by apply: e3.
  apply /coarser_gleP; split => // a.
  move /setC1_P => [] /setU1_P [] /set1_P p5 p6.
    rewrite p5;ex_tac => t;case/set3_P => ->; first by apply: p4; fprops.
        by apply p4; fprops. 
     by rewrite - s1s2; apply p2; fprops.
  move: p6; move /set1_P: p5 => -> p6.
  have FPy: inc F Py by apply /setC1_P;split => //; apply /setU1_P; right.
  move: (cc _ FPy)=> [s3 p7 p8]; ex_tac.
rewrite sup_C  (sup_comparable1 or oPx).
suff p3: forall a b, doubleton a b = doubleton y z ->
    (sup (coarser E) Px  (with_F (pa3 a x b)) = alpha).
  rewrite /Py/Pz p3 // p3; last by apply: set2_C.
  rewrite (inf_comparable1 or); last (by order_tac; apply/auxP); move => pa.
  have: inc (singleton y) alpha.
    by apply/setC1_P; split;fprops; apply /setU1_P;left; apply /funI_P;exists y.
  rewrite -pa; move /setC1_P => [] /setU1_P; case.
     move /set2_P; case =>h; first by move: (set1_inj h) => h1; case: xy.
    have /set1_P /(nesym yz) //: inc z (singleton y) by rewrite h; fprops.
  by move=> yF; move: (set1_1 y); rewrite yF; move /setC_P => [_]; case.
move=> a b da.
have ax: a <> x.
  by  move=> ax; move: (set2_1 a b); rewrite da ax;case /set2_P.
have bx: b <> x.
  by move=> bx; move: (set2_2 a b); rewrite da bx; case/set2_P. 
have ab: a <> b.
    move=> ab; move: (set2_2 y z)(set2_1 y z).
    by rewrite -da ab => /set1_P <- /set1_P.
have ao: inc a o by move: (set2_1 a b); rewrite da; case/set2_P =>->. 
have bo: inc b o by move: (set2_2 a b); rewrite da; case/set2_P =>->.
set Pt:= with_F (pa3 a x b).
have Ptsw: (Pt = Py \/ Pt = Pz).
  rewrite /Py /Pz /Pt.
  by case: (doubleton_inj da); move => [av bv]; rewrite av bv; [left | right].
rewrite intersection_is_sup2_b //; last by case: Ptsw => ->.
have fg1: fgraph (Lg o singleton) by fprops.
have in1: forall a b, (doubleton a b) \cap (singleton a) = singleton a.
  move=> A B; set_extens t; first by move /setI2_P => [].
  move => h; apply /setI2_P;split => //; move /set1_P: h => ->; fprops.
have in2:(doubleton a b) \cap (doubleton x b) = singleton b.
  set_extens s.
    by move => /setI2_P []; case/set2_P => ->; fprops; case/set2_P.
  move /set1_P => ->; apply /setI2_P; split; fprops.
set_extens t. 
  move /Zo_P => [] /setI_covering2_P [u [v [u1 v1 i1]]] /set1_P net.
  apply /setC1_P; split => //.
  move/nonemptyP : net; rewrite -i1; move=> [w] /setI2_P [wu wv].
  move: u1 v1 => /setC1_P  [p1 p2] /setC1_P [p3 p4].
  case /setU1_P: p1.
  - case /set2_P => p5; case /setU1_P: p3; first case /set2_P => p6. 
     + by case: ax; move: wu wv; rewrite p5 p6 => /set1_P -> /set1_P ->.
     + by apply /setU1_P; left; apply /funI_P; exists x=> //;
        rewrite p5 p6 setI2_C in1.
     + by move => vF;case: xnF; move: wu wv; rewrite p5 vF; move => /set1_P ->.
  - case/set2_P => p6.
    + by rewrite p5 p6 -da in1; apply /setU1_P; left; apply /funI_P; exists a.
    + by rewrite p5 p6 -da in2; apply /setU1_P; left; apply /funI_P; exists b.
    + by move => vF; move: wu wv; rewrite vF p5;
      case/set2_P => ->  h; [ by case: ynF | by case: znF ].
  - move => uF; case/setU1_P: p3; first case/set2_P => h.
    + move:wv wu; rewrite h uF => /set1_P.
      move: (set2_1 a b); rewrite da;
        case/set2_P => -> -> h1; [ by case: ynF | by case: znF ].
    + move: wv wu; rewrite h uF; case/set2_P; first by move => -> h2; case: xnF.
      move: (set2_2 a b); rewrite da;
        case/set2_P => -> -> h1; [ by case: ynF | by case: znF ].
    + by move=> ->; apply /setU1_P;right; rewrite uF; rewrite setI2_id.
move => /setC1_P [pa pb']; apply/setC1_P; split => //.
apply /setI_covering2_P. 
case/setU1_P: pa; last first.
  move=> tf ; exists t, t; rewrite setI2_id;split => //;
  apply /setC1_P;split => //; apply /setU1_P; right; ue.
move /funI_P => [c co] => tC.
set C1 := (((pa3 x y z) +s1 F) -s1 emptyset).
set C2 := (((pa3 a x b) +s1 F) -s1 emptyset).
have xc1: inc (singleton x) C1.
   apply /setC1_P;split; first (apply /setU1_P; left; apply /set2_P);fprops.
   have ac2: inc (singleton a) C2.
   apply /setC1_P;split; first (apply /setU1_P; left; apply /set2_P);fprops.
have bx2: inc (doubleton x b) C2.
   apply /setC1_P;split; first (apply /setU1_P; left; apply /set2_P);fprops.
have ab2: inc (doubleton a b) C1.
   apply /setC1_P;split; first (apply /setU1_P; left; apply /set2_P);fprops.
have cxab: (c = x \/ (c = a \/ c = b)).
  move: co  =>/set3_P; case; first (by fprops); move => -> ;right.
    by move: (set2_1 y z); rewrite -da; move /set2_P.
  by move: (set2_2 y z); rewrite -da; move /set2_P.
rewrite tC;case: cxab.
  move=> ->;exists (singleton x), (doubleton x b); split => //.  
  by rewrite setI2_C in1.  
case=> ->.
  by exists  (doubleton a b), (singleton a).
by exists (doubleton a b), (doubleton x b).
Qed.


(** The set is relatively complemented *)

Lemma Exercise1_18c E:
  greatest_partition E =  the_greatest (coarser E).
Proof. 
move: (coarser_osr E)  => [pa pb].
symmetry; apply: the_greatest_pr2 => //.
have p1: partition_s (greatest_partition E) E by apply: greatest_is_partition.
red; rewrite pb; split; first by apply /partitionsP.
move=> x => /partitionsP xE. 
apply /coarser_gleP;split => // y.
move /funI_P =>  [w wE ->]. 
rewrite -(proj1 (proj1 xE)) in wE; move:(setU_hi wE) => [z wz zx].
by ex_tac; move=> t /set1_P ->.
Qed.

Lemma Exercise1_18d E X Y (r := coarser E):
  gle r Y X -> exists X',
  [/\ inc X' (substrate r), inf r X X' = Y & sup r X X' = greatest_partition E].
Proof. 
move=> lYX; move: (lYX).
move /coarser_gleP => [py px cyx].
move: (px)(py) => [[px1 px3] px2] [[py1 py3] py2].
set (X1 := Zo (\Po E) (fun z=> exists2 a, z = singleton a &
    ~(exists2 u, inc u X & a = rep u))).
set X2 := fun_image Y (fun v => Zo E
    (fun z => exists u, [/\ inc u X, sub u v & z = rep u])).
set (Z:=X1 \cup X2).
have Hb: forall x a, inc x a-> inc a X -> x <> (rep a) -> inc (singleton x) Z.
  move=>x a xa aX nrep; apply /setU2_1.
  apply: Zo_i; first by apply /setP_P => w /set1_P ->; rewrite -px1;union_tac.
  exists x => //; move=> [w wx tr].
  have xw: (inc x w) by rewrite tr; apply: rep_i; apply: px2.
  case: (px3 _ _ aX wx) => aw; first by case: nrep; ue. 
  by red in aw; empty_tac1 x.
have pz: (partition_s Z E). 
  split; last first.
    move=> a; case/setU2_P.
      move /Zo_P => [_ [u ua _]];rewrite ua; exists u; fprops.
    move /funI_P => [v vy ->]; move: (py2 _ vy) => [x xv].
    have : inc x E by rewrite -py1; union_tac.
    rewrite -px1; move=> /setU_P [u xu uX].
    move: (rep_i (px2 _ uX)) (cyx _ uX) => ru [w wY uW].
    case: (py3 _ _ vy wY) => vw; last by empty_tac1 x.
    exists (rep u); apply: Zo_i; [ union_tac | exists u;split => //; ue].
  split; first set_extens x.
      move=> /setU_P [u xu]; case/setU2_P.
        by move /Zo_P => [] /setP_P uE _; apply: uE.
      by move=> /funI_P [v vy vw];move: xu; rewrite vw => /Zo_P [te _].
    move=> xE;move: (xE); rewrite -px1=> /setU_P [a xa aX]; apply /setU_P.
    case: (equal_or_not x (rep a)) => xrep; last first.
      exists (singleton x); fprops; apply: (Hb _ _ xa aX xrep). 
    move: (cyx _ aX)=> [b bY ab]. 
    set (w:= Zo E (fun z => exists u, [/\ inc u X, sub u b & z = rep u])).
    have tw: (inc x w) by apply: Zo_i => //; exists a.
    by exists w => //; apply: setU2_2; apply /funI_P; exists b. 
  move=> a b; case/setU2_P=> h1; case/setU2_P => h2.
  + move: h1 h2 => /Zo_hi [u au _] /Zo_hi [v bv _].
    rewrite au bv; case: (equal_or_not u v) => uv; first by left;ue.
    by right; apply: disjoint_pr; move=> w /set1_P -> /set1_P. 
  + move: h1 h2 =>  /Zo_P [aE [x ax nev]] /funI_P [z zY bv].
    right; apply: disjoint_pr => u; rewrite ax bv => /set1_P ->.
    move /Zo_P => [xE [w [wX wz rw]]]; case: nev; ex_tac.
  + move: h2 h1 => /Zo_P [aE [x ax nev]] /funI_P [z zY bv].
    right; apply: disjoint_pr => u; rewrite ax bv.
    move /Zo_P=> [xE [w [wX wz rw]]] /set1_P => h;case: nev; ex_tac; ue.
  + move: h1 h2 => /funI_P [x xY av] /funI_P [y yY bv]. 
    rewrite av bv.
    case: (py3 _ _ xY yY); first by move=> xy; left; rewrite xy.
    rewrite {1} /disjoint;move=> dixy; right; apply: disjoint_pr. 
    move=> u => /Zo_P [uE [c [cX cx ur]]] /Zo_P [_ [d [dX dx ur']]].
    move: (rep_i (px2 _ cX))(rep_i (px2 _ dX)). 
    rewrite -ur -ur' => uc ud; empty_tac1 u. 
have lr: lattice (coarser E).
  move: (Exercise1_18a E) => [cl1 cl2].
  by split => // u v uE vE;apply: cl2; move=> t; case/set2_P => ->.
move: (coarser_osr E) => [or sr].
have auxP: forall u, inc u (substrate r) <-> partition_s u E.
  by move=> u; rewrite sr; apply: partitionsP. 
have Xs: inc X (substrate r) by apply /auxP.
have Ys: inc Y (substrate r) by apply /auxP.
have Zs: inc Z (substrate r) by apply /auxP.
exists Z; split; first by exact.
  move: (lattice_inf_pr lr Xs Zs); rewrite -/r; move => [i1 i2 i3].
  have YZ: gle r Y Z.
    apply /coarser_gleP; split => // t /setU2_P; case.
      move=> /Zo_P [] /setP_P tE [a ta ap].
      have: inc a E by apply: tE; rewrite ta; fprops.
      rewrite -py1 => /setU_P  [y ay yY].
      by exists y => //; rewrite ta; apply: set1_sub.
    move=> /funI_P [z zY tv]; ex_tac;rewrite tv; move=> u /Zo_P.
    move => [uE [v [vX vz ur]]]; apply: vz; rewrite ur. 
    apply: (rep_i (px2 _ vX)).
  move: (i3 _ lYX YZ) => Yi.
  apply: (order_antisymmetry or); last by exact.
  move: i1 i2 => /coarser_gleP [p1 _ le1] /coarser_gleP [_ _ le2].
  apply/coarser_gleP;split => // a aY.
  set (z:= Zo E (fun z => exists u, [/\ inc u X, sub u a & z = rep u])).
  have zz: (inc z Z) by apply: setU2_2; apply /funI_P; ex_tac. 
  move: (le2 _ zz) => [b bi zb]; ex_tac => t ta.
  have tE: (inc t E) by rewrite -py1; union_tac. 
  move: (tE);rewrite -px1 => /setU_P [c tc cX].
  move: (cyx _ cX) => [d dY cd].
  case: (py3 _ _ aY dY) => ad; last by empty_tac1 t.
  rewrite -ad in cd; clear dY ad d.
  move: (rep_i (px2 _ cX)) => rd1.
  have rcb: inc (rep c) b. 
    by apply: zb; apply: Zo_i; [rewrite  -px1;union_tac | ex_tac].
  move: (le1 _ cX) => [d di db].
  case: (proj2 (proj1 p1)  _ _ bi di); first by move=> ->; apply: db.
  move => bd; empty_tac1 (rep c).
rewrite intersection_is_sup2_b //.
have Ha: forall a w, inc a X -> inc w X2 -> nonempty (a \cap w) ->
  a \cap w = (singleton (rep a)). 
  move=> a b aX /funI_P [v vY bv] [q qt].
  apply: set1_pr1; first by ex_tac.
  rewrite bv => w /setI2_P [wa]/Zo_P [wE [c [cX cb wr]]].
  case: (px3 _ _ aX cX); first by move=> ->.
  move=> di; empty_tac1 (rep c); [ ue | apply: (rep_i (px2 _ cX))].
set_extens t.
  move /setC1_P => [] /setI_covering2_P [a [b [aX bZ ti]]] /nonemptyP net. 
  apply /funI_P; case/setU2_P: bZ.
    move /Zo_P=>[bE [c bs _]].
    have cb: inc c b by rewrite bs; fprops.
    move/setP_P : bE => bE; move: (bE _ cb) => cE; ex_tac.
    by apply: (set1_pr1 net); rewrite - ti bs => u /setI2_P [_] /set1_P.  
  rewrite -ti in net;move => bX2; move: (Ha _ _ aX bX2 net) => wi.
  rewrite -ti wi -px1; exists (rep a)=> //; apply: (@setU_i _ a) => //.
  apply: (rep_i (px2 _ aX)).
move /funI_P => [x xE st].
apply/setC1_P; split; last by rewrite st; apply /nonemptyP/set1_ne.
apply /setI_covering2_P.
move: (xE); rewrite -px1 => /setU_P [a wa aX].
move: (cyx _ aX) => [b bY ab].
case: (equal_or_not x (rep a)) => ra.
  set (w:= Zo E (fun z  => exists u, [/\ inc u X, sub u b & z = rep u])).
  have wX2: inc w X2 by apply /funI_P; ex_tac.
  have nei: nonempty (a \cap w). 
    exists (rep a); apply: setI2_i; first by ue. 
    apply: Zo_i; [rewrite -px1 -ra; union_tac | ex_tac].
  exists a, w;rewrite (Ha _ _ aX wX2 nei) -ra st;split => //.
  by apply: setU2_2.
exists a, (singleton x); split => //; first by apply: (Hb _ _ wa aX ra).
rewrite st setI2_C; apply: set1_pr. 
  by apply /setI2_P;split;fprops.
by move => z /setI2_P  [] /set1_P.
Qed.

(** ----  Exercise 1.19  Sets without gaps; example of ordinal sum *)

Definition without_gaps r :=
  [/\ order r, (exists x y, glt r x y) &
  (forall x y, glt r x y -> exists2 z, glt r x z & glt r z y)].


Section  Exercise1_19.
Variables (r g: Set).
Hypotheses  (ax:orsum_ax r g) (ax2: orsum_ax2 g).

Lemma Exercise1_19a:
  without_gaps (order_sum r  g) <->
    [/\ (exists i j, glt r i j) \/
        (exists i x y, inc i (substrate r) /\ glt (Vg g i) x y),
    (forall i x y, inc i (substrate r) ->  glt (Vg g i) x y ->
      without_gaps (Vg g i))
    & (forall i j, glt r i j ->
      [\/ (exists2 k, glt r i k & glt r k j),
        (forall u, ~ (maximal (Vg g i) u)) |
        (forall u, ~ (minimal (Vg g j) u))])].
Proof. 
move: (ax) => [q1 q2 q4];split.
  move=>[or [x1 [y1 x1y1]] wg]; split.
  + move: x1y1 => [] /orsum_gleP [p1 p2 p3] di.
    case: p3; first by move=> h; left; exists (Q x1), (Q y1).
    move=> [sq1 cp]; right; exists (Q x1); exists (P x1), (P y1).
    move: (du_index_pr1 p1) (du_index_pr1 p2) => [a1 a2 a3][a4 a5 a6].
    by rewrite q2; split => //; split => // ; dneg sq; apply: pair_exten.
  + move => i x y isr lt1; split => //; first by apply: q4; ue.
      by exists x, y.   
    move=> u v [leuv neuv].
    rewrite q2 in isr.
    have lt2: (glt (order_sum r g) (J u i) (J v i)).  
      split; last by dneg sj; apply: (pr1_def sj).
      apply /orsum_gleP; split => //; last (by right; aw);
          apply: disjoint_union_pi1=>//; order_tac. 
    move: (wg _ _ lt2) => [z [zl1 zne1] [zl2 zne2]].
    move: (orsum_gle_id ax zl1)(orsum_gle_id ax zl2); aw => lea leb.
    move: (order_antisymmetry q1 lea leb) => lec.
    move: zl1 zl2 => /orsum_gleP [_  zs zl1] /orsum_gleP [_ _ zl2].
    move:  (du_index_pr1 zs)=> [a1 a2 a3].
    exists (P z); rewrite /glt;split => //.
    - by case: zl1;case; aw; rewrite - lec.
    - move=> upz; case: zne1; apply: pair_exten; aww. 
    - by case: zl2;case; rewrite - lec; aw. 
    - move=> upz; case: zne2; apply: pair_exten; aww.
  + move=> i j ij.
    case: (p_or_not_p (exists u, maximal (Vg g i) u)); last first.
      by move => bad; constructor 2 => u mu; case: bad; exists u.
    case: (p_or_not_p (exists v, minimal (Vg g j) v)); last first.
      by move => bad _; constructor 3 => v mu; case: bad; exists v.
    move => [v [vs vm]] [u [us um]].
    have idf: (inc i (domain g)) by rewrite -q2; order_tac.
    have jdf: (inc j (domain g)) by rewrite -q2; order_tac.
    have J1: (inc (J u i) (sum_of_substrates g)) by apply: disjoint_union_pi1. 
    have J2: (inc (J v j) (sum_of_substrates g)) by apply: disjoint_union_pi1. 
    have l1: (glt (order_sum r  g) (J u i) (J v j)). 
      split; first by apply/orsum_gleP; split => //; left; aw.
      move=> sj; move: ij => [_];  case; apply: (pr2_def sj).
    move: (wg _ _ l1) => [z [z1 z2] [z3 z4]].
    move: z1 z3 =>/orsum_gleP [_ zs z5] /orsum_gleP [_ _ z6].
    move:  (du_index_pr1 zs)=> [a1 a2 a3].
    case: z5; rewrite pr2_pair => a4.
      case: z6; rewrite pr2_pair => a5; first by constructor 1; exists (Q z).
      move: a5 => [Qa]; rewrite pr1_pair Qa => Pa.
      move: (vm _ Pa) => pz; case: z4; apply: pair_exten; aww.
    move: a4 => [Qa]; rewrite pr1_pair => Pa.
    move: (um _ Pa) => pz; case: z2; apply:  pair_exten; aww.
move=> [CI CII CIII].
have os: order (order_sum r g) by fprops.
split => //.
  case: CI. 
    move=> [i [j ij]].
    have idf: (inc i (domain g)) by rewrite -q2; order_tac.
    have jdf: (inc j (domain g)) by rewrite -q2; order_tac.
    move: (ax2 idf)(ax2 jdf) => [u us] [v vs].
    have J1: (inc (J u i) (sum_of_substrates g)) by apply: disjoint_union_pi1. 
    have J2: (inc (J v j) (sum_of_substrates g)) by apply: disjoint_union_pi1. 
    have l1: (glt (order_sum r  g) (J u i) (J v j)). 
      split; first by apply /orsum_gleP; split => //; left; aw. 
      move=> sj; case: (proj2 ij); apply: (pr2_def sj).
    by exists (J u i); exists (J v j).
  move=> [i [u [v [isr [leij neij]]]]].
  rewrite q2 in isr; move: (q4 _ isr) => oi.
  exists (J u i); exists (J v i);split; last by dneg sj; apply: (pr1_def sj). 
  apply /orsum_gleP; split => //; last (by right; aw);
    apply: disjoint_union_pi1 => //; order_tac.
move=> x y [lexy nexy]; move: lexy => /orsum_gleP //.
move=> [xsr ysr lexy].
move: (du_index_pr1 xsr) (du_index_pr1 ysr)=> [a1 a2 a3][a4 a5 a6].
case: lexy => lea.
  case: (CIII _ _ lea).
  + move=> [k k1 k2].
    have ksr: (inc k (domain g)) by rewrite -q2; order_tac.
    move: (ax2 ksr) => [z zs].
    have J1: (inc (J z k) (sum_of_substrates g)) by apply: disjoint_union_pi1.
    have xn: x <> J z k by move: k1 =>[_ Qx]; dneg xj;rewrite xj; aw.
    have yn: J z k <> y by move: k2 =>[_ Qx]; dneg xj;rewrite - xj; aw.
    by exists (J z k); split => //; apply /orsum_gleP; split => //; left; aw.
  + move => nmm; move: (nmm (P x));  rewrite /maximal => nm.
    have [z zs pz]: 
      (exists2 z, inc z (substrate (Vg g (Q x))) & glt (Vg g (Q x)) (P x) z).
      ex_middle ww; case: nm; split => // z z1.
      case:(equal_or_not (P x) z) => // pzx; case: ww; exists z => //;order_tac.
    have J1:inc (J z (Q x)) (sum_of_substrates g) by apply: disjoint_union_pi1.
    have xn: x <> J z (Q x) by move: pz =>[_ Qx]; dneg xj;rewrite xj; aw.
    have yn: J z (Q x) <> y by move: lea =>[_ Qx]; dneg xj;rewrite - xj; aw.
    exists (J z (Q x)); split => //; apply /orsum_gleP;split => //. 
      by right; aw; move: pz => [pz _].
    by left; aw.
  + move => nmm;move: (nmm (P y)); rewrite /minimal => nm.
    have [z zs pz]: 
      (exists2 z, inc z (substrate (Vg g (Q y))) & glt (Vg g (Q y)) z (P y)).
      ex_middle ww; case: nm;split => // z zl.
      case: (equal_or_not z (P y)) => // pzx; case: ww;exists z => //;order_tac.
    have J1: inc (J z (Q y)) (sum_of_substrates g) by apply: disjoint_union_pi1.
    have xn: x <> J z (Q y) by move: lea =>[_ Qx]; dneg xj;rewrite xj; aw.
    have yn: J z (Q y) <> y by move: pz =>[_ Qx]; dneg xj;rewrite - xj; aw.
    exists (J z (Q y)); split => //; apply /orsum_gleP; split => //. 
      by left; aw.
    by right; aw; move: pz => [pz _].
move: lea => [qxy sv].
have lv1: (glt (Vg g (Q x)) (P x) (P y)).
  by split=>//; dneg h; apply: pair_exten.
have qsr: (inc (Q x) (substrate r)) by ue.  
move: (CII _ _ _ qsr lv1) => [w1 w2 w3].
move: (w3 _ _ lv1) => [z [z1 z2] [z3 z4]].
have zs: inc z (substrate (Vg g (Q x))) by order_tac.
have J1: inc (J z (Q x)) (sum_of_substrates g) by apply: disjoint_union_pi1.
have xn: x <> J z (Q x) by move=> xe; case: z2;rewrite xe; aw.
have yn: J z (Q x) <> y by move=> xe; case: z4;rewrite - xe; aw.
by exists (J z (Q x)); split => //;apply /orsum_gleP; split => //;right; aw.
Qed.


Lemma Exercise1_19b:
  ne_substrate r ->
  (forall i u, ~ (maximal (Vg g i) u)) ->
  (forall i, inc i (substrate r) -> without_gaps (Vg g i)) ->
  without_gaps (order_sum r g).
Proof. 
move =>  [y yE] nm wg.
apply /Exercise1_19a;split => //.
    right; move: (wg _ yE)=> [_ [a [b ab]] _].
    by exists y, a, b.
  by move => i c z h _; apply: wg.
move=> i j ij; constructor 2; apply: nm.
Qed.

Lemma Exercise1_19c:
  ne_substrate r ->
  (forall i u, ~ (minimal (Vg g i) u)) ->
  (forall i, inc i (substrate r) -> without_gaps (Vg g i)) ->
  without_gaps (order_sum r g).
Proof.
move => [y yE] nm wg.
apply /Exercise1_19a;split => //.
+ by right; move: (wg _ yE)=> [_ [a [b ab]] _];  exists y, a, b.
+ by move => i c z h _; apply: wg.
+ move=> i j ij; constructor 3; apply: nm.
Qed.

Lemma Exercise1_19d:
  without_gaps r ->
  (forall i, inc i (substrate r) ->  
      (without_gaps (Vg g i) \/
        (forall x y, inc x (substrate (Vg g i)) -> inc y (substrate (Vg g i))
            -> ~ (glt (Vg g i) x y))))
    ->  without_gaps (order_sum r g).
Proof.
move => [_ q1 q2] wg.
apply/Exercise1_19a=> //; split; fprops; last first.
  by move => i j /q2 h; constructor 1.
move=> i u v isr luv; case: (wg _ isr) => // h.
have  p1:inc u (substrate (Vg g i)) by order_tac.
have  p2:inc v (substrate (Vg g i)) by order_tac.
by case: (h _ _ p1 p2).
Qed.

End  Exercise1_19.

(** ---- Exercise 1.20  Scattered sets*)

Definition scattered r := order r /\
  (forall x, sub x (substrate r) -> ~ (without_gaps (induced_order r x))).

Lemma Exercise1_20a r x: 
  sub x (substrate r) -> scattered r -> scattered (induced_order r x).
Proof. 
move=> xsr [or sc]; move: (iorder_osr or xsr) => [pa pb].
split => // y; rewrite pb => yx.
by rewrite  iorder_trans //; apply: sc; apply: (sub_trans yx).
Qed.

Lemma Exercise1_20b r: worder r -> scattered r.
Proof. 
move=> wor;split; first by  move: (wor) => [or _].
move=> z zsr.
have : (worder (induced_order r z)) by apply: induced_wor.
set (y:= induced_order r z).  
move=> woy [_ [a [b ab] yy]].
have asr: (inc a (substrate y)) by order_tac.
set F := Zo (substrate y) (glt y a).
have zs: (sub F (substrate y)) by apply: Zo_S.
have bF: (inc b F) by apply/Zo_P; split => //; order_tac.
have neF: (nonempty F) by exists b.
move: woy => [oy woy].
move: (woy _ zs neF) => [d []]; rewrite iorder_sr // => /Zo_P [dd dle] dp.
move: (yy _ _ dle)=> [e [e1 ne1] e2].
have eF: inc e F by apply/Zo_P; split => //; order_tac.
move: (iorder_gle1 (dp _ eF)) => h; order_tac.
Qed.

(** any scattered set satisfies the following property; the convetse is false *)

Definition Exercise1_20_prop r:=
forall x y, glt r x y ->
  exists x' y', 
   [/\ gle r x x', glt r x' y',  gle r y' y &
    (forall z, ~ (glt r x' z /\ glt r z y'))].

Lemma Exercise1_20c r:
  scattered r -> Exercise1_20_prop r.
Proof. 
move=> [or sc] x y xy.
set (F:= interval_cc r x y).  
have Fs: (sub F (substrate r)) by apply: Zo_S. 
move: (iorder_osr or Fs)=> [or1 sr1].
move: (sc _ Fs) => nw; ex_middle bad; case: nw;split => //.
  have xsr: inc x (substrate r) by order_tac.
  have ysr: inc y (substrate r) by order_tac.
  exists x, y; move: xy => [xy nxy]; split; last by exact.
  by apply /iorder_gle0P => //;  apply: Zo_i =>//; split => //; order_tac.
move => a b ab.
have ab2: (glt r a b) by apply: (iorder_gle2 ab). 
move: (iorder_gle4 ab) => [aF bF].
move: (iorder_gle4 ab) => [] /Zo_hi [xa _] /Zo_hi [_ lby].
ex_middle bad1; case: bad;exists a,b;split => //  z [[az anz] [bz bnz0]].
have zF: inc z F by apply: Zo_i; [ order_tac | split => //; order_tac].
by case: bad1; exists z; split => //;apply /iorder_gleP.
Qed.

Definition cantor_tri_aux := cst_graph Nat canonical_doubleton_order.
Definition cantor_tri_order:= order_prod Nat_order cantor_tri_aux.
Definition cantor_tri_sub:= productb (cst_graph Nat C2).

Lemma cantor_tri_order_axioms: orprod_ax Nat_order cantor_tri_aux.
Proof. 
rewrite/cantor_tri_aux;move : Nat_order_wor => [pa pb].
split=> //;hnf;aw;trivial=> i ib ; rewrite !LgV//.
by move: cdo_wor => [[ok _] _].
Qed.

Lemma cantor_tri_order_total : total_order cantor_tri_order.
Proof.
rewrite /cantor_tri_order/cantor_tri_aux; apply: orprod_total.
  by apply: cantor_tri_order_axioms. 
red; aw => i iN; rewrite !LgV//; apply: (worder_total (proj1 cdo_wor)).
Qed.

Lemma cantor_tri_order_sr1 :
  prod_of_substrates cantor_tri_aux =  cantor_tri_sub.
Proof.
congr (productb);rewrite  /fam_of_substrates /cantor_tri_aux; aw.
apply: Lg_exten; move=> x xN /=; rewrite LgV//; exact: (proj2 cdo_wor). 
Qed.

Lemma cantor_tri_order_sr :
 substrate cantor_tri_order = cantor_tri_sub.
Proof.
rewrite /cantor_tri_order orprod_sr.
  apply:  cantor_tri_order_sr1.
apply: cantor_tri_order_axioms.
Qed.

Lemma cantor_tri_order_gltP x x':
  glt cantor_tri_order x x' <->
  [/\ inc x cantor_tri_sub,  inc x' cantor_tri_sub &
    exists j, [/\  natp j,
      (forall i, natp i -> i <c  j -> Vg x i = Vg x' i),
      Vg x j = C0 & Vg x' j = C1]].
Proof.
rewrite /cantor_tri_order.
set r := Nat_order;set g := cantor_tri_aux.
have op: orprod_ax r g by apply: cantor_tri_order_axioms.
have sr: substrate r = Nat by rewrite /r (proj2 Nat_order_wor).
have rvP: forall j, natp j -> forall u v,
  (glt (Vg g j) (Vg u j) (Vg v j) <-> (Vg u j = C0 /\ Vg v j = C1)).
  move=> j jN u v; rewrite /g/cantor_tri_aux LgV// /glt; split.
    by move => [] /cdo_gleP h1; case: h1 => // [][-> ->]. 
  move=> [ -> -> ]; split; [ apply /cdo_gleP; in_TP4 | fprops].
have rijP: forall i j, natp j -> (glt r i j <-> (natp i /\ i <c j)).
  move => i j jN; split;first by move => [] /Nat_order_leP [pa pb pc] pd.
  by move => [pa [pb pc]]; split => //; apply/Nat_order_leP.
split.
  move => [] /(orprod_gleP op); rewrite cantor_tri_order_sr1.
  move=> [p1 p2 p3] p4; split => //; case: p3; first by move=> aux.
  rewrite sr;move=> [j [jsr /(rvP _ jsr) [pa pb]  lt2]]. 
  by exists j;  split => // i iN ij; apply: lt2; apply / rijP. 
move=> [p1 p2 [j [jb jp1 jp2 jp3]]]; split.
  apply /(orprod_gleP op);rewrite cantor_tri_order_sr1;split => //.
  right;exists j;split => //;[ ue | by apply/rvP | ].
  move  => i  /(rijP _ _ jb)  [pa pb]; apply: (jp1 _ pa pb).
move=> uv; rewrite uv jp3 in jp2; fprops.
Qed.

Lemma  Exercise1_20d: Exercise1_20_prop cantor_tri_order.
Proof.
move=> x y.
move /cantor_tri_order_gltP => [xb yb [j [jN sj jx jy]]].
pose f i :=  Yo (i <=c j) (Vg x i) C1.
pose g i :=  Yo (i <=c j) (Vg y i) C0.
have fgPr: (fgraph (cst_graph Nat C2)) by  fprops.
move: (xb)(yb) => /setXf_P [fgx dx xVV] /setXf_P  [fgy dy yVV].
have fPr: (inc (Lg Nat f) cantor_tri_sub).
apply /setXf_P;split;aww;move=> i iN; rewrite /f LgV//.
   Ytac hle; fprops.
have gPr: (inc (Lg Nat g) cantor_tri_sub ).
  apply /setXf_P;split;aww;move=> i iN; rewrite /g LgV//.
  Ytac h; fprops.
move: cantor_tri_order_total => [co _].
pose Zab a x := Zo Nat (fun i => j <c i /\ Vg x i = a). 
have Zabp: forall a x, nonempty (Zab a x) -> exists k,
  [/\ natp k, j <c k, Vg x k = a &
  (forall i, natp i ->  i <c k -> i <=c j \/ Vg x i <> a)].
  move=> a u [v vZ].
  have ov: ordinalp v by apply /OS_nat; apply: (Zo_S vZ).
  move: (least_ordinal4 (p := fun z=> inc z (Zab a u)) ov vZ).
  set w:= least_ordinal _ _ ; move => [wa /Zo_P [wb [wc wd]] we]. 
  exists w; split => // i iN iw; case: (inc_or_not i (Zab a u)) => h.
    case: (oleNgt (we _ (OS_nat iN) h) (oclt iw)).
  case: (equal_or_not (Vg u i) a) => eq; last by right.
  by case: (NleT_el iN (NS_lt_nat wc wb))=> ji; [by left | case: h;apply: Zo_i].
have p1: gle cantor_tri_order x (Lg Nat f).
  case: (emptyset_dichot (Zab C0 x)) => Ze.
    suff: x = (Lg Nat f) by move=> <- ;order_tac;rewrite cantor_tri_order_sr.
    apply: fgraph_exten => //; aww. 
    rewrite dx; move=> i iN; rewrite /f LgV//.
    Ytac hle =>//;  move: (xVV _ iN); aw; case/C2_P => // vb.
    by empty_tac1 i; apply: Zo_i => //; split => //;case: (NleT_el iN jN).
  suff: glt cantor_tri_order x (Lg Nat f) by case.
  move:(Zabp C0 x Ze) => [k [kN jk vk lt]].
  apply /cantor_tri_order_gltP; split => //.
  exists k; split => //; last by rewrite LgV// /f (Y_false (cltNge jk)).  
  move=> i iN ik; rewrite /f LgV//. 
  Ytac hle => //; case: (lt _ iN ik)=> // va.
  move: (xVV _ iN);aw;  case/C2_P => //. 
have p2: gle cantor_tri_order (Lg Nat g) y.
  case: (emptyset_dichot (Zab C1 y)) => Ze.
    suff: y = (Lg Nat g) by move=> <- ;order_tac;rewrite cantor_tri_order_sr //.
    apply: fgraph_exten => //; aww. 
    rewrite dy; move=> i iN; rewrite /g LgV//.
    Ytac hle => //; move: (yVV _ iN); case/C2_P => // vb.
    by empty_tac1 i; apply: Zo_i => //;split => //; case: (NleT_el iN jN).
  suff: glt cantor_tri_order  (Lg Nat g) y by case.
  move:(Zabp C1 y Ze) => [k [kN jk vk lt]].
  apply /cantor_tri_order_gltP; split => //.
  exists k; split => //; last by rewrite /g LgV// (Y_false (cltNge jk)).
  move=> i iN ik; rewrite /g LgV//; Ytac ij => //.
  case: (lt _ iN ik)=> // va; move: (yVV _ iN); case/C2_P=> //. 
have jj: j <=c j by apply: cleR; fprops.
exists (Lg Nat f), (Lg Nat g); split => //.
  apply /cantor_tri_order_gltP;split => //;exists j.
  rewrite /f/g!LgV//; Ytac0; Ytac0; split => //.
  by move => i ib [ij nij]; rewrite !LgV//; Ytac0; Ytac0;apply: sj.
move=> z [] /cantor_tri_order_gltP [_ zsub [k1 [k1N k1p k1a k1b]]].
move /cantor_tri_order_gltP => [_ _ [k2 [k2N k2p k2a k2b]]].
move: k1a k2b; rewrite /f /g ! LgV//;  Ytac k1j; Ytac k2j => k1a k2b;
   try (solve [apply: C0_ne_C1; done]).
case: (NleT_el k1N k2N) => k1k2.
  have l12: k1 <c k2 by split =>//h; case: C0_ne_C1; rewrite -k1b -k2a h.
  move: (k2p _ k1N l12); rewrite /g LgV// (Y_true k1j) k1b.
  rewrite -(sj _ k1N (clt_leT l12 k2j)) k1a; fprops.
move: (k1p _ k2N k1k2); rewrite /f LgV// (Y_true k2j) k2a.
rewrite (sj _ k2N  (clt_leT k1k2 k1j)) k2b; fprops.
Qed.

Lemma  Exercise1_20e: ~ (scattered cantor_tri_order).
Proof. 
move=> ns.
set (all_a := Zo cantor_tri_sub (fun z => exists2 i, natp i & forall j,
    natp j -> i <=c j -> Vg z j = C0)).
set (F:= cantor_tri_sub -s all_a). 
have sF: (sub F cantor_tri_sub) by apply: sub_setC.
have FpP: forall a, inc a F <-> (inc a cantor_tri_sub /\
  forall i, natp i -> exists j, [/\ natp j, i <=c j & Vg a j = C1]).
  move=> a; split.
    move /setC_P => [p1 p2];split =>// i iN; ex_middle nf; case: p2.
    apply: Zo_i => //; exists i => // j jN ij; ex_middle vj; case: nf. 
      exists j; split => //.
    move: p1 => /setXf_P [_ _ aux]; move: (aux _ jN);case/C2_P  =>//.  
  move => [pa pb]; apply /setC_P;split => //; move => /Zo_P [_ [i iN h]].
  move: (pb _ iN) =>[j [p3 p4]];rewrite (h _ p3 p4); fprops.
have sf1: sub F (substrate cantor_tri_order) 
  by rewrite cantor_tri_order_sr.
move: (iorder_osr (proj1 ns) sf1) => [xa xb].
move: ns => [oc ns]; case: (ns _ sf1);split; fprops.
  set zb:= (cst_graph Nat C1). 
  set zab:= (Lg Nat (fun i => Yo (i = \0c) C0 C1)).
  have zbF: (inc zb F).
    apply /FpP; rewrite /zb; split.
      apply /setXf_P; split;aww => i iN; rewrite LgV; fprops.
    move=> i iN; exists i; split => //; fprops; rewrite LgV//. 
  have zabF: inc zab F.
    apply /FpP; rewrite /zab; split.  
       apply /setXf_P;split => //;aww => i iN; rewrite LgV//; Ytac h; fprops.
    move=> i iN; move:(NS_succ iN) => nsiN; exists (csucc i).
    split=> //; fprops; rewrite LgV// Y_false //; apply: succ_nz.
  have [lt1 ne1]: (glt cantor_tri_order zab zb).
    have zeb:= NS0.
    apply /cantor_tri_order_gltP => //;split => //.
        by move: zabF => /setC_P [].
      by move: zbF => /setC_P [].
      exists \0c; rewrite /zb /zab; split => //.
      +  move => i iN iz; case: (clt0 iz). 
      + by rewrite ! LgV//;  Ytac0.
      + by rewrite LgV.
  exists zab, zb; split => //; apply /iorder_gleP => //.
move=> f g fg.
move: (iorder_gle2 fg)(iorder_gle4 fg).
move /cantor_tri_order_gltP => [fsr gsr [j [jN sj fj gj]]][fs gs].
have scj:= NS_succ jN.
move: (gs)=>/FpP [gc ha].
move: (ha _ scj) => [k [kN kle Vk]].
move: kle;rewrite  cleSltP // => kle.
set (h:= Lg Nat (fun i=> Yo (i= k) C0 (Vg g i))). 
have hF: inc h F.
  apply /FpP; split. 
    rewrite /h;apply/setXf_P;split => //;aww=> i iN; rewrite LgV//; Ytac h0; fprops.
    by move: gc =>  /setXf_P [_ _]; apply.
  move=> i iN.
  move:(cmax_p1 (CS_nat iN) (CS_succ k)) => []; set l := cmax _ _ => sa sb.
  have lN: natp l by  apply:Gmax_E => //; apply:NS_succ.
  move: (ha _ lN) => [n [nN mn Vb]]. 
  exists n;split => //; first exact:(cleT sa mn).
  case: (equal_or_not k n) => kn; last by rewrite /h LgV//; Ytac0.
  by move:(cltS nN) (cleT sb mn); rewrite kn => sc /(cltNge sc).
have [lt1 n1]: glt cantor_tri_order f h.
  apply /cantor_tri_order_gltP; split;fprops;exists j; split => //.
    move=> i iB ij; rewrite (sj _ iB ij); rewrite /h LgV//.
    by rewrite (Y_false (proj2 (clt_ltT ij  kle))).
  by move: kle => [_ kne]; rewrite /h -gj LgV//; Ytac0.
have [lt2 n2]: glt cantor_tri_order h g.
  apply /cantor_tri_order_gltP; split => //. 
    by move: hF => /setC_P [].
  exists k; split => //; last by rewrite /h LgV//; Ytac0.
  by move=> i iB [_ iK]; rewrite /h LgV//; Ytac0.   
exists h; split => //; apply /iorder_gleP => //.
Qed.

(** when is an ordinal sum scattered *)

Lemma  Exercise1_20f r g:
  orsum_ax r g ->  orsum_ax2  g -> 
  (scattered (order_sum r g) <->
    (scattered r /\ forall i, inc i (domain g) -> scattered (Vg g i))).
Proof. 
move=> oa alne.
move: (oa) =>[or sr alg];split.
  have so := (orsum_sr oa).
  pose R i := rep (substrate (Vg g i)).
  move=> [oar sca]; split.
    split => //x xsr [] nw1 [xa [xb lab]] nw3.
    set w:= fun_image x (fun i => (J (R i) i)).
    have sw: (sub w (substrate (order_sum r g))). 
      rewrite so => t /funI_P [z zx ->].
      have zdg:inc z (domain g) by rewrite - sr; apply: xsr.
      by apply: disjoint_union_pi1 => //;  apply: rep_i; apply: alne.
    move: (iorder_osr oar sw) => [oa1 sa1].
    have p1: forall a b, glt (induced_order r x) a b ->
      glt (induced_order (order_sum r g) w) (J (R a) a) (J (R b) b).
      move=> a b ab.
      move: (iorder_gle4 ab)(iorder_gle2 ab) => [xax xbx] lab'.
      split; last by move: lab' => [_ nab] sj; move: (pr2_def sj).
      have raw: inc (J (R a) a) w by apply :funI_i. 
      have rbw: inc (J (R b) b) w by apply :funI_i.
      by apply/(iorder_gle0P _ raw rbw)/orsum_gleP; split => //; try ue;left;aw.
    case: (sca _ sw); split => //.
      by exists (J (R xa) xa);  exists (J (R xb) xb); apply: p1.
    move=> u v uv.
    move: (iorder_gle4 uv)(iorder_gle2 uv) => [uw vw] [luv nuv].
    move: (orsum_gle_id oa luv) => le1.
    move: uw vw => /funI_P  [u' u'x J1] /funI_P [v' v'x J2].
    have lt1: glt (induced_order r x) u' v'.
      move: le1; rewrite J1 J2; aw => le2.
      split; [ by apply /iorder_gleP | by  dneg uv1; rewrite J1 J2 uv1].
    move: (nw3 _ _ lt1) => [z z1 z2].
    by rewrite J1 J2; exists (J (R z) z); apply: p1.
  move=> i idg.
  move: (alg _ idg) => og.
    split => // x xsr [nw1 [xa [xb lab]] nw3].
    set (w:= fun_image x (fun u => (J u i))).
    have sw: (sub w (substrate (order_sum r g))). 
      rewrite orsum_sr // => t /funI_P [z zx ->].
      by apply: disjoint_union_pi1 => //; apply: xsr. 
    move: (iorder_osr oar sw) => [oa1 sa1].
    have p1: forall a b, glt (induced_order (Vg g i) x) a b ->
      glt (induced_order (order_sum r g) w) (J a i) (J b i).
      move=> a b ab.
      move: (iorder_gle4 ab)(iorder_gle2 ab) => [xax xbx] [lab1 lab2].
      split; last by move => sj; move: (pr1_def sj).
      have raw: inc (J a i) w by apply:funI_i.
      have rbw: inc (J b i) w by apply:funI_i.
      by apply /iorder_gle0P => //; apply/orsum_gleP; split; try ue; right;aw.
    move: (sca _ sw); case; split => //.
      by exists (J xa i);  exists (J xb i); apply: p1.
    move=> u v uv.
    move: (iorder_gle4 uv)(iorder_gle2 uv) => [uw vw] [luv nuv].
    move: uw vw =>  /funI_P [u' u'x J1] /funI_P [v' v'x J2].
    move: luv => /orsum_gleP // [_ _].
    rewrite J1 J2; aw;case; first (by aw; move=> [_]; case); aw; move=> [_ le0].
    have lt1: glt (induced_order (Vg g i) x) u' v'.
      split; [ by apply /iorder_gleP | by  dneg uv1; rewrite J1 J2 uv1].
    move: (nw3 _ _ lt1) => [z z1 z2].
    by  exists (J z i)=> //; apply: p1.
move=> [scr alsci]; split; first by fprops.
move=> x xsr.
set (ns := Zo (substrate r) (fun z => exists2 i, inc i x & z = Q i)).
set (r' := induced_order r ns).
have nss: (sub ns (substrate r)) by apply: Zo_S.
move: (iorder_osr or nss) => [or' sr'].
pose f i := Zo (substrate (Vg g i)) (fun u => inc (J u i) x).
have fp1: forall i, sub (f i) (substrate (Vg g i)) by move=> i; apply: Zo_S.
set (g' := Lg ns (fun i=> induced_order (Vg g i) (f i))).
have dr':substrate r' = domain g' by rewrite /g' Lgd.
move: alg;rewrite /order_fam /allf - sr => alg.
have svig': forall i, inc i ns -> f i = substrate (Vg g' i).
  move=> i ins; rewrite /g' LgV//.
  rewrite iorder_sr //; exact: (alg _ (nss _ ins)).
have alne' : forall i, inc i (domain g') -> nonempty (substrate (Vg g' i)).
  rewrite -dr' sr'; move=> i ins; rewrite - svig' //.
  move: ins => /Zo_P [isr [j jx Qj]]; aw. 
  rewrite orsum_sr // in xsr.
  move: (du_index_pr1 (xsr _ jx)) => [p1 p2 p3].
  by exists (P j); apply: Zo_i; rewrite Qj // p3.
have oa': orsum_ax r' g'.
  split => //; rewrite /g';hnf; aw; rewrite /g'=> i ins; rewrite LgV//.
  exact:(proj1 (iorder_osr (alg _ (nss _ ins)) (fp1 i))).
have or'': order (order_sum r' g') by fprops.
have sr'': (x =  substrate (order_sum r' g')).
  move: xsr; rewrite ! orsum_sr // => xsr.
  set_extens t. 
    move=> tx; move: (du_index_pr1 (xsr _ tx)) => [Qt Pt pt].
    have qns: inc (Q t) ns by apply: Zo_i; [ ue | ex_tac ].
    rewrite - pt; apply: disjoint_union_pi1.
      rewrite -dr' sr' //.
    by rewrite - svig' //; apply: Zo_i =>//; rewrite pt.  
  move=> ts; move:(du_index_pr1 ts) => [Qt Pt pt].
  have qns: inc (Q t) ns by  rewrite - sr' dr'.
  by move: Pt; rewrite - (svig' _ qns) => /Zo_hi; rewrite pt.
have ss': (sum_of_substrates g') = x by rewrite sr'' orsum_sr //.
have auxP: forall u v, inc u x -> inc v x ->
  (gle (order_sum r g) u v  <-> gle (order_sum r' g') u v).
  move=> u v ux vx.
  move: xsr; rewrite (orsum_sr oa) => xsr.
  move: (du_index_pr1 (xsr _ ux))=> [u1a u1b u1c]. 
  move: (du_index_pr1 (xsr _ vx))=> [v1a v1b v1c]. 
  have Quns: inc (Q u) ns  by apply: Zo_i; [ue |  exists u].
  have Qvns: inc (Q v) ns  by apply: Zo_i; [ue |  exists v].
  split; last first.
    move => /orsum_gleP [pa pb pc]; apply /orsum_gleP;split. 
        move:xsr pa; rewrite - ss';apply.
      move:xsr pb; rewrite - ss'; apply.
    case: pc; move => [h1 h2]; [ left | right];split => //.
      by move: (iorder_gle1 h1).
    by move: h2; rewrite /g' LgV// => /iorder_gle1.
  move => /orsum_gleP [pa pb pc]; apply /orsum_gleP;split; try ue.
  case: pc; move => [h1 h2]; [ left | right];split => //.
       by apply /iorder_gleP.
     rewrite /g' LgV//; apply /iorder_gle0P => //; apply: Zo_i => //;
      [ by rewrite u1c | ue| by rewrite h1 v1c].
have io: (induced_order (order_sum r g) x = (order_sum r' g')).
  have oo: (order (order_sum r g)) by fprops.
  move: (iorder_osr oo xsr) => [oo1 _].
  have o1: order (induced_order (order_sum r g) x) by fprops.
  apply: order_exten => // => u v; split => rel1.
    move: (iorder_gle3 rel1) => [ux vx].
    by move: (iorder_gle1 rel1) =>/(auxP _ _ ux vx).
  have ux: inc u x by rewrite sr'' ; order_tac.
  have vx: inc v x by rewrite sr''; order_tac.
  by apply /iorder_gle0P => //; apply/auxP.
rewrite io; apply /(Exercise1_19a oa' alne'). 
move=> [wg1 wg2 wg3].
have p1: (forall i x y, inc i (substrate r') -> ~ glt (Vg g' i) x y).
  move=> i u v isr'; case:  (p_or_not_p (glt (Vg g' i) u v)) => // xy. 
  move: (wg2 _ _ _ isr' xy) => p1.
  rewrite sr' in isr'.
  have idg: inc i (domain g) by  rewrite - sr; apply: nss.
  move: (alsci _ idg) => [sca scb].
  have scc:  (sub (f i) (substrate (Vg g i))) by apply: Zo_S.
  move: p1 (scb _ scc);rewrite  (svig' _ isr');  rewrite /g' LgV// iorder_sr //.
move: scr => [_ scr]; move: (scr _ nss); case; split; fprops.
  case: wg1 => //; by  move=> [i [u [v [isr uv]]]]; case: (p1 i u v isr).
 rewrite dr' in p1.
move=> u v uv; case: (wg3 _ _ uv); first (by done); move => hm.
  have udg': inc u (domain g') by rewrite -dr'; order_tac.
  move: (rep_i (alne' _ udg')) => rm.
  case: (hm (rep (substrate (Vg g' u)))); split => //.
  move=> w we; symmetry;  ex_middle wr; case:(p1 _ _ _ udg' (conj we wr)).
have vdg': inc v (domain g') by rewrite -dr'; order_tac.
move: (rep_i (alne' _ vdg')) => rm.
case: (hm (rep (substrate (Vg g' v)))); split => //.
move=> w we;  ex_middle wr; case:(p1 _ _ _ vdg' (conj we wr)).
Qed.

(** ---- Exercise 1.21 Any set is isomorphic to an ordinal sum of scatteres sets whose index set is without gaps *)

Lemma Exercise1_2g r s: weak_order_compatibility r s->
  Ex1_2_hC' r s -> total_order r ->
  let r' := (quotient_order r s) in
    forall x y, gle r' x y <-> [/\ inc x (quotient s) , inc y (quotient s)&
       gle r (rep x) (rep y)].
Proof. 
move=> [[ps es sr] woc] qoa [or tor] r' x y. 
have ru: (forall u, inc u (quotient s) -> inc (rep u) u). 
  by move=> u uq;  apply: (setQ_repi es uq).
split.
  move /quotient_orderP=> [xq yq etc]; split => //.
  move: (ru _ xq) (ru _ yq) => rxx ryy.
  have rxs: (inc (rep x) (substrate r)) by  rewrite - sr; fprops.
  have rys: (inc (rep y) (substrate r)) by  rewrite - sr; fprops.
  case: (tor _ _ rys rxs) => // crxy.
  move: (etc _ rxx) => [z zy rz].
  have ryz: (gle r (rep y) z) by order_tac.
  have syz: (related s (rep y) z).
    by apply /(rel_in_class es _ zy); apply /(setQ_P es).
  by move: (qoa _ _ _ crxy rz syz) =>/(related_rr_P es yq xq) ->; order_tac.
move => [xq yq rr].
apply /quotient_orderP;split => // u ux.
move: (ru _ xq) (ru _ yq) => rxx ryy.
have rrux: (related s (rep x) u).
  by apply /(rel_in_class es _ ux); apply /(setQ_P es).
move:  (woc _ _ _ rr rrux)=> [v v1 v2]; exists v => //.
by apply: (rel_in_class2 es _ v1);  apply /(setQ_P es).
Qed.

Lemma Exercise1_2h r s: weak_order_compatibility r s->
  Ex1_2_hC' r s -> total_order r ->
  total_order (quotient_order r s).
Proof. 
move=> woc qoa tor.
move: (Exercise1_2g woc qoa tor) => e2g.
move: (woc) tor =>  [[ps es sr] woc'] [or tor].
move: (Exercise1_2d es or sr qoa) => oqo; split => //.
rewrite substrate_quotient_order //.  
move=> x y xq yq.
have rx: (inc (rep x) (substrate r)) by rewrite - sr; apply: rep_i_sr.
have ry: (inc (rep y) (substrate r)) by rewrite - sr; apply: rep_i_sr.
by case: (tor _ _ rx ry) => h; [left | right]; rewrite e2g.
Qed.

Lemma Exercise1_2i r s
  (q := quotient s)
  (r' := quotient_order r s)
  (f' := identity_g q)
  (g' := Lg q (fun z => induced_order r z))
  (du := disjointU f')
  (f :=  Lf (fun x => J x (class s x)) (substrate r) du):
  weak_order_compatibility r s->
  Ex1_2_hC' r s -> total_order r ->
  [/\ orsum_ax r' g',
    (forall i, inc i (domain g') -> nonempty (substrate (Vg g' i))),
    substrate (order_sum r'  g') = du,
    (forall x y, inc x (substrate r) -> inc y (substrate r) ->
      (related s x y <->
        related (equivalence_associated (second_proj du))  (Vf f x) (Vf f y)))&
     order_isomorphism f r (order_sum r' g')].
Proof. 
move=> woc qoa tor.
move: (Exercise1_2g woc qoa tor) (Exercise1_2h woc qoa tor)=> p1 [p2 p3].
move: woc tor => [[ps es sr] woc'] [or tor].
have sr': (substrate r' = q) by rewrite /r' substrate_quotient_order //. 
have iqs: (forall i, inc i q -> sub i (substrate r)).
  move=> i iq t ti; rewrite - sr;apply: (inc_in_setQ_sr es ti iq).
have oa1: orsum_ax r' g'.
  rewrite /g';saw.
   hnf;aw;move=> i iq; rewrite LgV//; move: (iqs _ iq) => h.
   apply: (proj1 (iorder_osr or h)).
have oa2: (forall i : Set, inc i (domain g') -> nonempty (substrate (Vg g' i))).
  rewrite /g'; aw; move=> i iq; rewrite LgV//; move: (iqs _ iq) => h.
  rewrite iorder_sr //; apply: (setQ_ne es iq).
have sos: substrate (order_sum r' g') = du.
  rewrite orsum_sr // /du /sum_of_substrates /f' /fam_of_substrates.
  rewrite /g';aw; apply: f_equal; apply: Lg_exten => x xd /=.
 rewrite LgV// iorder_sr//; fprops.
have ta: lf_axiom (fun x => J x (class s x)) (substrate r) du.
  move=> t tr /=.
  have ts: inc t (substrate s) by ue.
  have tc: inc t (class s t) by apply:inc_itself_class => //.
  apply: disjointU_pi; rewrite /f'.
  rewrite identity_d; apply /(setQ_P es); apply: class_class => //.
  by rewrite /identity_g LgV//; apply: inc_class_setQ.
have bf: bijection f.
  rewrite /f;apply: lf_bijective => //. 
    move=> u v _ _ sj; apply: (pr1_def sj).
  move=> y ydu; move:  (disjointU_hi ydu).
  rewrite /f' /identity_g Lgd; move=> [qy]; rewrite LgV// => Py py.
  move: ((iqs _ qy) _ Py) => psr; ex_tac; apply: pair_exten; aww.
  apply: is_class_pr => //.
have tf: du = target f by rewrite /f; aw.
have sf: substrate r = source f by rewrite /f; aw.
have du1: du = sum_of_substrates g' by rewrite - sos  orsum_sr //.
split => //.
  move=> x y xsr ysr.
  have sxx:related s x x by rewrite - sr in xsr;equiv_tac.
  rewrite du1  -/(E13_S _) /f LfV//; split.
   move => sxy; apply/(Exercise1_3a6P g'); rewrite LfV// ;split => //.
       by rewrite /E13_sF -du1; apply: ta.
     by rewrite /E13_sF -du1; apply: ta.
  by move /(related_equiv_P es): sxy => [_ _]; aw.
  move /(Exercise1_3a6P g'); move => [_ _]; rewrite LfV//; aw => h.
  apply  /(related_equiv_P es);split => //; ue.
split => //; fprops.
  saw; ue.
red; rewrite - sf; move=> x y xsf ysf; rewrite /f !LfV//.
have Jx: inc (J x (class s x)) du by apply: ta.
have Jy: inc (J y (class s y)) du by apply: ta.
rewrite - sr in xsf ysf.
have cxq: inc (class s x) q by apply: inc_class_setQ.
have cyq: inc (class s y) q by apply: inc_class_setQ.
have xcx: inc x (class s x) by apply:inc_itself_class.
have ycy: inc y (class s y) by apply:inc_itself_class.
have sxx:related s x x by equiv_tac.
split.
  move => rxy; apply /orsum_gleP; rewrite -du1;split => //.
  case: (p_or_not_p (related s x y)) => sxy.
    have aux: class s x = class s y by apply: class_eq1.
    right;saw; rewrite /g' LgV//; apply /iorder_gle0P => //; ue.
  left; aw;split; last by dneg xx; apply /(related_equiv_P es).
  apply /quotient_orderP; split => //.
  move=> z /(class_P es) sxz; move: (woc' x y z rxy sxz)=> [t syt rzt].
  by exists t=> //; apply /(class_P es).
move  /orsum_gleP => [_ _]; case; last first.  
  move=> [_]; aw; rewrite /g' LgV// => h; apply: (iorder_gle1 h).
aw; move => [] /quotient_orderP [q1 q2 h] necc. 
move: (h _ xcx) => [z zc xz].
rewrite sr in xsf ysf;case: (tor _ _  xsf ysf) => // yx.
case: necc; apply: (class_eq1 es).
apply: (symmetricity_e es);move: zc => /(class_P es) zc. 
apply: (qoa y x z yx xz zc).
Qed.


Lemma Exercise1_2j r s: weak_order_compatibility r s->
  Ex1_2_hC'  r s -> total_order r ->
  let r' := (quotient_order r s) in
    forall x y, inc x (substrate r ) -> inc y (substrate r) ->
      ((gle r x y -> gle r' (class s x) (class s y))
      /\ (glt r' (class s x) (class s y)  -> glt r x y)). 
Proof. 
move=> woc qoa tor r' x y xsr ysr.
move: (Exercise1_2h woc qoa tor) => [tqor _].
move: tor woc  => [or tor'] [[ps es sr] woc'].
have aux : forall  x y,gle r x y -> gle r' (class s x) (class s y).
  move=> a b ab; apply /quotient_orderP.
  move: (arg1_sr ab) (arg2_sr ab).
  rewrite - sr => asr bsr; split => //; try apply: inc_class_setQ => //.
  move=> c /(class_P es) ac.
  by move: (woc' _ _ _ ab ac) => [d bd cd]; exists d=> //; apply /(class_P es).
split; first by apply: aux => //.
move=> [h1 nc]; split; last by dneg xy; ue.
case: (tor' _ _ xsr ysr) => // xy; move: (aux _ _  xy) => h2.
case: nc; order_tac.
Qed.

Definition scattered_rel r x y :=
  (gle r  x y /\  scattered (induced_order r (interval_cc r x y)))
  \/ (gle r  y x /\  scattered (induced_order r (interval_cc r y x))).

Definition scattered_equiv r := graph_on (scattered_rel r) (substrate r).

Lemma Exercise1_21aP r v: order r ->
  sub v (substrate r) ->
  (scattered (induced_order r v) <->
    (forall u, sub u v ->  ~ without_gaps (induced_order r u))).  
Proof. 
move => or vsr; rewrite /scattered. 
move: (iorder_osr or vsr) => [pa pb];rewrite pb => //; split. 
  by move=> [oi h] u uv; move: (h _ uv);  rewrite iorder_trans.
move=> h;split;fprops;move=> x xv; move:(h _ xv);  rewrite iorder_trans //.
Qed.

Lemma Exercise1_21bP r u: total_order r ->
  sub u  (substrate r) ->
  ((exists x y, glt (induced_order r u) x y) <->
    (exists x y, [/\ inc x u, inc y u & x<> y])).
Proof. 
move=> [or tor] uv; split. 
   move=> [x [y [h1 h2]]].
   move: (iorder_gle3 h1) => [xr yr]; exists x, y; split => //.
move=> [x [y [h1 h3 h4]]]; case: (tor _ _ (uv _ h1) (uv _ h3)) => h5.
  by exists x; exists y; split =>//; apply /iorder_gleP. 
by exists y; exists x; split; [ apply /iorder_gleP |apply:nesym ].
Qed.

Lemma Exercise1_21cP  r u: total_order r ->
  sub u  (substrate r) ->
  ((forall a b, inc a u -> inc b u -> a = b) <->
    ~ (exists x y, glt (induced_order r u) x y)).
Proof. 
move=> tor usr; split.
  move => ha hb; move / (Exercise1_21bP tor usr) : hb =>[x [y [xu yu]]].
  case; apply (ha _ _ xu yu).
move =>h a b au bu;  ex_middle ab; case: h.
by apply/ (Exercise1_21bP tor usr); exists a, b. 
Qed.

Lemma Exercise1_21dP r u: total_order r ->
  sub u (substrate r) ->
  ((~ without_gaps (induced_order r u))  <->
  ((forall a b, inc a u -> inc b u -> a = b)
      \/ (exists a b, [/\ inc a u, inc b u, glt r a b &
        (forall z, inc z u -> gle r z a \/ gle r b z)]))).
Proof. 
move=> tor usr; move: (tor) => [or tor'].
move: (iorder_osr or usr) => [oi soi].
rewrite / without_gaps.
set P1:= (exists x y, glt (induced_order r u) x y).
split => h1.
  case: (p_or_not_p P1) => np1; [right | left ] =>//;
    last by apply/(Exercise1_21cP tor usr).
  ex_middle emh; case: h1; split => //;  move=> x y ltxy.
  ex_middle aux; case: emh.
   move:(iorder_gle4 ltxy)(iorder_gle2 ltxy)=> [h2 h3] h4.
   exists x, y; split => //; move => z zu.
   move:  (usr _ zu) (usr _ h2) (usr _ h3) => zs xs ys.
   case: (tor' _ _ zs ys) => h6; last by right.
   case: (tor' _ _ xs zs) => h5; last by left.
   case: (equal_or_not x z) => xz; first by  left; rewrite xz; order_tac.
   case: (equal_or_not y z) => yz; first by right; rewrite yz; order_tac.
   have zy:  z <> y by apply:nesym.
   case: aux; exists z; apply /iorder_gltP; split => //.
move=> [_ P1t h2]. 
case: h1; first by move /(Exercise1_21cP tor usr); case.
move=> [a [b [au bu ab etc]]].
have aux: glt (induced_order r u) a b by  apply /iorder_gltP. 
move: (h2 _ _ aux)=> [z] /iorder_gltP [_ zu za]/iorder_gltP [_ _ zb]. 
case: (etc _ zu) => h3; order_tac.
Qed.

Lemma Exercise1_21e r u a b: total_order r ->
  let v:= u \cap (interval_cc r a b) in 
  sub u (substrate r) -> without_gaps (induced_order r u) ->
  (exists x y,  [/\ inc x v, inc y v & glt r x y]) ->
  without_gaps (induced_order r v).
Proof. 
move=> tor v usr wg h1.
have svu: (sub v u) by apply: subsetI2l.
have svi: (sub v (interval_cc r a b)) by apply: subsetI2r.
have svr: (sub v (substrate r)) by apply: (sub_trans svu). 
ex_middle wg1.
move: wg1 => /(Exercise1_21dP tor svr) wg1. 
have: (~ ~ without_gaps (induced_order r u)) by case. 
move /(Exercise1_21dP tor usr) => wg2. 
case: wg2; case: wg1. 
  by move:h1 => [c [d [cv dv [_ cd]]]] h2; move: (h2 _ _  cv dv). 
move=> [c [d [cv dv cd icd]]]; right; exists c; exists d; split;fprops.
move=> z szu.
move: tor => [or tor].
case: (tor  _ _ (usr _ szu) (svr _ cv)) => zc; first by left.
case: (tor  _ _ (svr _ dv) (usr _ szu) ) => zd; first by right.
move: cv dv => /setI2_P [_] /Zo_hi [ac _] /setI2_P [_] /Zo_hi [_ db].
apply: icd;  apply: setI2_i => //; apply: Zo_i ; [| split => //]; order_tac. 
Qed.

Lemma Exercise1_21f r a b u: total_order r ->
  sub u (substrate r) ->
  inc a u -> inc b u -> glt r a b -> without_gaps (induced_order r u) ->
  without_gaps (induced_order r (u \cap (interval_cc r a b))).
Proof. 
move=>  tor usr au bu ab wg;  move: (tor) => [or _].
by apply:  Exercise1_21e => //; exists a, b;split => //;apply/setI2_P; 
   split => //;apply /Zo_P;split => //; try split=> //; order_tac; apply: usr.
Qed.

Lemma Exercise1_21g r x y z: total_order r ->
  gle r  x y ->  gle r y z->
  scattered (induced_order r (interval_cc r x y)) ->
  scattered (induced_order r (interval_cc r y z)) ->
  scattered (induced_order r (interval_cc r x z)).
Proof. 
move=>  tor xy yz scxy scyz.
move: (tor) => [or tor'].
have xz:(gle r x z) by order_tac.
have sxz:sub (interval_cc r x z) (substrate r) by apply: Zo_S.
have sxy:sub (interval_cc r x y) (substrate r) by apply: Zo_S.
have syz:sub (interval_cc r y z) (substrate r) by apply: Zo_S.
move: scxy scyz => /(Exercise1_21aP or sxy) scxy /(Exercise1_21aP or syz) scyz.
apply /(Exercise1_21aP or sxz) => u uxz.
case: (p_or_not_p (without_gaps (induced_order r u))) =>// wg.
have us: (sub u (substrate r)) by apply: sub_trans sxz.
set (u1 := u \cap (interval_cc r x y)).
set (u2 := u \cap (interval_cc r y z)).
have su1: sub u1 (interval_cc r x y) by  apply: subsetI2r.
have su2: sub u2 (interval_cc r y z) by  apply: subsetI2r.
have up1: forall t, inc t u -> gle r t y -> inc t u1. 
  move=> t tu ty; move: (uxz _ tu) => /Zo_P [t1 [t2 t3]].
  apply: setI2_i => //;apply: Zo_i => //. 
have up2: forall t, inc t u -> gle r y t -> inc t u2. 
  move=> t tu ty; move: (uxz _ tu) => /Zo_P [t1 [t2 t3]].
  apply: setI2_i => //;apply: Zo_i => //.
apply /(Exercise1_21dP tor us).
case: (p_or_not_p (exists x y, glt (induced_order r u) x y)); last first.
   by move /(Exercise1_21cP tor us); left.
move=> [a [b ltab]]; right.
move: (iorder_gle4 ltab) (iorder_gle2 ltab) => [au bu] ltab1.
exists a, b; split => // t tu. 
case: (tor' _ _ (us _ au) (us _ tu)) => ta; last by left.
case: (tor' _ _ (us _ tu) (us _ bu)) => tb; last by right.
have ysr: inc y (substrate r) by order_tac.
move: (scxy _ su1) (scyz _  su2) => wg1 wg2.
case: (tor' _ _ ysr (us _ tu)) => ty.
  move: (up2 _ tu ty) (up2 _ bu (order_transitivity or ty tb)) => t2 b2.
  case: (equal_or_not t b); first by move => ->; right; order_tac; order_tac.
  move=> bt1; have bt: glt r t b by order_tac.
  case: wg2; apply: Exercise1_21e => //; exists t, b; split => //.
move: (up1 _ tu ty) (up1 _ au (order_transitivity or ta ty )) => t2 b2.
case: (equal_or_not a t); first by move => ->; left; order_tac; order_tac.
move=> at1; have at2: glt r a t by order_tac.
by case: wg1; apply: Exercise1_21e => //; exists a,  t.
Qed.

Lemma Exercise1_21h r: total_order r ->
  equivalence_re (scattered_rel r) (substrate r).
Proof.
move=> tor; move: (tor) => [or tor'].
have Ha: forall a b x y, gle r x a -> gle r b y ->
    sub (interval_cc r a b) (interval_cc r x y).
   move=> a b x y xa lby t /Zo_P [tsr [lat tb]]. 
   apply /Zo_P;split => //; split; order_tac. 
have Hb: forall a b x y, gle r x a -> gle r b y ->
    sub (interval_cc r a b) (substrate (induced_order r (interval_cc r x y))).
  by move=> a b x y xa yb; rewrite iorder_sr //; [ apply: Ha | apply: Zo_S].
red; rewrite /scattered_rel; split; last first.
  move=> y; split; last by case;move=> [yy _]; order_tac.
  move=> ysr;  left;set I:= interval_cc r y y.
  have Iy: (forall t, inc t I -> t = y).  
    move=> t /Zo_P [_ [t1 t2]]; order_tac.
  have Isr: (sub I (substrate r)) by apply: Zo_S.
  split; first (by order_tac); apply /Exercise1_21aP => //.
  move => u uI ; apply /(Exercise1_21dP) => //; first by apply: sub_trans Isr.
  by left; move=> a b aI bI; rewrite (Iy _ (uI _ aI)) (Iy _ (uI _ bI)).
split; first by (move=> x y; rewrite /scattered_rel; case; [right| left]).
move=> y x z; case; move=> [xy sxy].
  case; move=> [yz syz].
    left; split; [order_tac | apply: (Exercise1_21g tor xy yz sxy syz)].
  have xsr: inc x (substrate r) by order_tac. 
  have zsr: inc z (substrate r) by order_tac.
  case: (tor' _ _ xsr zsr) => xz; [left | right]; split => //.
    have xx: (gle r x x) by order_tac.
    move: (Hb _ _ _ _ xx yz) => hs; move: (Exercise1_20a hs sxy). 
    rewrite iorder_trans //;  by apply: Ha.
  have zz: (gle r z z) by order_tac.
    move: (Hb _ _ _ _ zz xy) => hs;  move: (Exercise1_20a hs syz). 
    rewrite iorder_trans // ; by apply: Ha. 
case; move=> [yz syz]; last first.
  by right; split; [order_tac | apply: (Exercise1_21g tor  yz xy syz sxy) ].
have xsr: inc x (substrate r) by order_tac. 
have zsr: inc z (substrate r) by order_tac.
case: (tor' _ _ xsr zsr) => xz; [left | right]; split => //.
  have zz: (gle r z z) by order_tac.
  move: (Hb _ _ _ _ xy zz) => hs; move: (Exercise1_20a hs syz). 
  rewrite iorder_trans //; by apply: Ha.
have xx: (gle r x x) by order_tac.
  move: (Hb _ _ _ _ yz xx) => hs; move: (Exercise1_20a hs sxy). 
  rewrite iorder_trans // ; by apply: Ha. 
Qed.

Lemma Exercise1_21i r: total_order r ->
  equivalence (scattered_equiv r).
Proof.
move /Exercise1_21h => [pa pb].
by apply: equivalence_from_rel.
Qed.

Lemma Exercise1_21j r: total_order r ->
  substrate (scattered_equiv r) = substrate r.
Proof. 
move=> tor;  apply: graph_on_sr. 
by move=> a asr; move:  (Exercise1_21h tor) => [_ rr]; rewrite -rr.
Qed.

Definition scattered_aux1 r x y :=
  (forall u, sub u (interval_cc r x y) ->
    ((forall a b, inc a u -> inc b u -> a = b)
      \/ (exists a b, [/\ inc a u, inc b u, glt r a b &
        (forall z, inc z u -> gle r z a \/ gle r b z)]))).
Definition scattered_aux r x y :=
  gle r x y /\ scattered_aux1 r x y.


Lemma Exercise1_21kP r x y: total_order r ->
  gle r  x y ->
  (scattered (induced_order r (interval_cc r x y)) <->
   scattered_aux1 r x y).
Proof. 
move=> tor xy.
have or: order r  by move: tor => [or _ ].
set (i:=interval_cc r x y). 
have si: (sub i (substrate r)) by apply: Zo_S. 
have usr: (forall u, sub u i -> sub u (substrate r)).
  move => u ui; apply: (sub_trans ui si). 
split.
  move /(Exercise1_21aP or si) => h u ui. 
  apply /(Exercise1_21dP tor (usr _ ui)); apply: (h _ ui).
move => hyp; apply /(Exercise1_21aP or si) => u ui.
apply /(Exercise1_21dP tor  (usr _ ui)) => //; exact (hyp _ ui).
Qed.

Lemma Exercise1_21l r x y: total_order r ->
  (related (scattered_equiv r) x y <->
    (scattered_aux r x y \/ scattered_aux r y x)).
Proof.
move=> tor; split.
  by move /graph_on_P1 => [xsr ysr scxy];case: scxy; move=> [rxy];
     move /(Exercise1_21kP tor rxy) => aux;[ left | right]. 
by case; move=> [xsr aux]; apply /graph_on_P1;split => //;
  try order_tac; [left | right];split => //; apply / Exercise1_21kP.
Qed.


Lemma Exercise1_21m r: total_order r ->
  weak_order_compatibility r (scattered_equiv r).
Proof.
move=> tor; move: (tor) => [or tor'].
move: (Exercise1_21i tor) => es.
move: (Exercise1_21j tor) => ss.
split => //; first by split => //; by apply: order_preorder. 
move=> x y x' xy.
have ysr: (inc y (substrate r)) by order_tac. 
move: (ysr); rewrite - ss => yss.
have seyy: (related (scattered_equiv r) y y) by equiv_tac.
case/ (Exercise1_21l x x' tor) => - [xx' sc]; last first.
  exists y => //; order_tac.
have x'sr: inc x' (substrate r) by order_tac. 
case: (tor' _ _ ysr x'sr) => yx'; last by exists y.
  exists x'=> //;last (by order_tac);apply /Exercise1_21l=> //;left; split=> //.
  move=> u ui; apply: sc; move => t tu; move: (ui _ tu) => /Zo_P [tsr [xt tx']].
apply /Zo_P;split => //; split => //; order_tac.
Qed.

Lemma Exercise1_21n r x: total_order r -> inc x (substrate r) ->
  scattered (induced_order r (class (scattered_equiv r) x)).
Proof.
move=> tor xsr.
move: (Exercise1_21i tor)(Exercise1_21j tor) => es ss.
move: tor => [or tor].
have sc:(sub (class (scattered_equiv r) x) (substrate r)). 
 by rewrite - ss;apply: sub_class_substrate.  
move: (iorder_osr or sc) => [pa pb].
split => //.
move=> y; rewrite iorder_sr // => yc; rewrite (iorder_trans _ yc).
have yp: forall u, inc u y -> related (scattered_equiv r) u x. 
  move=> u uy; move: (yc _ uy) => /(class_P es) aux; equiv_tac. 
move=>[oiy [a [b rab]] wg2].
move: (iorder_gle4 rab)=> [ay biy]; move: (yp _ ay) (yp _ biy)=> ax bx.
have xb:(related (scattered_equiv r) x b) by equiv_tac.
have :(related (scattered_equiv r) a b ) by equiv_tac.
apply /Exercise1_21l  =>//; case;  move=> [aux1 aux2]; last first.
  move: (iorder_gle2 rab) => aux3; order_tac.
have asr: inc a (substrate r) by order_tac.
have bsr: inc b (substrate r) by order_tac.
move: (@subsetI2r y (interval_cc r a b)) => uy.
case: (aux2 _ uy).
  set u:= _ \cap _.
  have au:inc a u by apply: setI2_i => //;apply:Zo_i => //;split =>//;order_tac.
  have bu:inc b u by apply: setI2_i => //;apply:Zo_i => //;split =>//;order_tac.
  by move=> aux3; move: (aux3 _ _ au bu); case: rab.
move=> [c [d  [cu du cd cde]]].
have cd1: (glt (induced_order r y) c d). 
   apply /iorder_gltP;split => //; [ apply:(setI2_1 cu) |apply: (setI2_1 du) ].
move: (wg2 _ _ cd1) => [e ce ed].
move:(iorder_gle4 ce)(iorder_gle2 ce) (iorder_gle2 ed) => [_ er] ce' de'.
have aux:inc e (y \cap (interval_cc r a b)).
  apply: setI2_i => //; apply: Zo_i; [ order_tac | split => //]. 
  move:(setI2_2 cu) => /Zo_hi  [ac _]. 
     move: ce' => [ce' _];order_tac.
  move:(setI2_2 du) => /Zo_hi [_ db]. 
     move: de' => [de' _];order_tac.
case: (cde _ aux)=> aux3; order_tac.
Qed.

Lemma Exercise1_21o r: total_order r ->
  Ex1_2_hC' r (scattered_equiv r).
Proof. 
move=> tor; move=> x y z xy yz; move/(Exercise1_21l _ _ tor).
move:(Exercise1_21i tor)(Exercise1_21j tor) => es ss. 
move: tor => [or tor]; case;move=> [xx hyp].
    apply/Exercise1_21l => //;left; split => //.  
  move=> u ui; apply: hyp => //; move=> t tu; move: (ui _ tu) => /Zo_P.
  move=> [tsr [xt ty]]; apply /Zo_P; split => //;split => //; order_tac.
have leyx: (gle r y x) by order_tac. 
have <-: (x = y) by order_tac. 
have:(inc x (substrate r)) by order_tac.
rewrite - ss=> xsr;equiv_tac.
Qed.

Lemma Exercise1_21p r: total_order r ->
  order (quotient_order r (scattered_equiv r)).
Proof.
move => tor.
move: (Exercise1_21i tor) (Exercise1_21j tor)(Exercise1_21o tor) => p1 p2 p3.
by move: tor => [or _]; apply: Exercise1_2d. 
Qed.


Lemma Exercise1_21q r: total_order r ->
  let r' := quotient_order r  (scattered_equiv r) in
    small_set (substrate r') \/ without_gaps r'.
Proof. 
move=> tor r'.
move: (Exercise1_21m tor)(Exercise1_21o tor) => Ha Hb.
move: (Exercise1_2g Ha Hb tor) (Exercise1_2h Ha Hb tor)=> qo [oq toq].
simpl in qo; rewrite -/r' in qo oq toq.
move: (tor) => [or tor'].
set (s:= scattered_equiv r) in *.
have Hc:forall a b, gle r a b -> gle r' (class s a) (class s b).
  move=> a b ab.
  move: (arg1_sr ab) (arg2_sr ab) => asr bsr.
  by move:  (Exercise1_2j Ha Hb tor asr bsr) => [ok _]; apply: ok.
case: (p_or_not_p (small_set (substrate r'))); first by left.
move=> nss; right; split => //.
  ex_middle ne; case: nss => a b asr' bsr'. 
  ex_middle ab; case: (toq _ _ asr' bsr') => cab.
     by case: ne; exists a, b.
  by case: ne; exists b, a; split; fprops.
move: Ha => [[pr es ss] woc].
have sr': (substrate r' = quotient s) by  rewrite /r' substrate_quotient_order. 
move=> x y xy; move: (xy) => [lexy nxy].
have nsxy: (~ (related s (rep x) (rep y))).
  apply /related_rr_P =>//;rewrite - sr'; order_tac.
ex_middle nez; case: nsxy.
move: lexy; rewrite qo; move=> [xq yq lerxy].
apply /graph_on_P1; split => //; try order_tac. 
left;split => //.
have si: (sub (interval_cc r (rep x) (rep y)) (substrate r)) by apply: Zo_S. 
apply /(Exercise1_21aP or si).
have Hx:class s (rep x) = x by apply: class_rep.
have Hy:class s (rep y) = y by apply: class_rep.
move=> u ui [oi woi1 woi2].  
have uxu:  (forall a, inc a u -> inc a x \/ inc a y).
  move=> a au; move: (ui _ au) => /Zo_P [asr [rxa ary]].
  move: (Hc _ _ rxa); rewrite Hx => xca.
  move: (Hc _ _ ary); rewrite Hy => yca.
  case: (equal_or_not x (class s a)) => xca1.
    left; rewrite xca1; apply: inc_itself_class => //; ue.
  have p1: (glt r' x (class s a)) by split.
  case: (equal_or_not (class s a) y) => yca1.
    right; rewrite -yca1; apply: inc_itself_class => //; ue.
  have p2: (glt r' (class s a) y) by split.
  case: nez; exists (class s a); split => //.
move: (class_rep es xq) (class_rep es yq) => c1 c2.
have rxsr: (inc (rep x) (substrate r)) by order_tac.
have rysr: (inc (rep y) (substrate r)) by order_tac.
have Hu:forall a, inc a x -> x = class s a by move=> b bx;apply: is_class_pr.
have Hv:forall a, inc a y -> y = class s a by move=> b bx;apply: is_class_pr.
have  xsr: sub x (substrate r) by rewrite - ss - c1; apply: sub_class_substrate.
have  ysr: sub y (substrate r) by rewrite - ss - c2; apply: sub_class_substrate.
move: (Exercise1_21n tor rxsr); rewrite -/s c1.
move: (Exercise1_21n tor rysr); rewrite -/s c2.
move /(Exercise1_21aP or ysr) => c3 /(Exercise1_21aP or xsr) c4.
set (u1:= u \cap x). 
have u1x: (sub u1 x) by apply: subsetI2r. 
have u1sr: (sub u1 (substrate r)) by apply: (sub_trans u1x). 
move: (c4 _ u1x) => /(Exercise1_21dP tor u1sr) c5.
set (u2:= u \cap y). 
have u2y: (sub u2 y) by apply: subsetI2r. 
have u2sr: (sub u2 (substrate r)) by apply: (sub_trans u2y).
move: (c3 _ u2y) => /(Exercise1_21dP tor u2sr)  c6.
have p1u: (~(exists a b, [/\ inc a u1, inc b u1 & glt r a b])). 
  move=> [a [b [au1 bu1 ab]]].
  case: c5 => c5'; first by move:ab=> [_ ab]; case:ab; exact: (c5' _ _ au1 bu1).
  move: c5' => [a' [b' [a'u1 b'u1  ab' ie]]].
  move: (@subsetI2l u x) => u1x'.
  have ab'': glt (induced_order r u)  a' b' by apply/iorder_gltP; split;fprops.
  move: (woi2 _ _ ab'') => [c ca cb].
  move:(iorder_gle4 ca)(iorder_gle2 ca)(iorder_gle2 cb) => [_  cu] ca' cb'.
  suff uc1: (inc c u1) by case: (ie _ uc1)=> h; order_tac.
  apply: setI2_i => //; case: (uxu _ cu) => //cy.
  move: cb' => [cb'' _]; move: (Hc _ _ cb'').
  rewrite -(Hv _ cy) - (Hu  _ (setI2_2 b'u1)) => bad; order_tac.
have p2u: (~(exists a b, [/\ inc a u2, inc b u2 & glt r a b])). 
  move=> [a [b [au1 bu1 ab]]].
  case: c6 => c6'; first by move:ab=> [_ ab]; case:ab; exact: (c6' _ _ au1 bu1).
  move: c6' => [a' [b' [a'u1 b'u1 ab' ie]]].
  move: (@subsetI2l u y) => u2y'.
  have ab'': glt (induced_order r u)  a' b' by apply/iorder_gltP; split;fprops.
  move: (woi2 _ _ ab'') => [c ca cb].
  move:(iorder_gle4 ca)(iorder_gle2 ca)(iorder_gle2 cb) => [_  cu] ca' cb'.
  suff uc2: (inc c u2) by case: (ie _ uc2)=> h; order_tac.
  apply: setI2_i => //; case: (uxu _ cu) => //cx.
  move: ca' => [ca'' _]; move: (Hc _ _ ca'').
  rewrite -(Hu _ cx) - (Hv _ (setI2_2 a'u1)) => bad; order_tac.
move: woi1 => [a [b lab]]; move: (woi2 _ _ lab) => [c lac lcb].
move: (iorder_gle4 lac)(iorder_gle4 lcb) => [au cu][_ bu].
move: (iorder_gle2 lac)(iorder_gle2 lcb) => ltac ltcb.
have ltab: glt r a b by  order_tac.
case: (uxu _ au) => axy.
  have au1: inc a u1 by apply: setI2_i.
  case: (uxu _ cu) => cxy.
    case: p1u; exists a, c;split => //; by apply: setI2_i.
  case: (uxu _ bu) => bxy.
    case: p1u; exists a, b;split => //; by  apply: setI2_i.
  case: p2u; exists c, b;split => //; by  apply: setI2_i.
have au2: inc a u2  by apply: setI2_i.
case: (uxu _ cu) => cxy.
  case: (uxu _ bu) => bxy.
    case: p1u; exists c, b;split => //; by  apply: setI2_i.
  case: p2u; exists a, b;split => //; by  apply: setI2_i.
case: p2u; exists a, c;split => //; by  apply: setI2_i.
Qed.


Lemma Exercise1_21r r: total_order r ->
  exists r' g',
  [/\ orsum_ax r' g', orsum_ax2 g',
    r \Is  (order_sum r' g'),
    (small_set (substrate r') \/ without_gaps r') &
    allf g' scattered].
Proof.
set (s:= (scattered_equiv r)) => tor.
move: (@Exercise1_2i r s) => /=.
have p1: weak_order_compatibility r s  by apply: Exercise1_21m.
have p2: Ex1_2_hC' r s by apply: Exercise1_21o.
move=> h; move: (h p1 p2  tor).
set q:= quotient s; set d := (disjointU _).
 move => [q1 q2 q3 q4 [q5 q6]] {h}.
exists (quotient_order r s); exists(Lg q(fun z => induced_order r z)).
split => //.
- by exists (Lf (fun x => J x (class s x)) (substrate r) d). 
- by apply: Exercise1_21q.
- rewrite/allf;aw;move=> i idg; rewrite LgV//; move: idg => /funI_P  [z zs] ->.
  by apply: (Exercise1_21n tor); rewrite - (Exercise1_21j tor).
Qed.


(** ---- Exercise 1.22: open and regular sets.
We define an open set [open_o] and a regular open set [open_r]. Every open set 
is cofinal in exactly one regular open set, namely [bar1_22]. This mapping is 
increasing for [sub]; it maps disjoint sets to disjoint sets *)

Definition open_o r u:=  
  sub u (substrate r) /\ forall x y, inc x u -> gle r x y -> inc y u.
Definition open_r r u:=  
  open_o r u /\
  forall v, open_o r v -> cofinal (induced_order r v) u -> u = v.

Definition open_bar r u :=
  union (Zo (\Po(substrate r))
    (fun z => open_o r z /\ cofinal (induced_order r z) u)).

Definition reg_opens r := Zo (\Po (substrate r)) (open_r r).
Definition reg_open_order r :=  sub_order (reg_opens r).

Lemma inf_pr2 r x y z:
  order r -> gle r z x  -> gle r z y ->
  (forall t, gle r t x -> gle r t y -> gle r t z) ->
  inf r x y = z.
Proof. 
move=> or zx zy h.
move: (glb_set2 or zx zy h) => aux.
symmetry;apply: infimum_pr2 => //. 
Qed.

Section Exercise1_22.
Variable r:Set.
Hypothesis or: order r.


Lemma reg_opens_i x: open_r r x -> inc x (reg_opens r).
Proof.
move => h; apply /Zo_i => //; apply /setP_P; apply: (proj1 (proj1 h)).
Qed.

Lemma  Exercise1_22a u1 u2: 
  open_o r u1 -> open_o r u2 -> open_o r (u1 \cup u2).
Proof. 
move=> [u1p u1r][u2p u2r]; split.
  move=> t; case/setU2_P; [apply: u1p | apply: u2p].
by move=> x y;case/setU2_P; move=> h le; apply /setU2_P;
  [left; apply: (u1r x) | right; apply: (u2r x)].
Qed.

Lemma Exercise1_22b u:
  alls u (open_o r) ->  open_o r (intersection u).
Proof.
move=>  alo.
have aux: forall t, inc t (intersection u) -> exists a, inc a u.
  move => t; case: (emptyset_dichot u).
    by move => ->; rewrite setI_0 => /in_set0.
  by move=> [a au] _; exists a.
split.
  move=> t tu; move: (aux _ tu) => [a au].
  move: (setI_hi tu au);  move: (alo _ au) => [p1 _]; apply: p1.
move=> x y xu xy; move: (aux _ xu) => [a au].
apply: setI_i; first by  exists a;apply: au.
move=> z zu; move: (alo _ zu) => [_ p2]; move: xy; apply: p2.
exact (setI_hi xu zu).
Qed.

Lemma Exercise1_22c u:
  alls u (open_o r) ->  open_o r (union u).
Proof. 
move=> alo; split.
  by move=>t /setU_P [y ty yu]; move: (alo _ yu) => [p1 _]; apply: p1.
move=> x y /setU_P [z xz zu] xy; move: (alo _ zu) => [_ p2].
apply /setU_P; exists z => //; exact (p2 _ _ xz xy).
Qed.

Lemma cofinal_inducedP u:  sub u (substrate r) ->
  forall v,
  cofinal (induced_order r u) v <->
  (sub v u /\ (forall x, inc x u -> exists2 y, inc y v & gle r x y)).
Proof.
move=> usr v; rewrite /cofinal iorder_sr//.
split; move=> [vu h]; split => //; move=> x xu; move: (h _ xu)=> [y yv yx].
  ex_tac; apply: (iorder_gle1  yx).
by ex_tac; apply /iorder_gle0P => //; apply: vu.
Qed.


Lemma Exercise1_22d x u1 u2:
  open_o r x -> open_r r u1 -> open_r r u2 ->
  cofinal (induced_order r u1) x -> cofinal (induced_order r u2) x ->
  u1 = u2.
Proof. 
move=> ox [ou1 pu1] [ou2 pu2] co1 co2.
move: (Exercise1_22a ou1 ou2).
move: (@subsetU2l u1 u2) (@subsetU2r u1 u2).
set (u3:= u1 \cup u2)  => su1 su2 ou3.
have su3: (sub u3 (substrate r)) by move: ou3 => [ok _].
have su1r: (sub u1 (substrate r)) by move: ou1 => [ok _].
have su2r: (sub u2 (substrate r)) by move: ou2 => [ok _].
move: co1 co2 => /(cofinal_inducedP su1r) [xu1 co1] 
   /(cofinal_inducedP su2r) [xu2 co2].
have co31:(cofinal (induced_order r u3) u1). 
 apply/cofinal_inducedP => //; split => // t /setU2_P; case.
   by move => tu1; ex_tac; order_tac; apply: su1r.
  move/co2 => [y /xu1 ya yb]; ex_tac.
rewrite(pu1 _ ou3 co31).
have co32:(cofinal (induced_order r u3) u2).
  apply/cofinal_inducedP => //; split => // t /setU2_P; case.
    move/co1 => [y /xu2 ya yb]; ex_tac.
  by move => tu1; ex_tac; order_tac; apply: su2r.
by rewrite (pu2 _ ou3 co32).
Qed.


Lemma Exercise1_22e  u:
  open_o r u ->  sub u (open_bar r u).
Proof. 
move=> ou t tu; move: (ou) => [ou1 ou2]; apply: (@setU_i _ u) => //. 
apply: Zo_i; [by apply /setP_P | split => //; split; rewrite iorder_sr   // ].
by move=> x xu; ex_tac; apply /iorder_gle0P => //; order_tac; apply: ou1.
Qed.

Lemma Exercise1_22f u:
  open_o r u ->  sub (open_bar r u) (substrate r).
Proof. 
move=> [ou1 ou2] t => /setU_P [y ty] /Zo_P [] /setP_P ysr _.
by apply: ysr.
Qed.

Lemma Exercise1_22g u:
  open_o r u ->
  cofinal (induced_order r (open_bar r u)) u.
Proof. 
move=> ou; move:(Exercise1_22e ou) (Exercise1_22f ou) => h1 h2.
apply /cofinal_inducedP => //; split => //.
move => x /setU_P [y xy] /Zo_P [] /setP_P ysr [oy ].
move /(cofinal_inducedP  ysr) => [uy h]; apply: (h _ xy).
Qed.

Lemma Exercise1_22h u x:
  open_o r u -> inc x (substrate r) ->
  (forall y, gle r x y -> exists2 z, inc z u &  gle r y z) ->
  inc x (open_bar r u).
Proof. 
move=> ou xsr xp.
move: (Exercise1_22f ou) => Ha.
set (t:=(open_bar r u) \cup (Zo (substrate r) (fun z=> gle r x z))).
have tsr: (sub t (substrate r)). 
  move=> v; case/setU2_P; [  apply: Ha |apply: Zo_S].
apply: (@setU_i _ t). 
  by apply: setU2_2; apply: Zo_i =>//; order_tac.
have ob: (open_o r (open_bar r u)).
  by apply:  Exercise1_22c => //;move=> v /Zo_hi [].
apply: Zo_i; [by apply /setP_P | split].
  apply:Exercise1_22a => //; split; first by apply: Zo_S.
  move=> a b => /Zo_P [asr xa] ab; apply: Zo_i; order_tac.
move: (Exercise1_22g ou) => /(cofinal_inducedP  Ha) [ubu c1].
have sut: sub u t by  move  => s su; apply /setU2_P; left; apply: ubu.
apply/(cofinal_inducedP tsr); split => // a iat.
case/setU2_P: (iat) => h; first by move: (c1 _ h).
by move: h =>/Zo_P [pa pb]; move : (xp _ pb).
Qed.

Lemma Exercise1_22i u:
  open_o r u -> open_r r (open_bar r u).
Proof.
move=> ou.
move: (Exercise1_22f ou) => sbu.
have op: (open_o r (open_bar r u)). 
  by apply:  Exercise1_22c => //; move => x => /Zo_hi [].
split => // v [sv ov] ; move: (Exercise1_22g ou).
move /(cofinal_inducedP sbu) => [_ c]. 
move /(cofinal_inducedP sv) => [ss c']; apply: extensionality =>// t tv.
apply: Exercise1_22h => //; first by apply: sv.
move=> y ty; move: (ov _ _ tv ty) => yv; move: (c' _ yv) => [z zb zy].
move: (c _ zb) => [w wu zw]; ex_tac; order_tac.
Qed.

Lemma Exercise1_22j u v:
  open_o r u -> open_o r v -> sub u v ->
  sub (open_bar r u)  (open_bar r v).
Proof. 
move=> ou ov uv.
move=> t tu;apply: Exercise1_22h => //; first by apply: (Exercise1_22f ou).
move: (Exercise1_22i ou) => [[ob1 ob2] _].
move=> y ty; move: (ob2 _ _ tu ty) => ybu.
move: (Exercise1_22g ou) => /(cofinal_inducedP ob1) [_ h].
move: (h _ ybu) => [z zu yz]; exists z => //;fprops.
Qed.

Lemma Exercise1_22k u v:
  open_o r u -> open_o r v ->  disjoint u v ->
  disjoint (open_bar r u)  (open_bar r v).
Proof.
rewrite /disjoint;move=> ou ov iuve; apply /set0_P.
move=> y /setI2_P [] /setU_P [z yz z1]  /setU_P [z' yz' z2].
move: z1 z2 => /Zo_P [] /setP_P z1 [[_ o1] c1] /Zo_P [] /setP_P z2 [[_ o2] c2].
move: c1 c2 => /(cofinal_inducedP z1) [uz c1]/(cofinal_inducedP z2)[vz' c2].
move: (c1 _ yz)=> [y1 y1u le1].
move: (c2 _ (o2 _ _ yz' le1)) => [y2 y2u le2].
empty_tac1 y2; apply: setI2_i => //.
move: ou => [_ ou]; exact: (ou _ _ y1u le2).
Qed.

(** Assume [E] not empty. Then there are two regular sets, namely [E] and the 
empty set. There is no other regular open set iff [E] is directed.  *)

Lemma Exercise1_22m: open_r r emptyset.
Proof. 
split.
  split;[fprops | by move=> x y /in_set0].
move => v [sv ov]  [_ ]; rewrite iorder_sr // => h;symmetry;apply /set0_P.
by move=> y yv; move: (h _ yv) => [z /in_set0].
Qed.

Lemma Exercise1_22n: open_r r (substrate r).
Proof.
split.
  split; fprops; move=> x y _ xy; order_tac.
by move=> v [v1 _]  [];rewrite iorder_sr // => h _; apply: extensionality.
Qed.

Lemma Exercise1_22p x: open_r r x -> x = (open_bar r x) .
Proof. 
move=> [osr p3];move: (Exercise1_22g osr) (Exercise1_22i osr).
by move=> p1 [p2a p2b]; apply: (p3 _ p2a p1).
Qed.

Lemma Exercise1_22o: ~ (right_directed r) ->
  exists a b, [/\ open_r r a, open_r r b, nonempty a, nonempty b & a <> b].
Proof. 
move=>  nrd.
pose i x := Zo (substrate r) (gle r x).
have io: (forall x, inc x (substrate r) -> open_o r (i x)).
  move=> x xsr; split; first by apply: Zo_S.
  move => a b /Zo_P [asr xa] ab; apply /Zo_P;split; order_tac.
have obi: (forall x, inc x (substrate r) -> open_r r (open_bar r (i x))).
  by move=> x xsr; apply:  Exercise1_22i =>//; apply: io.
have bne1: forall x, inc x (substrate r) -> inc x (open_bar r (i x)).
  move=> x xsr; apply: Exercise1_22e =>//; [ apply: io => //| apply: Zo_i =>//].
  by order_tac.
pose p a b := [/\ inc a (substrate r),inc b (substrate r) &
    disjoint (i a) (i b)].
case: (p_or_not_p (exists a  b, p a b)). 
  move=> [a [b [asr bsr iabe]]].
  move: (bne1 _ asr) (bne1 _ bsr) => a1 b1.
  exists (open_bar r (i a)); exists (open_bar r (i b)); split;fprops.
      by exists a. 
    by exists b.
  move:  (Exercise1_22k (io _ asr) (io _ bsr) iabe). 
  rewrite /disjoint.
  by move=> ie sv; rewrite sv in ie; empty_tac1 b; apply: setI2_i.
move=> h; case: nrd; apply /right_directedP; split => //.
move=> x y xsr ysr; ex_middle ep; case: h.
exists x, y; split => //.
apply /set0_P;  move=> t /setI2_P [] /Zo_P [tsr xt] /Zo_P [_ yt].
by case: ep; exists t.
Qed.


Lemma Exercise1_22qP:
  (doubletonp (reg_opens r)) <->
  (nonempty (substrate r) /\ (right_directed r)). 
Proof. 
have pa: inc emptyset (reg_opens r).
  apply /Zo_P; split; [apply /setP_P; fprops | apply: Exercise1_22m].
have pb: inc (substrate r) (reg_opens r).
  apply /Zo_P; split; [apply /setP_P; fprops | apply: Exercise1_22n].
split. 
  move=> [a [b [ab sd]]].
  have : (inc a (reg_opens r)) by rewrite sd; fprops.
  have : (inc b (reg_opens r)) by rewrite sd; fprops.
  move /Zo_P => [] /setP_P bsr ob /Zo_P [] /setP_P asr oa.
  split.
    case: (emptyset_dichot a); last by move=> [a' a'a]; exists a'; apply: asr.
    case: (emptyset_dichot b); last by move=> [b' b'b]; exists b'; apply: bsr.
    by move => be ae; case: ab; rewrite ae be.
  ex_middle nrd; move:(Exercise1_22o  nrd) =>[u [v [ou ov neu nev uv]]].
  have uo := reg_opens_i ou.
  have vo := reg_opens_i ov.
  have c2: ~ (inc emptyset (doubleton u v)).
    case/set2_P => h' ;[ case: neu | case: nev];
        move=> y; rewrite -h'; case; case.
  rewrite sd in uo vo pa.
  case/set2_P: uo => vu; case/set2_P:vo => vv;
     try (rewrite -vu in vv; case: uv; fprops);
     case: c2;rewrite vu vv //; rewrite set2_C //.
move=> [ner rdr]; exists emptyset; exists (substrate r); split => //. 
  by move=> esr; rewrite -esr in ner; case /nonemptyP: ner.
set_extens t; last by case/set2_P => ->.
move /Zo_P=> [tse ot]; case: (emptyset_dichot t); first by move => ->; fprops.
move=> [y yt]; apply /set2_P; right; move /setP_P: tse => tse.
apply: extensionality => // u usr.
move: (ot) => [ot1 _]; rewrite (Exercise1_22p ot); apply: Exercise1_22h => //. 
move=> v uv.
have vsr: inc v (substrate r) by order_tac.
move: rdr => /right_directedP [_ h]. 
move: (h _ _ (tse _ yt) vsr) => [z  [zy zv]].
move: ot1 =>[_ ot2]; move: (ot2 _ _ yt zy)=> zt; ex_tac.
Qed.

(** The set of regular open sets is a complete boolean lattice*)

Lemma Exercise1_22rP u v: 
  gle (reg_open_order r) u v <->
  [/\ open_r r u, open_r r v &sub u v].
Proof. 
split; first by move /sub_gleP => [] /Zo_hi pa /Zo_hi pb pc.
by move=> [p1 p2 p3]; apply /sub_gleP => //; split => //; apply:reg_opens_i.
Qed.

Lemma Exercise1_22s1P x:
  inc x (substrate (reg_open_order r)) <-> open_r r x.
Proof. 
rewrite /reg_open_order (proj2 (sub_osr  (reg_opens r))).
split; [ by move /Zo_hi | apply:reg_opens_i ].
Qed.


Lemma Exercise1_22s: greatest (reg_open_order r) (substrate r).
Proof.
move: (Exercise1_22n) => so.
split; first by apply /Exercise1_22s1P.
move=> x => /Exercise1_22s1P ox; move: (proj1 (proj1 ox)) => xsr.
apply /Exercise1_22rP;split; fprops.
Qed.

Lemma Exercise1_22t: least (reg_open_order r) (emptyset).
Proof.
move: (Exercise1_22m) => so.
split; first by apply /Exercise1_22s1P.
move=> x => /Exercise1_22s1P ox; apply /Exercise1_22rP;split;fprops.
Qed.


Lemma Exercise1_22u  u v:
  open_r r u -> open_r r v ->
  inf (reg_open_order r) u v = open_bar r (u \cap v).
Proof. 
move => ou ov.
set (z := open_bar r (u \cap v)). 
have oi: (open_o r (u \cap v)).
  apply: Exercise1_22b => //; move=> x.
  case/set2_P => ->; [by case: ou | by case: ov].
move: (Exercise1_22i oi) (Exercise1_22e oi)=> oz sz.
apply: inf_pr2.
      rewrite/reg_open_order; fprops.
    apply /Exercise1_22rP; split => //; rewrite (Exercise1_22p ou).  
    apply: Exercise1_22j => //; [by case: ou | apply: subsetI2l]. 
  apply Exercise1_22rP; split => //; rewrite (Exercise1_22p ov).  
  apply: Exercise1_22j => //; [by case: ov | apply: subsetI2r]. 
move => t /Exercise1_22rP [ot _ tu] /Exercise1_22rP [_ _ tv]. 
apply /Exercise1_22rP; split => //.
apply: (@sub_trans  (u \cap v)) => //.
by move=> w wt; apply: setI2_i; [apply: tu | apply: tv].
Qed.

Lemma Exercise1_22v X:
  sub X (substrate (reg_open_order r)) -> 
  least_upper_bound (reg_open_order r) X (open_bar r (union X)).
Proof.
move=> Xsr.
have ou: (open_o r (union X)). 
  apply: Exercise1_22c => // x xX; move: (Xsr _ xX) => /Exercise1_22s1P.
  by case.
have oru: (open_r r (open_bar r (union X))) by apply: Exercise1_22i.
have us: (inc (open_bar r (union X))  (substrate (reg_open_order r))).
  by apply /Exercise1_22s1P.
have orr: (order (reg_open_order r)) by rewrite /reg_open_order; fprops.
apply /(lubP orr Xsr);split.
  split => // y yX; move:(Xsr _ yX) => /Exercise1_22s1P oy.
  apply /Exercise1_22rP;split => //; apply: (@sub_trans (union X)).
    by apply: setU_s1.
  apply:  Exercise1_22e => //.
move=> z []  /Exercise1_22s1P oz h; apply /Exercise1_22rP;split => //.
rewrite (Exercise1_22p oz); apply: Exercise1_22j =>//; first by case: oz.
by move => w /setU_P [y wy yX]; move: (h _ yX) => /Exercise1_22rP [_ _]; apply.
Qed.

Lemma Exercise1_22w u v:
  open_r r u -> open_r r v ->
  sup (reg_open_order r) u v = open_bar r (u \cup v).
Proof. 
move=>  ou ov. 
have sd: (sub (doubleton u v) (substrate (reg_open_order r))).
  by move=> t; case/set2_P => ->; apply /Exercise1_22s1P.
symmetry; apply: supremum_pr2; first by rewrite /reg_open_order; fprops.
apply: (Exercise1_22v sd).
Qed.

Lemma Exercise1_22x: complete_lattice (reg_open_order r).
Proof. 
have oro: (order (reg_open_order r)) by rewrite /reg_open_order; fprops.
apply: Exercise1_11b => //.  
move=> X Xsr; exists (open_bar r (union X)); apply: (Exercise1_22v Xsr). 
Qed.

Lemma Exercise1_22y: lattice (reg_open_order r).
Proof.
move: (Exercise1_22x)=> [cl1 cl2].
by split => //u v => usr vsr; apply: cl2; move=> t; case/set2_P => ->.
Qed.
 
Lemma Exercise1_22z: relatively_complemented (reg_open_order r).
Proof. 
move: (Exercise1_22t) => lee.
have oro: (order  (reg_open_order r)) by rewrite /reg_open_order; fprops.
have thel:  (the_least (reg_open_order r) = emptyset).
  by apply: the_least_pr2.
split => //; [by apply: Exercise1_22y | exists emptyset => // |]. 
move=> x y /Exercise1_22rP [ox oy xy].
move: (ox) (oy)=> [oox _] [ooy _].
set (z:= Zo y (fun u => forall t, gle r u t -> ~ (inc t x))).
have zr: (sub z (substrate r)).
   apply: (@sub_trans  y) ;[ apply: Zo_S | by case: (proj1 oy) ].
have oz: (open_o r z).
  split => //;  move=> u v /Zo_P [uy h] uv; apply :Zo_i=> //. 
  move:ooy => [aa h1]; apply: (h1 _ _ uy uv).
  by move=> t vt tx; case: (h _ (order_transitivity or uv vt)).
move: (Exercise1_22i oz)=> orz.
have ou: (open_o r (x \cup (open_bar r z))).
  by apply:  Exercise1_22a =>//; move: orz; move=> [ok _].
exists (open_bar r z); red.
rewrite thel Exercise1_22w //  Exercise1_22u //.
move: (Exercise1_22p ox)(Exercise1_22p oy) => bxp byp.
have xze: (x \cap z) = emptyset.
  apply /set0_P; move=> a /setI2_P [ax] /Zo_P.
  move=> [ay h1]; case: (h1 a) => //; order_tac. 
  by move: (oox) => [xsr _]; apply: xsr.
have zy: sub z y by apply: Zo_S.
split; first (by apply /Exercise1_22s1P); last first.
  rewrite bxp Exercise1_22k // - Exercise1_22p //; apply: Exercise1_22m=>//.
apply: extensionality.
   rewrite byp;apply: Exercise1_22j => //.
   move=> t; case/setU2_P; first by apply: xy.
   rewrite byp; apply: (Exercise1_22j oz ooy zy).
move: ooy=> [ysr ooy2].
move=> t ty; apply: Exercise1_22h  =>//; first by apply: ysr.
move=> u tu.
move: (ooy2 _ _ ty tu) => uy.
case: (p_or_not_p (exists2 t, inc t x & gle r u t)). 
  by move=> [w wx uw]; exists w => //; apply: setU2_1.
move: (ysr _ uy) => usr.
move=> h; exists u => //; last (by order_tac); apply: setU2_2.
apply: Exercise1_22e => //; apply: Zo_i => // w uw; case: (inc_or_not w x) =>//.
by move=> wx; case: h; exists w.
Qed.

Lemma Exercise1_22A: boolean_lattice (reg_open_order r).
Proof. 
move: (Exercise1_22t) => le.
have oo: (order  (reg_open_order r)) by rewrite  /reg_open_order; fprops.
split; first by apply: Exercise1_22z. 
  by  exists (substrate r); apply: (Exercise1_22s).
move: (Exercise1_22y)=> lr. 
apply/ (distributive_lattice_prop3 lr) => x y z xsr ysr zsr.
set (a1:= sup (reg_open_order r) x y).
set (a2:= inf (reg_open_order r) y z).
have a1s: (inc a1 (substrate (reg_open_order r))). 
   move: (lattice_sup_pr lr xsr ysr) => [ok _ _]; order_tac.
have a2s: (inc a2 (substrate (reg_open_order r))). 
   move: (lattice_inf_pr lr ysr zsr) => [ok _ _]; order_tac.
have b1s: inc (inf (reg_open_order r) z a1) (substrate (reg_open_order r)). 
   move: (lattice_inf_pr lr zsr a1s) => [ok _ _]; order_tac.
have b2s: inc (sup (reg_open_order r) x a2) (substrate (reg_open_order r)). 
   move: (lattice_sup_pr lr xsr a2s) => [ok _ _]; order_tac.
move: xsr ysr zsr a1s a2s b1s b2s =>/Exercise1_22s1P
   xor /Exercise1_22s1P yor /Exercise1_22s1P zor /Exercise1_22s1P a1or
    /Exercise1_22s1P a2or  /Exercise1_22s1P b1or  /Exercise1_22s1P b2or.
apply /Exercise1_22rP; split => //.
move: (refl_equal a1)(refl_equal a2); rewrite {2} /a1 {2} /a2.
rewrite  Exercise1_22u // Exercise1_22w// => a1s a2s.
rewrite Exercise1_22u// Exercise1_22w// a1s a2s.
move => a /setU_P [b ab] /Zo_P [] /setP_P bsr [[_ ob]].
move /(cofinal_inducedP bsr) => [bi bip].
move: (bsr _ ab) => asr.
move: (xor)(yor)(zor) => [xo _] [yo _][zo _].
apply: Exercise1_22h => //. 
  apply: Exercise1_22a => //; rewrite -a2s; by case: a2or.
  move=> c ac; move: (ob _ _ ab ac) => cb.
move: (bip _ cb) => [d] /setI2_P [dz dbu] cd.
move: dbu => /setU_P [e de] /Zo_P [] /setP_P esr [[_ oe]].
move  /(cofinal_inducedP esr)=> [ei eip].
move: (eip _ de) => [f fxy ef].
exists f; last by  order_tac.
case/setU2_P: fxy => fx; first by apply: setU2_1.
apply: setU2_2; apply: Exercise1_22e => //.
  by apply: Exercise1_22b => //; move=> i; case/set2_P => ->.
apply: setI2_i => //.
move: zo => [_ zo]; apply: (zo _ _ dz ef).
Qed.

(** if [R(E)] is the set of regular sets, [F] cofinal, then 
[U => intersection2 U F] is an isomorphism [R(E) -> R(F)] *)


Lemma Exercise1_22B F x:
  cofinal r F -> open_r r x -> 
  open_r (induced_order r F) (x \cap F).
Proof.
move=> cf ox.
have sF:  (sub F (substrate r)) by case: cf. 
move: (iorder_osr or sF) => [oio sio].
have oioi: (open_o  (induced_order r F) (x \cap F)).
  red; rewrite iorder_sr //; split; first by apply: subsetI2r. 
  move=> a b /setI2_P [ax aF] ab.
  move: (iorder_gle1 ab)(iorder_gle3 ab) => leab [_ nF]. 
  apply /setI2_P;split => //.
  move: ox => [[_ ox] _]; apply: (ox _ _ ax leab).
split; first by exact.
move=> v ov cfi.
move: (proj1 ov); rewrite iorder_sr // => svF.
move:(proj1 cfi); rewrite iorder_sr // ? iorder_sr // => siv.
apply: extensionality =>// t tv.
move: (ov) => [sov _].
move: sov; rewrite iorder_sr // => sov;move: cfi; rewrite  iorder_trans //.
move /(cofinal_inducedP (sub_trans sov sF)) =>  [_ cfi].
have tF: inc t F by  apply: sov.
move: sov  => /setP_P sov.
move: (sF _ tF) => ts.
apply /setI2_P;split => //.
rewrite (Exercise1_22p  ox); apply: Exercise1_22h => //; first by case: ox.
move => y ty.
have ysr: inc y (substrate r) by order_tac.
move: cf=> [_ cf]; move: (cf _ ysr) => [z zF yz].
have aux: (gle (induced_order r F) t z) by apply /iorder_gle0P => //; order_tac.
move:ov => [_ h]; move: (h _ _ tv aux) => zv.
move: (cfi _ zv)=> [w h1 h2]; move: h1 => /setI2_P [wx wf]; ex_tac; order_tac.
Qed.

Lemma Exercise1_22C F U U':
  cofinal r F -> open_r r U -> open_r r U' -> 
    sub (U \cap F) (U' \cap F) -> sub U U'.
Proof.
move=>  [cf1 cfi] oU oU' sUU'.
move: (oU) => [[sU sU1] _].
move=> t tU; rewrite(Exercise1_22p oU');  apply: Exercise1_22h; fprops.
  by case: oU'.
move=> y ty.
have ysr: (inc y (substrate r)) by order_tac. 
move: (cfi _ ysr) => [z zF yz].
move: (sU1 _ _ tU (order_transitivity or ty yz)) => zU.
have zi: inc z (U' \cap F) by apply:sUU'; apply:setI2_i =>//.
move: (setI2_1 zi) => zU'; ex_tac.
Qed.

End Exercise1_22.

Lemma Exercise1_22D r F:
  order r -> cofinal r F ->
  order_isomorphism (Lf (fun z => z \cap F) (reg_opens r)
    (reg_opens (induced_order r F)))
  (reg_open_order r)(reg_open_order (induced_order r F)).
Proof. 
move=> or cF.
have Fs: (sub F (substrate r)) by move: cF => [ok _].
move: (iorder_osr or Fs) => [].
set (r':=  induced_order r F)=> oir sr'.
have oi: (forall x, open_r r x -> open_r r' (x \cap F)).
  move=> x ox; apply: (Exercise1_22B or cF ox).
have ta: (lf_axiom (fun z => z \cap F) (reg_opens r) (reg_opens r')).
  move=> t => /Zo_P [] /setP_P tsr ot; apply: Zo_i; fprops; apply /setP_P.
  rewrite sr'; apply: subsetI2r.
set (g:=Lf (fun z : Set => z \cap F) (reg_opens r) (reg_opens r')).
have bg: (bijection g).
  rewrite /g; apply: lf_bijective => //.
    move=> u v => /Zo_P [] /setP_P usr ou /Zo_P [] /setP_P vsr  ov si.
    apply: extensionality.
     apply: (Exercise1_22C (U:=u) (U':=v) or cF) => //; rewrite si; fprops.
     apply: (Exercise1_22C (U:=v) (U':=u) or cF) => //; rewrite - si; fprops.
  move=> y  /Zo_P [] /setP_P ysr' oy.
  have ysr: (sub y (substrate r)) by apply: (@sub_trans  F) => //; ue.
  set (x1:= Zo (substrate r) (fun z => exists2 x, inc x y& gle r x z)).
  have x1sr: (sub x1 (substrate r)) by apply: Zo_S.
  have yx1: (sub y x1).
    by move=> t ty; move: (ysr _ ty)=> tsr;apply: Zo_i =>//; ex_tac; order_tac.
  have ox1: (open_o r x1).
  split => // a b /Zo_P [asr [c cy ca]] ab; apply /Zo_P.
    split; [ order_tac | ex_tac; order_tac].
  set (x2:= open_bar r x1). 
  have x2F: (sub y (x2 \cap F)). 
    move=> t ty; apply: setI2_i.
      by apply: (Exercise1_22e or ox1); apply: yx1.
    by rewrite - sr'; apply: ysr'.
  move:(Exercise1_22i or ox1) => ob; exists (open_bar r x1).
     by apply: Zo_i => //; apply /setP_P; apply: Exercise1_22f.
  apply: extensionality => // x /setI2_P  [xb xF].
  rewrite (Exercise1_22p oir oy); apply:Exercise1_22h => //;[by case: oy | ue|].
  move=> z xz; move: (iorder_gle1 xz) => xz1.
  have : (inc z (open_bar r x1)) by move: ob =>[[_ h] _]; apply: (h _ _ xb xz1).
  move /setU_P => [t zt] /Zo_P [] /setP_P tsr [ot]. 
  move /(cofinal_inducedP or tsr) => [x1t x1p].
  move: (x1p _ zt) => [x3 yx3 xy3].
  move: yx3 => /Zo_P [x3s [x4 x4y x4x3]].
  move: cF => [_ cF]; move: (cF _ x3s) => [x5 x5F x35].
  have r45: (gle r' x4 x5).
    apply /iorder_gle0P => //; [ by rewrite - sr'; apply:  ysr' | order_tac].
  exists x5=> //; first by move:oy => [[_ oy] _]; apply: (oy _ _ x4y r45).
  apply /iorder_gle0P => //; [rewrite - sr'; order_tac |  order_tac  ].
rewrite /reg_open_order /g.
split => //; fprops.
  rewrite !(proj2 (sub_osr _)); saw.
hnf; aw;move => x y xsr ysr; rewrite !LfV//; split.
  move /sub_gleP => [i1 i2 i3]; apply /sub_gleP;split; fprops.
  by move=> t /setI2_P [tx tF]; apply/setI2_P;split => //; apply: i3.
move /sub_gleP => [i1 i2 i3]; apply /sub_gleP;split => //.
move:  xsr ysr => /Zo_P  [_ i4] /Zo_P [_ i5].
apply: (Exercise1_22C or cF i4 i5 i3). 
Qed.

(** open sets in a product. This part of the exercise is false  *)

Lemma Exercise1_22E r r' X X': order r -> order r' ->
  open_o r X -> open_o r' X' -> open_o  (order_product2 r r') (X \times X').
Proof. 
move=>  or or' oX oX'; split.
  rewrite order_product2_sr //.
  apply: setX_Slr; [ by case: oX | by case: oX'].
move=> x y xp /order_product2_P; move=> [_ yp [le1 le2]].
move: oX oX' => [_ ox][_ oy].
move: xp yp => /setX_P [px Px Qy] /setX_P [py _ _]; apply /setX_P;split => //.
  apply: (ox _ _ Px le1).
apply: (oy _ _ Qy le2).
Qed.

Lemma Exercise1_22F E X:
    sub X E -> open_r (diagonal E) X.
Proof. 
move=> XE.
move: (diagonal_osr E) => [oi si].
have h:  (forall x y, gle  (diagonal E) x y -> x = y). 
  by move=> x y /diagonal_pi_P  [_].
split. 
  split; [ue |by move=> x y xE xy; rewrite - (h _ _ xy) ].
move=> v [sv ov]  cf; apply: extensionality => //.
move: (proj1 cf); rewrite iorder_sr //.
move=> t tv; move: cf => /(cofinal_inducedP oi  sv) [_ cof].
by move: (cof _ tv)=> [y yX le]; rewrite  (h _ _ le).
Qed.

Lemma Exercise1_22G E:
  let r := diagonal E in
    (order_product2 r r = diagonal (E \times E)).
Proof. 
move=> r.
move: (diagonal_osr E) => [or sr].
have h: (forall x y, gle r x y -> x = y). 
  by move=> x y /diagonal_pi_P [_].
set_extens t.
  move /Zo_P; rewrite sr; move => [ ] /setX_P [pa pb pc] [pd pe]. 
  apply /diagonal_i_P;split => //;move /setX_P: pb => [pf _ _]. 
  move /setX_P: pc => [pg _ _]; apply: pair_exten; fprops.
move /diagonal_i_P => [pt] /setX_P [pa pb pc] pd.
have pf:inc (P t) (E \times E) by apply /setX_P.
have pg: inc (J (P (P t)) (P (Q t))) r by apply /diagonal_pi_P;split => //; ue.
have ph: inc (J (Q (P t)) (Q (Q t))) r by apply /diagonal_pi_P;split => //; ue.
by apply:Zo_i => //; rewrite sr; apply /setX_P; rewrite -pd.
Qed.
 
Lemma Exercise1_22H: exists r, 
  let r' := order_product2 r r in 
    order r /\ (exists2 t, open_o r' t & forall a b, t <> a \times b).
Proof.
move: (Exercise1_22G C2).
set r := diagonal C2 ; move => /= ta.
move: (diagonal_osr C2) => [or sr].
exists r; split => //.
exists ((C2 \times C2) -s1 (J C0 C0)).
  by rewrite ta; apply Exercise1_22F; move => t /setC1_P [].
move => a b eq.
have pa: inc (J C0 C1) (a \times b).
  rewrite - eq; apply /setC1_P; split; first by apply:setXp_i; fprops.
  move =>ba; move: (pr2_def ba); fprops.
have pb: inc (J C1 C0) (a \times b).
    rewrite - eq;  apply /setC1_P; split; first by apply:setXp_i; fprops.
   move =>ba; move: (pr1_def ba); fprops.
move: pa pb => /setXp_P [pa _] /setXp_P [_ pb].
have : inc (J C0 C0) (a \times b) by apply:setXp_i; fprops.
by rewrite -eq => /setC1_P [_].
Qed.

Lemma Exercise1_22I: exists r,   
    let r' := order_product2 r r in 
      let R := reg_open_order r in 
        order r /\ not(reg_open_order r' \Is order_product2 R R).
Proof.
set E := singleton \0c.
move: (Exercise1_22G E) => /=.
move: (diagonal_osr E) => []; set r := diagonal E => od sr h.
exists r; split => //; move => [f [_ _ [bf sf tf] _]].
move: (proj1 (Exercise1_22y od)) => oR.
move: sf tf. 
rewrite order_product2_sr // /reg_open_order (proj2 (sub_osr _)) => sf tf.
have sr0: inc \0c (substrate r) by rewrite sr /E; fprops.
have nef: nonempty (substrate r) by exists \0c.
have rr: right_directed r.
  split => // x y; rewrite sr => /set1_P-> /set1_P ->; exists \0c;split => //.
  by move =>t /set1_P ->; order_tac.
set r' := (order_product2 r r).
have sr': substrate r' = E \times E by rewrite order_product2_sr // sr.
have sr0': inc (J \0c \0c) (substrate r') 
  by rewrite sr' ; apply /setXp_P;split => //; ue.
have see: forall x, inc x (E \times E) -> x = J \0c \0c.
   move => x => /setX_P [ta] /set1_P tb / set1_P tc.
   by rewrite - ta tb tc.
have nef': nonempty (substrate r') by exists  (J \0c \0c).
have or': order r' by apply:  order_product2_or.
have rr': right_directed r'.
  split => // x y; rewrite sr' => xsr ysr; rewrite (see _ xsr) (see _ ysr).
  exists  (J \0c \0c); split => //.
  by move =>t ; case /set2_P => ->; order_tac.
move: (proj2 (Exercise1_22qP od) (conj nef rr)) => [a [b [ab eab]]].
move: (cardinal_set2 ab); rewrite -eab => c1.
move: (f_equal cardinal tf); rewrite - cprod2_pr1.
rewrite (proj2 (sub_osr _)) - cprod2cl - cprod2cr c1.
move: (proj2 (Exercise1_22qP or') (conj nef' rr')) =>  [a' [b' [ab' eab']]].
move: (cardinal_set2 ab'); rewrite -eab';rewrite - sf.
have->: (cardinal (source f) = cardinal (target f)) 
  by apply /card_eqP; exists f;split => //.
move => ->;rewrite cprod_22; exact:(proj2 clt_24).
Qed.



(** ---- Exercise 1.23.
Let [R0(E)] denote the set of non-empty regular open sets of [E]. 
Let [r(x)] the unique open regular set that contains the interval with endpoint 
[x]. This mapping is increasing. Its image is cofinal in [R0(E) ]
 *)

Definition nreg_opens r := 
  (reg_opens r) -s1 emptyset.

Definition nregs_order r :=
  opp_order (sub_order (nreg_opens r)).

Lemma Exercise1_23aP r X:
  inc X (nreg_opens r) <-> (open_r r X /\ nonempty X).
Proof. 
split.
  by move /Zo_P => [] /Zo_hi xe /set1_P xne;split => //; apply /nonemptyP.
move => [pa pb]; apply /Zo_P;split; first by apply reg_opens_i.
by move /set1_P; apply /nonemptyP.
Qed.

Lemma Exercise1_23bP r : order r -> forall X Y,
  (gle (nregs_order r) X Y <->
  [/\ nonempty X, nonempty Y, open_r r X, open_r r Y & sub Y X]).
Proof. 
move=> or X Y; split.
 by move /opp_gleP /sub_gleP => [] /Exercise1_23aP [pa pb]
   /Exercise1_23aP [pc pd] pe.
by move => [pa pb pc pd pe]; apply /opp_gleP /sub_gleP;
  split => //;apply /Exercise1_23aP.
Qed.

Definition canonical_reg_open r x :=
  open_bar r (Zo (substrate r) (fun z => gle r x z)).

Lemma  Exercise1_23c r x: order r ->
  open_o r  (Zo (substrate r) (fun z => gle r x z)).
Proof. 
move=> or; split; first by apply: Zo_S. 
move=> u v => /Zo_P [usr xu] uv; apply /Zo_P;split; order_tac. 
Qed.

Lemma Exercise1_23d1 r x: order r -> inc x (substrate r) ->
  inc x  (canonical_reg_open r x).
Proof. 
move=> or xsr; apply: Exercise1_22e => //; first by apply: Exercise1_23c. 
by apply: Zo_i => //; order_tac.
Qed.

Lemma Exercise1_23d2 r x: order r -> inc x (substrate r) ->
  inc (canonical_reg_open r x) (nreg_opens r).
Proof.
move=> or xsr; apply /Exercise1_23aP; split. 
  move: (Exercise1_23c x or) => aux; apply:  Exercise1_22i => //.
by exists x; apply: Exercise1_23d1.
Qed.

Lemma Exercise1_23e r x y: order r ->
  inc x (substrate r) -> inc y (substrate r) ->
  (inc y (canonical_reg_open r x) <->
    forall z, gle r y z -> exists2 t, gle r z t & gle r x t).
Proof.
move=> or xsr ysr.
rewrite /canonical_reg_open; split. 
  move /setU_P=> [z yz] /Zo_P [] /setP_P zsr [[_ oz]].
  move /(cofinal_inducedP or zsr) => [h1 h2].
  move => t yt; move: (h2 _ (oz _ _ yz yt)) => [v v1 v2].
  by move: v1 => /Zo_hi xv; exists v.
move=> h; apply: Exercise1_22h => //.
   apply: Exercise1_23c => //. 
move=> z yz; move: (h _ yz) => [t zt xt].
exists t => //;apply: Zo_i=> //; order_tac.
Qed.

Lemma Exercise1_23f r x y: order r ->
  gle r x y -> gle (nregs_order r)  
  (canonical_reg_open r x)  (canonical_reg_open r y).
Proof. 
move=> or xy.
have xsr: (inc x (substrate r)) by order_tac. 
have ysr: (inc y (substrate r)) by order_tac. 
move: (Exercise1_23d2 or xsr) (Exercise1_23d2 or ysr) => s1 s2.
apply /opp_gleP /sub_gleP;split => //. 
apply: Exercise1_22j; (try apply: Exercise1_23c) => //.
move=> t => /Zo_P [tsr yt]; apply /Zo_i => //; order_tac.
Qed.


Lemma  Exercise1_23g r: order r ->
  cofinal (nregs_order r) 
   (fun_image (substrate r) (canonical_reg_open r)).
Proof.
move=> or; red.
move:(sub_osr (nreg_opens r)) => [pr1 pr2].
have ->:(substrate (nregs_order r) = nreg_opens r).
  by rewrite /nregs_order (proj2 (opp_osr pr1)).
split.
  move=> t /funI_P [z zsr] ->; apply: Exercise1_23d2 => //. 
move=> x /Exercise1_23aP [ox [y yx]].
have ysr: inc y (substrate r) by move: ox => [[xsr _] _]; apply: xsr.  
move: (Exercise1_23d2 or ysr) => /Exercise1_23aP [p1 p2].
exists  (canonical_reg_open r y); first by apply /funI_P;exists y.
apply /Exercise1_23bP=> //; split => //; first by exists y. 
move: (ox) => [ox1 _].
rewrite /canonical_reg_open (Exercise1_22p or ox);apply: Exercise1_22j => //.
  apply: Exercise1_23c => //. 
move=> t /Zo_hi yt; move: ox1 => [_ h]; apply: (h _ _ yx yt).
Qed.


(** Antidirected means that [canonical_reg_open] is injective; We give an equivalent condition *)

Definition anti_directed r:=
    {inc (substrate r) &, injective (canonical_reg_open r) }.

Lemma  Exercise1_23hP r: order r ->
  let aux := (fun x y => forall z, gle r x z -> gle r y z -> False) in 
  (anti_directed r) <->
  ((forall x y, glt r x y -> exists2 z, glt r x z & aux y z)
    /\ forall x y, inc x (substrate r) -> inc y (substrate r) ->
     [\/ gle r x y, gle r y x, (exists2 x', gle r x x' & aux x' y) |
        (exists2 y', gle r y y' & aux x y')]).
Proof. 
move=> or aux.
have p1: (forall x y, inc x (substrate r) -> inc y (substrate r) ->
  (inc y  (canonical_reg_open r x) <-> forall z, gle r y z -> ~ (aux x z))).
  move=> x y xsr ysr; apply: (iff_trans (Exercise1_23e or xsr ysr)); split.
    move=> h z yz h1;  move: (h _ yz)=> [t zt xt]; apply: (h1 _  xt zt).
  move=> h z yz; move: (h _ yz) => h1;ex_middle h2; case: h1.
  by move=> t xt zt; case: h2; exists t.
have Hb:forall x y, gle r x y ->
    sub  (canonical_reg_open r y) (canonical_reg_open r x).
  move=> x y xy; move: (Exercise1_23f or xy) => /(Exercise1_23bP or).
  by move => [_ _ _].
have Hc:forall x y, aux x y -> aux y x. 
  move => x y h z s1 s2; apply: (h _ s2 s1).
split; last first.
  move=> [C1 C2] x y xsr ysr cxy; ex_middle nxy.
  have xc: (inc x (canonical_reg_open r x)) by apply: Exercise1_23d1. 
  have yc: (inc y (canonical_reg_open r y)) by apply: Exercise1_23d1.
  case: (C2 _ _ xsr ysr) => c2p.
  + have ltxy: glt r x y by split.
    move: (C1 _ _ ltxy) => [z [xz _] yz].  
    by move: xc; rewrite cxy => /(p1 _ _ ysr xsr) h; case: (h _ xz).
  + have ltxy: glt r y x by split => //; apply:nesym.
    move: (C1 _ _ ltxy) => [z [xz _] yz].
    by move: yc; rewrite - cxy => /(p1 _ _ xsr ysr) h; case: (h _ xz).
  + case: c2p=> [t xt ty].
    by move: xc; rewrite cxy => /(p1 _ _ ysr xsr) h; case: (h _ xt); apply: Hc.
  + case: c2p=> [t xt ty].
    by move: yc; rewrite - cxy=> /(p1 _ _ xsr ysr) h; case: (h _ xt). 
move=> adr.
have p2: (forall x y,  inc x (substrate r) ->  inc y (substrate r) ->
    (sub (canonical_reg_open r x) (canonical_reg_open r y)
    \/ (exists2 x', gle r x x' & aux x' y))).
  move=> x y xsr ysr.
  case: (p_or_not_p (exists2 x', gle r x x' & aux x' y)); first by right.
  move=> ne; left.
  move: (Exercise1_23d2 or ysr) => /Exercise1_23aP [o1 ne1].
  rewrite(Exercise1_22p or o1); apply: Exercise1_22j => //.
      by apply: Exercise1_23c. 
    by case: o1.
  move=> t /Zo_P [tsr xt].
  apply/ (p1 _ _ ysr tsr) => z tz; case: (p_or_not_p (aux y z)) => // ayt. 
  by case: ne; exists z; fprops; order_tac.
suff:(forall x y : Set, glt r x y -> exists2 z, glt r x z & aux y z).
  move=> hs; split => // x y xsr ysr.
  case: (p_or_not_p (gle r x y)) => lexy; first by constructor 1.
  case: (p_or_not_p (gle r y x)) => leyx; first by constructor 2.
  case: (p2 _ _ xsr ysr) => q1.
     case: (p2 _ _ ysr xsr)=> q2.
      by case: lexy; rewrite (adr _ _ xsr ysr (extensionality q1 q2));order_tac.
     by constructor 4; move: q2 => [t t1 t2]; exists t => //; apply: Hc.
   by constructor 3; move: q1 => [t t1 t2]; exists t.
move=> x y [xy nxy].
have xsr:(inc x (substrate r)) by order_tac.
have ysr:(inc y (substrate r)) by order_tac.
case: (p2 _ _ xsr ysr) => h.
  move: (Exercise1_23f or xy) => /(Exercise1_23bP or) [_ _ _ _ h'].
  by  case: nxy; rewrite (adr _ _ xsr ysr (extensionality h h')).
move: h => [u xyu uy]; exists u; fprops;split => // xu.
by case: (uy y); [ ue | order_tac].
Qed.

(** The set [set_of_nreg_order] is antidirected *)

Lemma Exercise1_23i r x y: order r ->
  inc x y -> inc y  (nreg_opens r) ->
    gle (nregs_order r) y (canonical_reg_open r x).
Proof.
move=> or xy.
move /Exercise1_23aP => [h1 h2].
have ysr: (sub y (substrate r)) by move: h1 => [[ ok _] _].
move: (Exercise1_23d2 or (ysr _ xy)) => /Exercise1_23aP [h3 h4].
apply  /(Exercise1_23bP or); split => //.
rewrite (Exercise1_22p or h1). 
apply: (Exercise1_22j or (Exercise1_23c x or) (proj1 h1))=> t /Zo_P [tsr xt].
move: h1 => [[_ h] _]; apply: (h _ _ xy xt).
Qed.

Lemma Exercise1_23j r: order r ->
  let r':= nregs_order r in 
    (forall x y, inc x (substrate r') -> inc y (substrate r') ->
      ( (forall z, gle r' x z ->  gle r' y z -> False) <->
        (disjoint  x y))).
Proof. 
move=> or r' x y xsr' ysr'.
move:(sub_osr (nreg_opens r)) => [pr1 pr2].
move: (opp_osr pr1) => [or' prb].
have sr': (substrate r' = nreg_opens r) by rewrite /r' prb pr2.
rewrite /r'/nregs_order; aww.
split. 
  move=> h; apply: disjoint_pr=> u ux uy.
  rewrite sr' in xsr' ysr'.
  exact (h _ (Exercise1_23i or ux xsr') (Exercise1_23i or uy ysr')). 
rewrite /disjoint=> di z => /(Exercise1_23bP or) [_ [t tz] _ _ zx]
 /(Exercise1_23bP or) [_ _ _ _ zy].
empty_tac1 t; apply: setI2_i. 
Qed.

Lemma Exercise1_23k r: order r ->
  anti_directed (nregs_order r).
Proof. 
move=> or.
move:(sub_osr (nreg_opens r)) =>[pa pb].
set (r':= nregs_order r).
move: (opp_osr pa) => [or' prb].
have sr': (substrate r' = nreg_opens r) by rewrite /r' prb.
set (aux:=(fun x y => forall z, gle r' x z ->  gle r' y z -> False)).
have p1: (forall x y, inc x (substrate r') -> inc y (substrate r') ->
    (disjoint  x y) -> aux x y). 
  by move=> x y xsr' ysr' dxy; rewrite /aux /r' Exercise1_23j // pr2.
have Hv:substrate r' = nreg_opens  r.
   rewrite /r' /nregs_order; aww; ue.
set (i := fun x y => open_bar r
    (Zo x (fun u => forall t, gle r u t -> ~ (inc t y)))).
have p2: (forall x y,  inc x (substrate r') -> inc y (substrate r') ->
   [/\ open_r r (i x y), sub (i x y) x, disjoint (i x y) y &
    (i x y = emptyset -> sub x y)]). 
  move=> x y xsr' ysr'.
  set (z:= Zo x (fun u => forall t, gle r u t -> ~ (inc t y))).
  have zx: sub z x by apply: Zo_S.
  move: xsr' ysr';rewrite Hv=> /Exercise1_23aP [ox nex]/Exercise1_23aP [oy ney].
  move: (ox)(oy) => [[xsr xop] _] [oy1 _].
  have zsr: (sub z (substrate r)) by apply: (@sub_trans  x).
  have oz: (open_o r z).
    split => // u v /Zo_P [ux xp] uv; apply /Zo_P;split.
      apply: (xop _ _ ux uv).
    move => t vt; apply: (xp _ (order_transitivity or uv vt)).
  move: (Exercise1_22i or oz) => oi; rewrite /i -/z; split => //.
      rewrite(Exercise1_22p or  ox); apply: Exercise1_22j => //. 
    rewrite/disjoint (Exercise1_22p or oy); apply: Exercise1_22k => //. 
    apply /set0_P => u /setI2_P [] /Zo_P [ux p] uy.
    by case: (p u) => //; order_tac; apply: xsr.
  move=> bze t tx.
  rewrite(Exercise1_22p or oy); apply: (Exercise1_22h or oy1 (xsr _ tx)).
  move=> u ut; move: (xop _ _ tx ut)=> ux.
  ex_middle ep; empty_tac1 u; apply: Exercise1_22e => //. 
  apply: Zo_i => // v uv.
  by case: (inc_or_not v y)=> // vy; case: ep; exists v.
have p3: (forall x y, inc x (substrate r') -> inc y (substrate r') ->
    (inc (i x y) (substrate r') \/ sub x y)). 
  move=> x y xsr' ysr';move:  (p2 _ _ xsr' ysr') => [oi si di ai].
  rewrite Hv; case: (emptyset_dichot (i x y)) => ei; first by right; apply: ai.
  by left; apply /Exercise1_23aP.
apply /(Exercise1_23hP or'); split.
  move=> x y xy.
  have xsr': (inc x (substrate r')) by order_tac. 
  have ysr': (inc y (substrate r')) by order_tac. 
  move: xy=> [] /(Exercise1_23bP or) [nex ney ox oy yx] xy.
  case: (p3 _ _ xsr' ysr') => p3c; last by case: xy; apply: extensionality. 
  move: (p2 _ _ xsr' ysr')=> [oi si di ai].
  exists  (i x y); first split. 
  + apply /Exercise1_23bP => //; split => //.
    by move: p3c;rewrite  Hv => /Exercise1_23aP [].
  + move=> xi; red in di;move: ney => [t ty]; empty_tac1 t.
    apply: setI2_i=> //; ue.
  + move: (disjoint_S di) => di'; apply: (p1 _ _ ysr' p3c di').
  move=> x y xsr' ysr'.
move: (xsr')(ysr') ; rewrite Hv => /Exercise1_23aP  [ox nex] 
  /Exercise1_23aP[oy ney].
case: (p3 _ _ xsr' ysr') => p3c; last by constructor 2; apply /Exercise1_23bP.
move: (p3c); rewrite Hv => /Exercise1_23aP [oi nei].
move: (p2 _ _ xsr' ysr')=> [oi2 si di ai].
constructor 3; exists  (i x y); last by apply: p1.
by  apply /Exercise1_23bP.
Qed.

(** Bourbaki says that the mapping is  [R0(E) -> R0(R0(E))] bijective.
   Injectivity has been proved above. We do not know how to prove surjectivity*)

Lemma Exercise1_23l r y: order r ->
  let r' := nregs_order r in
    inc y (nreg_opens r') ->
    exists ! x, (inc x (nreg_opens r) /\ 
      y =  canonical_reg_open r' x).
Proof. 
move=> or r' ys.
set (E:=nreg_opens r). 
set (E':=nreg_opens r').
move:(sub_osr (nreg_opens r)) =>[pa pb].
move: (opp_osr pa) => [or' prb].
have sr': (substrate r' = nreg_opens r) by rewrite /r' prb.
have se: (E = substrate r') by ue.
apply /unique_existence;split; last first.
  move => u v [uE up][vE vp]; apply: (Exercise1_23k or).
     by rewrite - se.
  by rewrite - se. 
ue.
have p1: (forall x t, inc x E -> inc t E -> (inc t (canonical_reg_open r' x) <->
    (forall u, gle r' t u -> nonempty (u \cap x)))).
  move=> x t xE tE; move: (xE) (tE); rewrite se => xs ts.
  apply:(iff_trans (Exercise1_23e or' xs ts)); split.
    move=> h u tu; move: (h _ tu) => [v].
     move /(Exercise1_23bP or)=> [_ [w wv] _ _ vu]
          /(Exercise1_23bP or)  [_ _ _ _ vx].
    by exists w; apply: setI2_i; [apply: vu  | apply: vx].
  move=> h z zx; move: (h _ zx) => [w] /setI2_P [wz wx].
  have zs: (inc z (substrate r')) by  order_tac. 
  rewrite - se in zs; move:  (Exercise1_23i or wx xE) => le1.
  move:  (Exercise1_23i or wz zs) => le2.
  by exists (canonical_reg_open r w).
have p2: (forall x t, inc x E -> inc t E -> (inc t (canonical_reg_open r' x) <->
    (forall a, inc a t -> (exists2 b, inc b x & gle r a b)))).
  move=> x t xE tE; rewrite p1 //; split.
    move => h a iat; move: (h _ (Exercise1_23i or iat tE)) => [u us].
    move: xE =>/Exercise1_23aP [xo [w wx]].
    move: us => /setI2_P;rewrite /canonical_reg_open (Exercise1_22p or xo).  
    set z:= Zo _ _; case: (emptyset_dichot (z \cap x)) => ie.
      move: (xo) => [xo1 _]  [h1 h2].
      move:(Exercise1_22k or  (Exercise1_23c a or) xo1 ie) => ie2.
      case: (in_set0 (x:= u)); rewrite -ie2; apply/setI2_P; split => //.
    move: ie => [v] /setI2_P [] /Zo_P [vsr le1] vx _.
    by exists v => //; apply:  Exercise1_22e => //; case: xo.
  move=> h u => /(Exercise1_23bP or) [_ [b bu] ot ou ut].
  move: (h _ (ut _ bu)) => [c cx bc]; exists c; apply: setI2_i =>//.
  move: ou => [[_ ou] _]; apply: (ou _ _ bu bc).
have p3: (forall x t, nonempty x -> open_o r x -> inc t E -> 
    (inc t (canonical_reg_open r' (open_bar r x)) <->
    (forall a, inc a t -> (exists2 b, inc b x & gle r a b)))).
  move=> x t [z zx] o tE.
   have bE: (inc (open_bar r x) E).
      apply /Exercise1_23aP; split => //; first by apply:  Exercise1_22i => //. 
     exists z; apply:  Exercise1_22e => //. 
  rewrite (p2 _ _ bE tE); split.
    move=> h a ait; move: (h _ ait) => [c cb ac].  
    move: cb => /setU_P [d cd] /Zo_P [] /setP_P dsr [od].
    move =>/(cofinal_inducedP or dsr)  [xd h'].
   move: (h' _ cd) => [e ex ey]; ex_tac; order_tac.
  move=> h a ait; move: (h _ ait) => [b bx ab].
  exists b => //; apply:  Exercise1_22e => //.
have Hu:forall x, inc x y -> open_r r x. 
  move=> x xy; move: ys => /Exercise1_23aP [[[q1 q2] q3] ney].
  by move: (q1 _ xy); rewrite - se => /Exercise1_23aP [].
have Hv: (sub (union y) (substrate r)). 
   move=> t /setU_P [x tx xy]; move: (Hu _ xy)=> [[h _] _]; by apply: h. 
have Hw: (open_o r (union y)).
  by apply: Exercise1_22c=> //; move=> x xy; case: (Hu _ xy). 
set (T:=Zo E (fun z => forall a, inc a z -> exists2 b, 
    inc b (union y) & gle r a b)).
set (y':= canonical_reg_open r' (open_bar r (union y))).
have neuy: (nonempty (union y)). 
  move: ys => /Exercise1_23aP [[[q1 q2] q3] ney].
  move: ney => [z zy]; move: (q1 _ zy); rewrite - se => /Exercise1_23aP.
  move => [_ [t tz]]; exists t; union_tac.
have Hx :inc (open_bar r (union y)) E.
  apply /Exercise1_23aP; split; first by apply: Exercise1_22i =>//. 
  by move: neuy => [t tu]; exists t; apply:  Exercise1_22e. 
have Ty: (T = y').  
  suff: (forall t, inc t E -> (inc t T <-> inc t y')). 
    have p4: sub y' E.
      have p5: (inc  (open_bar r (union y)) (substrate r')) by rewrite - se. 
      move: (Exercise1_23d2 or' p5) => /Zo_P [ ] /Zo_P [] /setP_P.
      by rewrite se -/y'.
    move=> tp; set_extens t => ts. 
      by rewrite -tp //; move: ts => /Zo_P [].
    by rewrite  tp //; apply: p4.
  move=> t tE; rewrite /y'; rewrite (p3 _ _ neuy Hw tE). 
  split; first by move => /Zo_P [].
  by move => h; apply: Zo_i.
have syy': (sub y y').  
  move: ys  =>/Exercise1_23aP [[[q1 _] _] _].
  move=> t ty;rewrite -Ty; apply: Zo_i; first by rewrite se; apply: q1.
  move=> a ait; have au: (inc a (union y)) by union_tac.
   ex_tac; order_tac. 
  by move: (q1 _ ty); rewrite - se =>/Exercise1_23aP [[[h _] _] _]; apply: h.
have oy': open_o r' y'.  
   rewrite /y'; rewrite se in Hx.
   move: (Exercise1_23d2 or' Hx) => /Exercise1_23aP. 
   by move=> [[oo _] _].
have cf: substrate (induced_order r' y') = y'.
   rewrite iorder_sr // - se -Ty; apply: Zo_S.
(* 
  set (T:= intersection(Zo (\Po (substrate r)) 
    (fun x => open_o r x /\ forall a, inc a (union y) -> exists b,
      inc b x /\ gle r a b))).
  assert (open_o r T). uf T. apply: Exercise1_22b. exists (union y). Ztac.
  apply: powerset_inc. split. apply: Exercise1_22c. ir. nin (Hu _ H7). am.
  ir. exists a. split. am. order_tac. apply: H6. ir. Ztac. nin H9; am.
*)
Abort.

(** ---- Exercise 1.24: branched sets *)

Definition branched r :=
  order r /\ (forall x, inc x (substrate r) -> 
    exists y  z, [/\ gle r x y, gle r x z &
      (forall t, gle r y t -> gle r z t -> False)]).
    
(** An antidirected set with no maximal element is branched *)

Lemma Exercise1_24a r: 
  order r -> anti_directed r ->  
  (forall x, inc x (substrate r) -> ~ maximal r x) ->
  branched r.
Proof. 
move=> or ar nm; split => // x xsr.
move: ar => /(Exercise1_23hP or) [ar1 ar2].
move: (nm _ xsr)=> xnm.
have [y xy]: (exists y, glt r x y).  
  ex_middle xy; case: xnm;split => //.
  by move=> z xz; symmetry;ex_middle exz; case: xy; exists  z.
move: (ar1 _ _ xy) => [z xz h].
by move: xy xz => [xy _][ xz _]; exists y; exists z.
Qed.


(** a product is branched *)

Lemma Exercise1_24e r r': branched r -> order r' ->
  branched (order_product2 r r').
Proof.
move=>  [or bc] or'; split.
  apply: order_product2_or => //.
move: (order_product2_sr or or') => sp.
rewrite sp; move=> x xp.
move: (xp) => /setX_P [px Px Qx].
move: (bc _ Px)=> [y [z [xy xz etc]]].
set s:= ((substrate r) \times (substrate r')).
set y1 := J y (Q x);set z1 := J z (Q x).
have y1sr: inc y1 s by rewrite /y1; apply /setX_P; split;aww;order_tac.
have z1sr: inc z1 s by rewrite /s /z1; apply /setX_P; split;aww;order_tac.
have leqa: gle r' (Q x) (Q x) by order_tac.
exists y1; exists z1; split => //. 
    by apply/order_product2_P;split => //; rewrite /y1; aw.
  by apply/order_product2_P;split => //; rewrite /z1; aw.
move=> t /order_product2_P [_ _ [q1 _]] /order_product2_P [_ _ [q2 _]]. 
move: q1 q2; rewrite /y1/z1; aw; apply: etc.
Qed.

(** Bourbaki says: the product of [ Qpairi_o] and a well-orderd [r'] that has no 
 countable cofinal subset has no antidirected cofinal subset.
This is an attempt of a proof (but a part of the assumptions is missing *) 


(** Bourbaki says: Note that an ordinal sum  contains a cofinal subset
 isomorphic to E; this seems to be wrong. 
Bourbaki deduces that there exists a set that is not antidirected but has an
antidirected  cofinal subset ?? 
 *)

Lemma Exercise1_24g r g: orsum_ax r g -> orsum_ax2 g ->
   anti_directed r ->
   let R := order_sum r g in
     exists X, [/\ sub X (substrate R), cofinal R X &
       anti_directed (induced_order R X)].
Proof.
move=> osa alne ar R.
pose f i := J (rep (substrate (Vg g i))) i.
have oR: order R by rewrite /R; fprops.
have p1: forall i, inc i (domain g) -> inc (f i) (substrate R).
  move=> i idg; rewrite orsum_sr //; apply: disjoint_union_pi1=> //. 
  apply: rep_i; apply: (alne _ idg).
set X:= fun_image  (domain g) f.
have Xsr: sub X (substrate R).
  move=> t /funI_P [z zdf ->]; exact (p1 _ zdf).
exists X; split => //.
  split => //x; rewrite  orsum_sr //.
Abort.

(* unused *)
Lemma nth_set11 K a (f:= nth_elt K)(g:= nth_elt (K +s1 a)) (q:= cardinal K) :  
  sub K Nat -> finite_set K -> natp a ->
  (forall i, inc i K -> i <c a) ->
  (forall i, i<c q -> f i = g i) /\ g q = a.
Proof. 
move => KN fsK aN Ha.
have anK: ~ inc a K by move => /Ha [].
move:(csucc_pr anK); set q1:= cardinal (K +s1 a);rewrite -/q => qv.
have K1N: sub (K +s1 a) Nat by move => t /setU1_P; case; [apply: KN | move ->].
have qN: natp q by apply /NatP.
have q1N: natp q1 by rewrite  qv; fprops.
move:(nth_set6 qN KN) (nth_set6 q1N K1N); rewrite -/q -/q1 qv => sa sb.
suff aux: forall i, i<=c q -> nth_elts K i = nth_elts (K +s1 a) i.
  rewrite /f/g /nth_elt.
  split. 
    move => i liq. 
    move/(cleSltP  (NS_lt_nat liq qN)): (liq) => /aux ->.
    by rewrite (aux _ (proj1 liq)).
  have hb: ((K +s1 a) -s K)  = singleton a.
    apply:set1_pr; first by apply/setC_P; split; fprops.
    by move => z /setC_P [/setU1_P ha hb]; case: ha.
  by rewrite - (aux _ (cleR (CS_nat qN))) sb sa hb setU_1.
move => i ilq; move:(NS_le_nat ilq qN) => iN.
move: i iN ilq; apply: Nat_induction.
   by rewrite /nth_elts !induction_term0.
move => n nN Hrec sc.
rewrite (nth_elts_succ _ nN) (nth_elts_succ _ nN).
have lenk:=(cleT (cleS nN) sc).
rewrite - (Hrec lenk).
move:(nth_set5 nN KN lenk) => [[]].
rewrite /nth_more; set S1 := (nth_elts K n) => ha hb hc.
have s1: sub (K -s S1) Nat by move => t /setC_P [/KN].
have s2: sub ((K +s1 a) -s S1) Nat by move => t /setC_P [/K1N].
case:(emptyset_dichot (K -s S1)) => ne1.
  move:(cardinal_setC4 ha fsK); rewrite - /q hc ne1 cardinal_set0.
  by move: (nesym (cdiff_nz (clt_leT (cltS nN) sc))). 
have ne2: nonempty ((K +s1 a) -s S1).
   by exists a; apply/setC_P; split; [ fprops | move/ha].
move:(inf_Nat s1 ne1); set y1:= intersection _; move => [/setC_P[hu hv] pb].
move:(inf_Nat s2 ne2); set y2:= intersection _; move => [pa' pb'].
apply: f_equal; apply:f_equal.
have /pb' y21: inc y1 ((K +s1 a) -s S1) by apply/setC_P; split; fprops.
move/setC_P:pa' => [/setU1_P hu1 hv1]; case: hu1=> hu1.
  by move/(setC_P): (conj hu1 hv1) => /pb le1; apply:cleA.
by move:(Ha _ hu); rewrite - hu1 => /(cleNgt y21).
Qed.

End  Exercise2.

Export  Exercise2.
