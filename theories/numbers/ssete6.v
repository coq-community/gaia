(** * Theory of Sets : Exercises sections 6 
  Copyright INRIA (2012-2018) Marelle Team (Jose Grimm). 

$Id: ssete6.v,v 1.31 2018/10/01 14:40:54 grimm Exp $
*)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype.
From gaia Require Export sset15 ssete2 ssete3 ssetq2.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module Exercise6.

Definition csup_s A := \csup (fun_image A cnext). 

Lemma csup_s1 A (x := csup_s A): cardinal_set A ->
  (forall y, inc y A -> y <c x).
Proof.
move => csa y yA.
apply /(cnext_pr5P (csa _ yA)); apply: card_sup_ub.
  move => t /funI_P [z za ->]; exact: (CS_cnext (csa _ za)).
by apply /funI_P; ex_tac.
Qed.

Lemma csup_s2 A z: cardinal_set A -> cardinalp z ->
  (forall y, inc y A -> y <c z) -> csup_s A <=c z.
Proof.
move => csa cz h2; apply: card_ub_sup => //.
move => i /funI_P [t /h2 tA ->]; apply /cnext_pr5P => //; exact: (proj31_1 tA).
Qed.

Definition disjointness_degree F :=
  csup_s (fun_image (coarse F -s diagonal F) 
       (fun z => cardinal ((P z) \cap (Q z)))).

Lemma dd_pr1 F x y: inc x F -> inc y F -> x <> y ->
  cardinal (x \cap y) <c  (disjointness_degree F).
Proof.
move => xF yF xy; apply: csup_s1.
  move=> t /funI_P [z _ ->]; fprops.
apply /funI_P; exists (J x y); last by aw.
by apply /setC_P;split; [apply :setXp_i | case /diagonal_pi_P].
Qed.

Lemma dd_pr2 F z: cardinalp z ->
  (forall x y, inc x F -> inc y F -> x <> y ->
     cardinal (x \cap y) <c z)
  -> (disjointness_degree F) <=c z.
Proof.
move => cz h; apply:csup_s2 => //.
  move=> t /funI_P [u _ ->]; fprops.
move => y /funI_P [t /setC_P [/setX_P [pt Pt Qt] pb ->]]; apply: h => //. 
by dneg h; apply /diagonal_i_P.
Qed.

Lemma dd_pr3 F : (disjointness_degree F = \0c) <-> small_set F.
Proof.
split => h.
   move => x y fx fy; ex_middle xy.
   by move: (dd_pr1 fx fy xy); rewrite h => /clt0.
by apply: cle0; apply: (dd_pr2 CS0) => x y xf yf; move: (h _ _ xf yf). 
Qed.

Lemma dd_pr4 F : (disjointness_degree F = \1c) <-> 
  (~ small_set F /\ disjoint_set F).
Proof.
split => h.
  split; first by move /dd_pr3; rewrite h; fprops.
  move => x y xf yf; case: (equal_or_not x y); first by left.
  move => xny; move: (dd_pr1 xf yf xny); rewrite h.
  by move /clt1 /card_nonempty; right.
move: h => [/dd_pr3 dn0 h1];
have /cle_eqVlt: disjointness_degree F <=c \1c. 
   apply: (dd_pr2 CS1) => x y xF yF; case: (h1 _ _ xF yF) => // -> _.
   rewrite cardinal_set0 ; exact: clt_01.
by case => // /clt1.  
Qed.


(* ---- Exercise 6.25 *)



(** -- Exercise 5.7 *)


(* --------- *)

Definition Noetherian r :=
  (forall X, sub X (substrate r) -> nonempty X ->
    exists a,  maximal (induced_order r X) a).

Definition Noetherian_set r x:=
   sub x (substrate r) /\ Noetherian (induced_order r x).


Lemma Noetherian_set_pr r x: order r -> sub x (substrate r) ->
   (Noetherian_set r x <->
   (forall X, sub X x -> nonempty X ->
    exists2 a, inc a X & (forall x, inc x X -> gle r a x -> x = a))).
Proof.
move => or xsr; rewrite /Noetherian_set /Noetherian.
rewrite (iorder_sr or xsr); split.
  move => [_ h] X Xx xne; move: (h _ Xx xne);rewrite (iorder_trans _ Xx).
  move=> [a []]; rewrite (iorder_sr or (sub_trans Xx xsr)) => ax ap.
  by ex_tac; move => t tX lat; apply: ap; apply /iorder_gleP.
move => h; split; first  exact.
move => X Xx ne; rewrite (iorder_trans _ Xx); move: (h _ Xx ne) => [a ax ap].
exists a; split; first by rewrite (iorder_sr or (sub_trans Xx xsr)).
by move => b => /iorder_gleP  [_ bx ab]; apply: ap.
Qed.

Lemma Exercise6_29a r: order r ->  
  Noetherian r ->  Noetherian_set r (substrate r).
Proof. 
move => or nr; split; [fprops | by rewrite  iorder_substrate ].
Qed.

Lemma Exercise6_29b r:  Noetherian_set r emptyset.
Proof.
split; fprops. 
move => X xns [w wx]; move: (xns _ wx).
have ->: (induced_order r emptyset) = emptyset.
  by apply /set0_P => y /setI2_P [_]/setX_P [_ /in_set0]. 
by rewrite /substrate domain_set0 range_set0 setU2_id => /in_set0.
Qed.

Lemma Exercise6_29c r a b: order r ->
  Noetherian_set r a -> Noetherian_set r b -> Noetherian_set r (a \cup b).
Proof.
move => or pa pb.
move: (proj1 pa)  (proj1 pb) =>  asr bsr.
move/(Noetherian_set_pr or asr):pa => pa.
move /(Noetherian_set_pr or bsr):pb => pb.
have usr: sub (a \cup b) (substrate r)
  by move=> t; case /setU2_P; [apply asr | apply: bsr].
apply/ (Noetherian_set_pr or usr).
move => X Xu neX.
set Xa:=  X \cap a.
case: (emptyset_dichot Xa) => Xane.
  have sb: sub X b.
    move => t tX; move: (Xu  _ tX); case /setU2_P => // ta.
    by empty_tac1 t; apply /setI2_P.
  by apply: pb.
have sxa: sub Xa a by apply: subsetI2r.
move: (pa _ sxa Xane) => [ea sea eap].
set Xb:= Zo X (fun t => glt r ea t).
case: (emptyset_dichot Xb) => Xbne.
  have eax: inc ea X by move: sea;move /setI2_P=> [].
  exists ea => //; move => x xE le1; ex_middle ne.
  by empty_tac1 x; apply: Zo_i => //;split => //; apply:nesym.
have sxb: sub Xb b.
  move => t /Zo_P [tx [le1 ne1]].
  move: (Xu _ tx);case /setU2_P=> // ta.
  have txa: inc t Xa by rewrite /Xa; fprops.
  by move: (eap _ txa le1) =>eq1; case: ne1.
move: (pb _ sxb Xbne) => [eb seb ebp].
have ebx: inc eb X by move: seb => /Zo_P [].
exists eb => //; move => x xE le1.
apply: ebp => //; apply: Zo_i => //.
move: seb => /Zo_P [_ lt1]; order_tac.
Qed.

Lemma Exercise6_29d r X: order r ->
  finite_set X -> 
  (forall x, inc x X -> Noetherian_set r x) ->
  Noetherian_set r (union X).
Proof.
move => or; move: X.
apply: (finite_set_induction).
  move => _; rewrite setU_0; apply: Exercise6_29b.
move => a n Hrec aux.
have ->: union (a +s1 n) = (union a) \cup n. 
  set_extens t.
    move => /setU_P [y ty] /setU1_P;
       case => h; apply /setU2_P; [ left;union_tac | right; ue].
  case /setU2_P.
      move /setU_P=> [y ty ya]; union_tac. 
  by move => tn; apply /setU_P;exists n;fprops.
apply: (Exercise6_29c or); last by apply: aux; fprops.
apply: Hrec=> x xa; apply: aux; fprops.
Qed.


Lemma Exercise6_29e r X: order r -> Noetherian r ->
  sub X (substrate r) ->  Noetherian_set r X.
Proof.
move => or Nr xsr.
rewrite (Noetherian_set_pr or xsr) => Y YX neY.
move: (sub_trans YX xsr) => Ysr.
move: (Nr _ Ysr neY) => [a []]. rewrite (iorder_sr or Ysr) => pa pb.
by ex_tac; move => x xY ax; apply: pb; apply /iorder_gleP.
Qed.

Lemma Exercise6_29f r: order r -> 
 (Noetherian r <->
   (forall i, inc i (substrate r) -> Noetherian_set r (interval_ou r i))).
Proof.
move => or; split => h.
  by move => i isr; apply: (Exercise6_29e or h); apply: Zo_S.
move => X Xsr neX.
move: (neX) => [a aX].
case: (p_or_not_p (maximal (induced_order r X) a)) => ma.
  by exists a.
set Y := Zo X (fun z => glt r a z).
case: (emptyset_dichot Y) => neY.
  case: ma; split; first by rewrite (iorder_sr or Xsr).
  move => x /iorder_gleP  [_ pa pb].
  by ex_middle exa; empty_tac1 x; apply: Zo_i=> //; split => //; apply: nesym.
have sY: sub Y (interval_ou r a).
  move => y /Zo_P [yX ay]; apply /Zo_P; split => //; order_tac. fprops.
move: (h _ (Xsr _ aX)).
have Isr: sub  (interval_ou r a) (substrate r) by apply: Zo_S.
rewrite  (Noetherian_set_pr or Isr) => aux. 
move: (aux _ sY neY) => [b ibY etc].
move: ibY => /Zo_P [bX ab].
exists b; split; first by rewrite (iorder_sr or Xsr).
move=> x /iorder_gleP [_ xX bx].
apply: etc => //;apply /Zo_P; split => //; order_tac.
Qed.

(* to be commented *)
Definition restriction_to_segmentA r x g :=
  [/\ order r, inc x (substrate r), function g & sub (segment r x) (source g)].

Lemma rts_function1 r x g: restriction_to_segmentA r x g  -> 
  function (restriction1 g (segment r x)).
Proof. 
move=> [p1 p2 p3 p4];  exact: (proj31 (restriction1_prop p3 p4)).
Qed.

Lemma rts_W1 r x g a:  restriction_to_segmentA r x g  -> 
  glt r a x -> Vf (restriction1 g (segment r x)) a = Vf g a.
Proof. 
move=> [p1 p2 p3 p4] ax.
by apply: restriction1_V =>//; apply/segmentP.
Qed.

Lemma rts_surjective1 r x g:  restriction_to_segmentA r x g  -> 
  surjection (restriction1 g (segment r x)).
Proof.
move=> [p1 p2 p3 p4].
by apply: restriction1_fs. 
Qed.

Lemma rts_extensionality1 r s x f g:
  order r -> inc x (substrate r) -> order s -> inc x (substrate s) ->
  segment r x = segment s x ->
  function f -> sub (segment r x) (source f) ->
  function g -> sub (segment s x) (source g) ->
  (forall a , inc a (segment r x) -> Vf f a = Vf g a) ->
  restriction1 f (segment r x) = restriction1 g (segment s x).
Proof. 
move=> wor xsr wos xss srsx ff srf fg ssg sv.
have rf:  (restriction_to_segmentA r x f) by done.
have rg:  (restriction_to_segmentA s x g) by done.
apply: function_exten =>//; try  apply: rts_function1;
  try solve [rewrite /restriction1; aw;trivial].
  rewrite /restriction1; aw; trivial.
  set_extens t. 
    move/(Vf_image_P ff srf)=> [u us Wu]; apply /(Vf_image_P fg ssg).
    by rewrite - srsx; ex_tac; rewrite - sv.
  move/(Vf_image_P fg ssg)=> [u us Wu]; apply /(Vf_image_P ff srf).
  by rewrite - srsx in us; ex_tac; rewrite sv.
move=> u;rewrite  /restriction1; aw. 
move=> us.
have p1: glt r u x by apply: (inc_segment us).
have p2: glt s u x by rewrite srsx in us;apply: (inc_segment us); ue.
rewrite  rts_W1 // rts_W1 // sv //. 
Qed.

Lemma transfinite_unique11 r p  f f' z: order r ->
  inc z (substrate r) ->
  transfinite_def r p f -> transfinite_def r p f' -> 
  (forall x : Set, inc x (segment r z) -> Vf f x = Vf f' x) ->
  restriction1 f (segment r z) = restriction1 f' (segment r z).
Proof. 
move=>  wo zsr [[ff _ ] sf Wf] [[ff' _] sf' Wf'] sW.
have ss: sub (segment r z) (substrate r) by apply: sub_segment.
apply: rts_extensionality1=> //; ue.
Qed.


Lemma inc_set_of_segments1 r x: order r ->
  inc x (segments r) -> segmentp r x. 
Proof.
rewrite /segments/segmentss=> or.
case /setU1_P.
  by move /funI_P => [z zr ->];  apply: segment_segment=>//. 
by move=> ->; apply: substrate_segment.
Qed.


(* ---------- *)
Lemma Exercise_6_20b a: 
   \2c <c a ->
   (forall m, \0c <c m -> m <c a -> a ^c m = a) -> regular_cardinal a.
Proof.
move => a2 h.
have ca:= proj32_1 a2.
case: (finite_or_infinite ca).
  move /NatP => aN.
  move: (h _ clt_02 a2); rewrite cpowx2 => eq1.
  have aa: a <=c a by fprops.
  have anz: a <> \0c by move => eq2; rewrite eq2 in a2; case: (clt0 a2).
  move: (cprod_Mlelt  aN aN aa a2 anz); rewrite eq1 => le1.
  case: (cltNge le1(cprod_M1le ca card2_nz)).
move => ica; apply /regular_cardinalP; split; first by exact.
ex_middle ne1.
have sa: singular_cardinal a by split.
have pa: (cpow_less_ec_prop a a \1c).
  split; first by apply: clt_fin_inf; fprops.
  move => b; rewrite (cpowx1 ca); move /cge1P => b1 ba. 
  by rewrite (h _ b1 ba).
move: (cantor ca);  rewrite - (infinite_power1_b ica).
move: (cpow_less_ec_pr3 pa (proj1 a2) sa) => [-> <-].
by rewrite (cpowx1 ca); move => [].
Qed.

Lemma Exercise_6_20c1 a: 
   GenContHypothesis -> regular_cardinal a ->
   (forall m, \0c <c m -> m <c a -> a ^c m = a).
Proof.
move => gch /regular_cardinalP [ia ra] m [_ m0] ma.
move: (infinite_power10 gch m ia); move=> [_ pa _ _].
by apply: pa; [ apply:nesym | ue].
Qed.

Lemma Exercise_6_20c2: 
  (forall a, regular_cardinal a ->
    (forall m, \0c <c m -> m <c a -> a ^c m = a)) ->
 GenContHypothesis.
Proof.
move => h.
move => t ict; move: (ict) => [ct _].
move: (ord_index_pr1 ict)=> [on tv].
move: (regular_initial_successor on).
rewrite - (cnextE on) tv => rs.
move: (h _ rs _ (clt_fin_inf finite_0 ict) (cnext_pr2 ct)).
move => le1.
apply: cleA; first by apply: (cnext_pr3 ct).
have pa: \2c  <=c cnext t. 
   rewrite -tv (cnextE on).
   apply: (cle_fin_inf finite_2 (CIS_aleph (OS_succ on))).
by rewrite -le1; apply: (cpow_Mleeq _ pa card2_nz).
Qed.

Lemma Exercise6_22c1 x: 
   card_dominant x -> 
   (x = omega0 \/ (exists2 n, limit_ordinal n & x = \aleph n)).
Proof.
move => [pa pb].
move: (ord_index_pr1 pa); set c := ord_index x; move => [pd pe].
case: (ordinal_limA pd) => ln;last by right; exists c.
  by left; rewrite -pe ln aleph0E.
move: ln => [m om mv].
set y:= \aleph m.
have yx: y <c x.
  by  rewrite /y -pe; apply: aleph_lt_ltc; rewrite mv; apply: oltS.
move: (pb _ _ yx yx); rewrite (infinite_power1_b (CIS_aleph om)) => le1.
by move: (cnext_pr3(CS_aleph om));rewrite (cnextE om) -mv pe => /(cltNge le1).
Qed.


Lemma Exercise6_22c2 x 
  (p1 := forall z, \0c <c z -> z <c x -> x ^c z = x)
  (p2:= forall z, \0c <c z ->  x ^c z = x *c \2c ^c z):
  [/\ (infinite_c x -> p1 -> p2),
    (card_dominant x -> (p1 <-> p2)),
    (card_dominant x -> p1 -> (x = omega0 \/ inaccessible x)) &
    (x = omega0 \/ inaccessible x -> (card_dominant x /\ p1))].
Proof.
have r1:infinite_c x -> p1 -> p2.
  move=> icx hp1 z zp.
  move: (infinite_ge2 icx) => x2.
  move: (infinite_nz icx) => xnz.
  have cz:= proj32_1 zp.
  case: (cleT_ee (proj1 icx) (CS_pow \2c z)).
    move => le1.
    move: (cle_inf_inf icx le1) => icp.
    case: (finite_or_infinite cz) => icz.
      have f1: finite_c (\2c ^c z). 
        by apply /NatP; apply NS_pow; fprops; rewrite inc_Nat.
      case: (finite_not_infinite f1 icp). 
    rewrite (infinite_power1 x2 le1 icz).
    by rewrite cprodC cprod_inf.
  have pnz: \2c ^c z <> \0c by apply: cpow2_nz.
  move => le1.
  rewrite (hp1 _ zp (clt_leT (cantor cz) le1)).
  rewrite cprod_inf //.
have r2: card_dominant x -> (p1 <-> p2).
  move=> [icx cdx]; split; first by apply: r1.
  move => hp2 z z0 zx.
  have pnz: \2c ^c z <> \0c by apply: cpow2_nz.
  move: (cdx _ _ (clt_fin_inf finite_2 icx) zx) => [l1 _].
  rewrite (hp2 _ z0) cprod_inf //.
have r3:  card_dominant x -> p1 -> x = omega0 \/ inaccessible x.
  move => pa pc; case: (Exercise6_22c1 pa); first by left.
  move => h; right.
  move: pa => [pa pb].
  split; last first. 
    by move => t tx; apply: pb => //; apply: (clt_fin_inf finite_2 pa).
  split; last by exact.
  move: (cofinality_c_small (proj1 pa)) => h1.
  split => //; ex_middle eq1.
  have pd: \0c <c cofinality_c x. 
    apply: (clt_fin_inf  finite_0 (cofinality_infinite pa)).
  move: (power_cofinality (infinite_ge2 pa)).
  by rewrite (pc _ pd (conj h1 eq1)); move => [_].
split => //.
case => ix.
  rewrite ix; split; first by apply: card_dominant_pr2.
  move => z z0 zf.
  have pa: infinite_c x by rewrite ix; apply: CIS_omega.
  have pb: inc z Nat.
    by rewrite ix in zf; move: (oclt zf) => /oltP0 [_ _].
  have pc: z <> \0c by move: z0 => [_ /nesym].
  by rewrite cpow_inf.
split; first by apply: inaccessible_dominant.
by move => z [_ zc] zx;apply: inaccessible_pr7 => //; apply:nesym.
Qed.


(************************************************* *)

(** Exercise 6 31 *)


Lemma infinite_setU1 X x: infinite_set X -> infinite_set (X +s1 x).
Proof.
move/infinite_setP => h; apply/infinite_setP.
by apply: (cle_inf_inf h); apply: sub_smaller; move => t tx; apply: setU1_r.
Qed.

Lemma infinite_setC1 X x: infinite_set X -> infinite_set (X -s1 x).
Proof.
by move => h; rewrite /infinite_set - (card_setC1_inf x h).
Qed.

Lemma sub_infinite_set x y: sub x y -> infinite_set x -> infinite_set y.
Proof.
move => /sub_smaller le1 /infinite_setP ix; apply/infinite_setP.
by apply: (cle_inf_inf ix le1).
Qed.


Lemma sub_infinite_countable x:
  infinite_set x -> exists y, [/\ infinite_set y, countable_set y & sub y x].
Proof.
move /infinite_setP / infinite_c_P2; rewrite -/Nat - cardinal_Nat.
move /eq_subset_cardP1 /set_leP => [y yx /card_eqP cy].
have iy: infinite_set y.
  apply/infinite_setP; rewrite - cy; apply/infinite_setP; apply: infinite_Nat.
by exists y; split => //; apply /aleph0_countable; rewrite - cy - aleph0_pr1.
Qed.

Section Ex6_31. 
Variable A : Set.
Hypothesis Ainf: infinite_set A.
Definition inf_subsets := Zo (\Po A) infinite_set. 
Definition inf_subset_order := opp_order (sub_order inf_subsets).
Let r := inf_subset_order.




Lemma Exercise6_31_a: order_on r inf_subsets.
Proof.
by move:(sub_osr inf_subsets) => [or <-]; apply: opp_osr.
Qed.  

Lemma Exercise6_31_b x y: gle r x y <->
  [/\ inc x inf_subsets, inc y inf_subsets & sub y x].                     
Proof.
apply: (iff_trans  (opp_gleP (sub_order inf_subsets) x y)).
apply: (iff_trans (sub_gleP inf_subsets y x)).
by split => - [qa qb qc].
Qed.


Lemma Exercise6_31_c x: inc x inf_subsets -> inc (rep x) x.
Proof.
move/Zo_hi => ix.
case: (emptyset_dichot x); last by move/rep_i.
move => xe; case:(finite_not_infinite_set emptyset_finite); ue.
Qed.
  
  
Lemma Exercise6_31_d:  ~ (exists x : Set, maximal r x).
Proof.
move => [x [xsr xmax]].
move: Exercise6_31_a =>[or sr].
rewrite sr in xsr; move/Zo_P: (xsr) => [/setP_P xA ix].
set y := (x -s1 (rep x)).
have id : infinite_set y by apply:infinite_setC1.
have syx: sub y x by move => t /setC1_P [].
have dZ: inc y  inf_subsets.
  apply:Zo_i => //; apply/setP_P; apply: (sub_trans syx xA).
have /xmax eq: gle r x y by  apply/Exercise6_31_b.
by move: (Exercise6_31_c xsr); rewrite - {2} eq => /setC1_P [_].
Qed.


Lemma Exercise6_31_e: ramifiedc r .
Proof.
split; last by apply:Exercise6_31_d.
move => x y [lxy /nesym nxy].
move/Exercise6_31_b: lxy => [xE yE stx].
move: (Exercise6_31_c yE) => iby.
set a := rep (x -s y).
have bb: inc a (x -s y) by apply: rep_i; apply: setC_ne.
set z := y -s1 (rep y) +s1 a.
have az: inc a z by  apply/setU1_P; right.
move/setC_P: bb  => [ax ay].
move: (stx _ iby) => bx.
have bz: ~ (inc (rep y) z).
  case /setU1_P;  first by case/setC1_P.
  by move => rya; case: ay; rewrite - rya.   
case: (equal_or_not x z) => xnz; first by case: bz; ue.
have zE: inc z inf_subsets.
  move/Zo_P: xE => [/setP_P xA ix].
  move/Zo_P: yE => [/setP_P yA iy].
  apply/Zo_P; split.
    apply/setP_P => t /setU1_P; case; first by  move/setC1_P => [/yA].
    by move ->; apply/xA.
  by apply:infinite_setU1; apply: infinite_setC1.
exists z; split.
- split => //; apply/Exercise6_31_b; split => //. 
  move => t /setU1_P; case; [ by move/setC1_P => [/stx ] | by move -> ].
- by move/Exercise6_31_b =>[_ _ zy]; move: (zy _ az).
- by move/Exercise6_31_b =>[_ _ zy]; move: (zy _ iby).
Qed.

Lemma Exercise6_31_f x y: inc x inf_subsets -> inc y inf_subsets ->
 ( (forall t, gle r x t -> gle r y t -> False) <-> finite_set (x \cap y)).
Proof.
move => xE yE.
split => h.
  case: (finite_or_infinite_set (x\cap y)) => ixy //.
  have s1: sub (x \cap y) x by apply: setI2_1.
  have xyE: inc (x \cap y) inf_subsets.
    move: (Zo_S xE) => /setP_P xA.
    apply: Zo_i => //; apply/setP_P; apply: (sub_trans s1 xA).
  by case: (h (x \cap y)); apply/Exercise6_31_b; split => //;  apply: setI2_2.
move =>t /Exercise6_31_b [_ /Zo_hi tinf s1] /Exercise6_31_b [_ _ s2].
have txy: sub t (x\cap y). move => s st;apply /setI2_P; split; fprops.
exact (finite_not_infinite_set (sub_finite_set txy h) tinf).
Qed.

Lemma Exercise6_31_g_unused:
  exists2 x, inc x inf_subsets & inc (A -s x)  inf_subsets.
Proof.
move/infinite_setP: Ainf => icA.
move: (disjointU2_pr3 A A  C0_ne_C1);
move: (csum_inf1 icA); set c := cardinal A  => h.
rewrite - csum2cr - csum2cl h double_cardinal. 
move /esym / equipotent_ex_pr1; set f := (equipotent_ex _ _).
move =>[bf sf tf].
have ff: function f by fct_tac.
set X := Vfs f (A *s1 C1).
have sXA: sub X A by  rewrite - tf; apply:(fun_image_Starget1 ff).
have s1: sub (A *s1 C1) (source f) by rewrite sf => t; apply: setU2_1.
move: (cardinal_image s1 (proj1 bf)); rewrite -/X cardinal_indexed => cc.
have ra: inc X inf_subsets.
  by apply: Zo_i; [ by apply/setP_P | apply/infinite_setP; rewrite cc].
set Y := Vfs f (A *s1 C0).
have sYA: sub Y A by  rewrite - tf; apply:(fun_image_Starget1 ff).
have s2: sub (A *s1 C0) (source f) by rewrite sf => t; apply: setU2_2.
move: (cardinal_image s2 (proj1 bf)); rewrite -/Y cardinal_indexed => ccc.
have rb: inc Y inf_subsets.
  by apply: Zo_i; [ by apply/setP_P | apply/infinite_setP; rewrite ccc].
have XY: Y = A -s X. 
  set_extens t.
    move/(Vf_image_P ff s2) =>[u ua ->]; apply/setC_P; split; first Wtac.      
    move/(Vf_image_P ff s1) =>[v va sv].
    move: (proj2 (proj1 bf) u v (s2 _ ua) (s1 _ va) sv) => sv1.
    case: C0_ne_C1.
    move/indexed_P: ua => /proj33 <-.
    by move/indexed_P: va => /proj33 <-; rewrite sv1.
  move => /setC_P [sa].
  rewrite - tf in sa; move: (proj2(proj2 bf) _ sa); rewrite sf.
  move => [i /setU2_P ii ->] sb; case:ii => ts.
    by case: sb; apply /(Vf_image_P ff s1);  exists i.
  by apply /(Vf_image_P ff s2);  exists i.
by exists X => //; rewrite - XY.
Qed.

Lemma Exercise6_31_g: ~ anti_directed r.
Proof.
move => h.
move :Exercise6_31_a =>[or sr].
move/ (Exercise1_23hP or): h =>[qa _].
have aE: inc A inf_subsets by apply: Zo_i => //; apply: setP_Ti.     
set X := A -s1 (rep A). 
have sXA: sub X A by move => t /setC1_P; case.
have xE: inc X inf_subsets.
  by apply: Zo_i; [by apply/setP_P | apply: infinite_setC1].
move: (Exercise6_31_c aE) => raa.
have nAX: A <> X.
  by move => h; move: raa; rewrite{2} h => /setC1_P [_].
have lxA:  glt r A X.
  by split => //; apply/Exercise6_31_b.
move: (qa _ _ lxA) =>[z laz].
move/(Exercise6_31_b): (proj1 laz) => /proj32 zE.
move/(Exercise6_31_f xE zE) => ifin.
move/Zo_P: (zE) => [/setP_P szA iz].
apply:(finite_not_infinite_set ifin).
move: (infinite_setC1 (rep A) iz).
have <- //: (X \cap z) = z -s1 (rep A).
set_extens t.
   by move => /setI2_P [/setC1_P [ua ub] uc]; apply/setC1_P.
move => /setC1_P [tz tra]; apply/setI2_P; split => //.
by apply/setC1_P; split => //; apply: szA.
Qed.

Definition count_inf_subsets := Zo inf_subsets countable_set. 
Let F := count_inf_subsets. 
 
Lemma Exercise6_31_h: cofinal r F.
Proof.
move :Exercise6_31_a =>[or sr].
split; first by rewrite sr; apply: Zo_S.
rewrite sr => x xE.
move/Zo_P:(xE) => [/setP_P xA ix].
move:(sub_infinite_countable ix) =>[y [ya yb yc]].
have yE: inc y inf_subsets.
  apply: Zo_i => //; apply/setP_P; apply: (sub_trans yc xA).
exists y; first by apply: (Zo_i yE yb).
by apply/Exercise6_31_b.
Qed.

Definition count_inf_subsets_order := induced_order r F.
Let r' := count_inf_subsets_order.

Lemma Exercise6_31_i: order_on r' F.
Proof.
move:  Exercise6_31_a =>[or sr].
have ha: sub count_inf_subsets (substrate r) by rewrite sr; apply: Zo_S.
exact: (iorder_osr or ha).
Qed.


Lemma Exercise6_31_j x y:
  gle  r' x y <-> [/\ inc x F, inc y F & sub y x].
Proof.
apply: (iff_trans (iorder_gleP r F x y)).
split; move =>[xF yF etc]; split => //.
  by case/Exercise6_31_b: etc.
apply/Exercise6_31_b; split; [apply: (Zo_S xF) |  apply: (Zo_S yF) | done ].
Qed.

Lemma Exercise6_31_j_bis x y:
  inc x F -> infinite_set y -> sub y x -> gle  r' x y.
Proof.
move => xF yi syx.
move /Zo_P: (xF) => [/Zo_P [/setP_P xA xi] xc].
have yF: inc y F.
  apply: Zo_i (countable_sub syx xc); apply: Zo_i yi.
  apply/setP_P; apply: (sub_trans syx xA).
by apply/Exercise6_31_j.
Qed.


Let Z := nreg_opens r'.
Let f := canonical_reg_open r'.
Let r'' := (nregs_order r').


Lemma  Exercise6_31_A z :inc z Z ->
  inc (rep z) F /\  gle r'' z (f (rep z)).
Proof.
move: Exercise6_31_i =>[or sr] /Exercise1_23aP [qa qb].
move: (rep_i qb) => yz.
move: (proj1 (proj1 qa) _ yz) => ysr.
move: (Exercise1_23d2 or ysr) => /Exercise1_23aP [p1 p2].
move: ysr; rewrite sr => yF; split => //.
apply/(Exercise1_23bP or); split => //.
rewrite /f /canonical_reg_open {2} (Exercise1_22p or qa).
apply: (Exercise1_22j or (Exercise1_23c (rep z) or)(proj1 qa)).
by move=> t /Zo_hi yt; move: (proj2 (proj1 qa) _ _ yz yt).
Qed.



Definition Ex6_31_Xnz z n :=
  Zo (rep z) (fun t => exists i j, [/\ natp i, natp j, n <=c i &
     t = Vf  (equipotent_ex Nat(rep z)) 
        (Vf (equipotent_ex (coarse Nat) Nat) (J i j))]).  


Lemma Exercise6_31_k z  (X0 := rep z) (Xn := Ex6_31_Xnz z) : inc z Z ->
  [/\ Xn \0c = X0, forall n, natp n -> inc (Xn n) F,
     forall n,  natp n -> sub (Xn (csucc n)) (Xn n),
     forall n,  natp n -> infinite_set ((Xn n) -s (Xn (csucc n))) &
     intersectionf Nat Xn = emptyset].
Proof.
move => zZ.
set g :=  (equipotent_ex Nat X0).
move: (Exercise6_31_A zZ); rewrite -/X0; move =>[X0F le0].
move/Zo_P: X0F => [/Zo_P [/setP_P xc xa] xb].
have [bg sg tg]:  bijection_prop g Nat X0.
   case: (countable_finite_or_N xb); first by  move /finite_not_infinite_set.
   by rewrite aleph0_pr1; move/esym /card_eqP/equipotent_ex_pr.
move: (equipotent_ex_pr equipotent_N2_N).
set h := equipotent_ex _ _; move => [bh sh th].
have ra n: sub (Xn n) X0 by apply: Zo_S. 
have fg: function g by fct_tac.
have fh: function h by fct_tac.
have comp_inj i j i1 j1: natp i -> natp j -> natp i1 -> natp j1 ->
  Vf g (Vf h (J i j)) = Vf g (Vf h (J i1 j1)) -> i = i1 /\ j = j1.
  move => iN jN i1N j1N.
  have sa1: inc (J i j) (source h) by rewrite sh; apply: setXp_i.
  have sa: inc (Vf h (J i j)) (source g)  by rewrite sg - th; Wtac. 
  have sb1: inc (J i1 j1) (source h) by rewrite sh; apply: setXp_i.
  have sb: inc (Vf h (J i1 j1)) (source g)  by rewrite sg - th; Wtac. 
  move/ (proj2 (proj1 bg) _ _ sa sb).
  by move/ (proj2 (proj1 bh) _ _ sa1 sb1) => /pr12_def.
have rb: Xn \0c = X0.
  set_extens t; first by move/Zo_S.
  move => tx0; apply: Zo_i => //. 
  rewrite - tg in tx0. move: (proj2 (proj2 bg) _ tx0); rewrite sg.
  move => [x xN ->].
  rewrite -th in xN; move: (proj2 (proj2 bh) _ xN); rewrite sh.
  move => [ij /setX_P [qa qb qc] ->].
  exists (P ij), (Q ij); split => //; [ by apply: cle0n | by rewrite qa].
have re: intersectionf Nat Xn = emptyset. 
  have nen: nonempty Nat by exists \0c; apply: NS0.
  apply/set0_P => t /(setIf_P _ nen) hyp.
  move: (hyp _ NS0) => /Zo_hi [i [j [iN jN _ tv]]].
  move: (hyp _ (NS_succ iN)) => /Zo_hi [i1 [j1 [i1N j1N la]]].
  rewrite tv.   move/(comp_inj _ _ _ _ iN jN i1N j1N) => /proj1 ii.
  by case: (proj2 (clt_leT (cltS iN) la)).
have rf n : natp n -> sub (Xn (csucc n)) (Xn n).
  move => nN t /Zo_P [tX [i [j [iN jN lin ee]]]]; apply:Zo_i => //.
  by rewrite ee; exists i, j; split => //; move: (cleT (cleS nN) lin).
have rd1 n: natp n ->
  Xn n -s Xn (csucc n) = fun_image Nat (fun z => (Vf g (Vf h (J n z)))).
  move => nN;set_extens t.
     move => /setC_P [/Zo_P [ha [i [j [iN jN kin tv]]]  hc]].
     case: (equal_or_not n i) => ein.
       by apply/funI_P; exists j => //; rewrite  ein.
     case: hc; apply:Zo_i => //; exists i, j; split => //.
     by apply/(cleSltP nN).
   move =>/funI_P[j jN ->]; apply/setC_P; split.
     apply: Zo_i.
       rewrite -/X0 - tg; Wtac; rewrite sg - th; Wtac. 
       by rewrite sh; apply: setXp_i.    
     exists n, j; split => //; apply: (cleR (CS_nat nN)).
   move=> /Zo_hi [i1 [j1  [i1N j1N le1]]].
   move/(comp_inj _ _ _ _ nN jN i1N j1N) => /proj1 ee.
   by case: (cleNgt le1); rewrite - ee; apply:cltS.
have rd n: natp n -> infinite_set (Xn n -s Xn (csucc n)).
  move => nN; rewrite (rd1 _ nN); apply/infinite_setP.
  rewrite cardinal_fun_image; first by apply/infinite_setP /infinite_Nat.
  by move => i1 i2 i1N i2N; move/(comp_inj _ _ _ _ nN i1N nN i2N); case.
split => //.
move => n nN.
have qa: infinite_set (Xn n).
  have /sub_smaller la: sub (Xn n -s Xn (csucc n)) (Xn n).
    by move => t/setC_P; case.
  move/infinite_setP: (rd _ nN) => sa.
  by move: (cle_inf_inf sa la); move/infinite_setP.
move: (countable_sub (ra n) xb) => cs.
apply: Zo_i => //.
apply: Zo_i => //; apply/setP_P;  apply:(sub_trans (ra n) xc).  
Qed.

Definition Ex6_31_res :=
  Zo F (fun t => exists z n, [/\ inc z Z, inc n Nat & t = Ex6_31_Xnz z n]).

Lemma Ex6_31_resP t: inc t Ex6_31_res <->
   exists z n, [/\ inc z Z, inc n Nat & t = Ex6_31_Xnz z n].
Proof.
split; [ by move/Zo_hi | move => h; move: (h) =>[z [n [zZ nN ->]]]].
move:(Exercise6_31_k zZ) =>[_ hh _ _ _].
by apply: (Zo_i (hh _ nN)); exists z,n.
Qed.


Lemma Exercise6_31_l z: inc z Z ->
   exists2 x, inc x  Ex6_31_res  & gle r'' z (f x).
Proof.
move => zZ; move: (proj2 (Exercise6_31_A zZ)) => h.
exists (rep z) => //. apply/Ex6_31_resP.
move:(Exercise6_31_k zZ) =>[<- _ _ _ _]; exists z, \0c; split => //; apply: NS0.
Qed.


Lemma Exercise6_31_fP x y: inc x F -> inc y F ->
  (inc y  (f x) <->
  forall z,  infinite_set z -> sub z y ->  infinite_set (x \cap z)).
Proof.
move => xF yF.
move: Exercise6_31_i =>[or sr].
have xsr: inc x (substrate r') by ue.
have ysr: inc y (substrate r') by ue.
apply: (iff_trans (Exercise1_23e or xsr ysr)).
split => hyp.
  move => z iz szy.
  move/Zo_P: (yF) => [/Zo_P [/setP_P yA yi] yc].
  move: (countable_sub szy yc) => cz.
  have zF: inc z F.
    by apply: Zo_i cz; apply:Zo_i iz; apply/setP_P; apply: (sub_trans szy yA).
  have le1:  gle r' y z by apply/Exercise6_31_j.
  move:(hyp z le1) => [t /Exercise6_31_j [_ tf s1] /Exercise6_31_j [_ _ s2]].
  have s3: sub t (x\cap z). 
    move => a ia; apply: setI2_i; [ by apply: s2 | by apply: s1].
  exact:(sub_infinite_set s3 (Zo_hi (Zo_S tf))).
move => z /Exercise6_31_j [_ zF zy].
move: (hyp _ (Zo_hi (Zo_S zF)) zy) => ii.
have siz: sub (x \cap z) z by move => t /setI2_P [].
have six: sub (x \cap z) x by move => t /setI2_P [].
move/Zo_P: (xF) => [/Zo_P [/setP_P xA _] xc].
have iF: inc (x \cap z) F.
  apply:Zo_i   (countable_sub six xc); apply: Zo_i => //.
  apply/setP_P; apply: (sub_trans six xA).
by exists (x \cap z); apply/Exercise6_31_j.
Qed.


Lemma Exercise6_31_B x y: inc x F ->
  (inc y  (f x) <-> inc y F /\ finite_set (y -s x)).
Proof.
move: Exercise6_31_i =>[or sr].
move => xF; split.
  move: (@Exercise1_23d2 r' x or); rewrite sr -/f => h yf.
  move /setC1_P: (h xF) => /proj1/Zo_S/setP_P; rewrite sr => fxF.
  have yF := (fxF _ yf).
  move/ (Exercise6_31_fP xF yF): yf => q; split => //.
  case: (finite_or_infinite_set (y -s x)) => // di.
  have ce: (x \cap (y -s x)) = emptyset.
   by apply/set0_P => t /setI2_P [tx /setC_P /proj2].
  case: (finite_not_infinite_set emptyset_finite).
  by move: (q _ di (@sub_setC y x)); rewrite ce.
move =>[yF etc]; apply /(Exercise6_31_fP xF yF) => [z iz zy ].
case: (finite_or_infinite_set (x \cap z)) => // fi.
move: (finite_union2 (sub_finite_set (@setI2_2 z (y -s x)) etc) fi).
have ee1: z \cap (x \cap y) = x \cap z.
  rewrite setI2_A (setI2_C z); set_extens t; first  by case/setI2_P.
  by move => ta; apply: setI2_i => //; apply: zy; case/setI2_P: ta.
have <-: z = z \cap (y -s x) \cup (x \cap z).
  rewrite - ee1- set_IU2r; set_extens t; last by case /setI2_P.
  move => tz; apply/setI2_P; split => //; move: (zy _ tz) => ty.
   case: (inc_or_not t x) => tx.
     by apply/setU2_P; right; apply: setI2_i.
   by apply/setU2_P; left; apply/setC_P.
by move/finite_not_infinite_set.
Qed.


Lemma Exercise6_31_C x y: inc x F ->
  (inc y  (f x) <-> 
   exists a b,
     [/\ sub a A, finite_set a, sub b x, infinite_set b  & y = a \cup b]).
Proof.
move => xF; apply: (iff_trans (@Exercise6_31_B x y  xF)); split.
  move => [qa qb].
  have e1: y = (y -s x) \cup (y \cap x).
    set_extens t; last by case/setU2_P; [case/setC_P | move/setI2_1].
    move => ty; case: (inc_or_not t x) => tx.  
      by apply/setU2_P; right; apply/setI2_P.
    by apply/setU2_P; left; apply/setC_P.
  move: (Zo_S qa) => /Zo_P [/setP_P yA yi].
  case: (finite_or_infinite_set(y \cap x)) => fi.
    by move: (finite_union2 qb fi); rewrite - e1 => /finite_not_infinite_set.
  have dA: sub (y -s x) A by move => t /setC_P [/ yA].
  by exists  (y -s x), (y \cap x); split => //; apply: subsetI2r. 
move => [a [b [aA fA bx ib yv]]].
move/Zo_P: (xF) => [/Zo_P [/setP_P xA xi] xc].
have yA :sub y A.
  by move => t;rewrite yv; case/setU2_P; [ apply: aA | move/bx /xA].
have syb: sub b y by rewrite yv; apply:subsetU2r.
have iy:= (sub_infinite_set syb ib).
have cy: countable_set y.
  apply/countableP. 
  move: (countable_sub bx xc) => /countableP cb.
  move/infinite_setP: ib => cbi.
  move: (csum2_pr6 a b).
  rewrite - csum2cl - csum2cr  (csum_fin_infin fA cbi) - yv => ll.
  apply: (cleT ll cb).
have yF: inc y F by apply: Zo_i cy; apply: Zo_i iy; apply/setP_P.
split => //; apply:sub_finite_set fA.
by move => t; rewrite yv; move=> /setC_P [/setU2_P]; case => //; move/bx.
Qed.



Lemma Exercise6_31_fE x: f x = (open_bar r' (Zo F  (gle r' x))). 
Proof.
by rewrite /f /canonical_reg_open (proj2 (Exercise6_31_i)).
Qed.

Lemma Exercise6_31_p z: inc z Z ->
   exists2 x, inc x  Ex6_31_res  & sub (f x) z.
Proof.
move => zZ.
exists (rep z).
  apply/Ex6_31_resP; move:(Exercise6_31_k zZ) =>[<- _ _ _ _].
  exists z, \0c; split => //; apply: NS0.
by move: (proj2 (Exercise6_31_A zZ)) => /opp_gleP /sub_gleP /proj33.
Qed.

Lemma Exercise6_31_q U: open_o r' U  <->
  sub U F /\ forall x y, inc x U -> sub y x -> infinite_set y -> inc y U.
Proof.
move: Exercise6_31_i => [pr sr].
split.
  move=> [qa qb]; split; [ by rewrite - sr | move => x y xU syx ict].
  move: (qa _ xU); rewrite sr => xF.
  apply: (qb _ _ xU); apply/Exercise6_31_j; split => //.
  move/Zo_P: xF => [/Zo_P [/setP_P xA xi] xc].
  have ya: inc y (\Po A).   apply/setP_P; apply: (sub_trans syx xA).
  by apply: Zo_i (countable_sub syx xc); apply/Zo_i. 
move =>[qa qb]; split; [ by rewrite sr | move => x y xU /Exercise6_31_j].
by move => [xF /Zo_S /Zo_hi h sxy]; apply: (qb _ _ xU sxy).
Qed.


Lemma Exercise6_31_q_bis x: inc x F ->  open_o r' (Zo F  (gle r' x)). 
Proof.  
move => xF; apply/Exercise6_31_q; split; first by apply: Zo_S.
move => t y /Zo_P [tF /Exercise6_31_j /proj33 qa] qb qc.
move: (sub_trans qb qa) => qd.
have yF: inc y F.
  move/Zo_P: xF => [/Zo_P [/setP_P xA _] xc].
  move: (countable_sub qd xc) => cy.
  by apply: Zo_i cy; apply:Zo_i qc; apply/setP_P; apply: (sub_trans qd xA).
by apply/Zo_P; split => //; apply/Exercise6_31_j.
Qed.

Lemma Exercise6_31_r z: inc z Z <-> (z <> emptyset /\ open_r r' z).
Proof.
rewrite /Z/nreg_opens.
split; first by move => /setC1_P [/Zo_hi za znz].
move =>[aa /reg_opens_i qb]; apply/setC1_P; split => //.
Qed.




End Ex6_31.

(** Exercise 6 33 *)

Notation ZN := BZ_of_nat.
Notation ZNo := BZm_of_nat.

Definition zbetween x a b := a <=z x /\ x <z b.
Definition zbetween_eq x a b := a <=z x /\ x <=z b.

Definition znat_fam c := [/\ fgraph c, domain c = BZ & allf c natp].

Definition zpartial_sum c n :=
  Yo (inc n BZp) (ZN (csumb (BZ_val n) (fun i => Vg c (ZN i))))
     (ZNo (csumb (BZ_val n) (fun i => Vg c (ZNo (csucc i))))).

Lemma ZNz n: natp n -> intp (ZN n).
Proof. exact: BZ_of_nat_i. Qed.

Lemma zpartial_sum_p0 c n: natp n ->
   zpartial_sum c (ZN n) = (ZN (csumb n (fun i => Vg c (ZN i)))).
Proof.
by move => nN; rewrite /zpartial_sum (Y_true (BZ_of_natp_i nN)) BZ_of_nat_val.
Qed.

Lemma zpartial_sum_p1 c n: natp n ->
   zpartial_sum c (ZNo n) =
   ZNo (csumb n (fun i => Vg c (ZNo (csucc i)))).
Proof.
move => nN; rewrite /zpartial_sum.
case: (equal_or_not n \0c) => nz.
  have aux: ZNo \0c = \0z  by rewrite /ZNo; Ytac0.
  by rewrite nz aux (Y_true ZpS0) BZ0_val /csumb !csum_trivial; aw. 
move: (BZm_of_natms_i nN nz)  => /BZ_di_neg_pos vn.
by rewrite (Y_false vn) BZm_of_nat_val.
Qed.

Lemma zpartial_sum_int c n: znat_fam c -> intp n -> intp (zpartial_sum c n).
Proof. 
move => [qa qb qc]  nz; move: (BZ_valN nz) => vn.
rewrite /zpartial_sum.
case: (inc_or_not n BZp) => np; Ytac0.
  apply:ZNz; apply: finite_sum_finite; split.
    hnf; aw => i lin; rewrite (LgV lin); apply: qc; rewrite qb.
    apply: ZNz; exact:(NS_inc_nat vn lin).
  by aw; apply: finite_set_nat.
apply: BZm_of_nat_i;  apply: finite_sum_finite; split.
  hnf; aw => i lin; rewrite (LgV lin); apply: qc; rewrite qb.
  apply: BZm_of_nat_i; exact(NS_succ (NS_inc_nat vn lin)).
by aw; apply: finite_set_nat.
Qed.


Lemma zpartial_sum_p3 c n: znat_fam c -> natp n ->
   zpartial_sum c (ZN (csucc n)) = (zpartial_sum c (ZN n)) +z ZN (Vg c (ZN n)).
Proof. 
move => [qa qb qc] nN.
rewrite (zpartial_sum_p0 _ (NS_succ nN)) (zpartial_sum_p0 _ nN)(csum_fs  _ nN). 
symmetry;apply: BZsum_cN.
  apply: finite_sum_finite; split.
    hnf; aw => i lin; rewrite (LgV lin); apply: qc; rewrite qb.
    apply: (ZNz (NS_inc_nat nN lin)).
  by aw; apply: finite_set_nat.
by apply: qc; rewrite qb; apply: ZNz.
Qed.

Lemma zpartial_sum_p4 c n: znat_fam c -> natp n ->
  zpartial_sum c (ZNo (csucc n)) +z ZN (Vg c (ZNo (csucc n))) = 
  zpartial_sum c (ZNo n). 
Proof.
move => [qa qb qc]nN.
rewrite (zpartial_sum_p1 _ (NS_succ nN)) (zpartial_sum_p1 _ nN)(csum_fs  _ nN). 
set u := csumb _ _.
have uN: natp u.
  apply: finite_sum_finite; split.
    hnf; aw => i lin; rewrite (LgV lin); apply: qc; rewrite qb.
    apply: BZm_of_nat_i; exact: (NS_succ (NS_inc_nat nN lin)).
  by aw; apply: finite_set_nat.
set v := Vg _ _.
have vN: natp v.
  by apply: qc; rewrite qb; apply: BZm_of_nat_i;  exact: (NS_succ nN).
move: (ZNz uN) (ZNz vN) => uz vz.
rewrite - BZopp_p - (BZsum_cN uN vN) (BZoppD uz vz) (BZsum_diff1 vz (ZSo uz)).
by rewrite  BZopp_p.
Qed.

Lemma zpartial_sum_00 c:  zpartial_sum c \0z = \0z.
Proof.
by rewrite (zpartial_sum_p0 _ NS0) /csumb csum_trivial //; aw.
Qed.

Lemma zpartial_sum_rec c n: znat_fam c -> intp n ->
  zpartial_sum c (BZsucc n) = (zpartial_sum c n) +z ZN (Vg c n).
Proof.
move => cp nz; have mN :=  BZ_valN nz.
case/BZ_i0P: nz => np; last first.
  rewrite - (BZp_hi_pr np) (BZsucc_N mN); exact: (zpartial_sum_p3 cp mN).
move: (BZms_hi_pr np) =>[qa qb].
move: (cpred_pr mN qa) =>[sa sb].
have mz := (ZNz sa).
rewrite - qb sb (zpartial_sum_p4 cp sa) - BZopp_p - (BZsucc_N sa).
by rewrite  /BZsucc (BZoppD mz ZS1) (BZsum_diff1 ZS1 (ZSo mz))  BZopp_p.
Qed.

Lemma zpartial_sum_mon c n m: znat_fam c -> n <=z m ->
  zpartial_sum c n <=z zpartial_sum c m.
Proof.
move => ha hb.
move: (zleR (zpartial_sum_int ha (proj31 hb))) => hh.
move: m hb; apply:(BZ_induction_pos) => // m lnm Hrec; apply: (zleT Hrec).
have mz := (proj32 lnm).
rewrite  (zpartial_sum_rec ha mz). 
apply: (BZsum_Mp (zpartial_sum_int ha mz)).
by apply: BZ_of_natp_i; move: ha =>[qa qb qc]; apply: qc; ue.
Qed.

Lemma zpartial_sum_mon_bis c n m: znat_fam c -> intp n -> intp m ->
  zpartial_sum c n <z zpartial_sum c m -> n <z m.
Proof.
move => ha nz mz le.
by case: (zleT_el mz nz) => // /(zpartial_sum_mon ha) /zleNgt; case.
Qed.


Lemma zpartial_sum_mon_spec c n m j : znat_fam c -> intp n -> intp m ->
  zbetween j (zpartial_sum c n) (zpartial_sum c (BZsucc m)) ->
  exists2 p, zbetween_eq p n m & 
    zbetween j (zpartial_sum c p) (zpartial_sum c (BZsucc p)).
Proof.
move => ha nZ mZ hb.
have lnm: n <=z m.
  move: hb =>[la lb].
  move: (zpartial_sum_mon_bis ha nZ (ZS_succ mZ) (zle_ltT la lb)).
  by move/(zlt_succ1P nZ mZ).
clear mZ; move: m lnm j hb.
apply:(BZ_induction_pos). 
  by move => j jj; exists n => //; split; apply: (zleR nZ).
move => m lnm Hrec j [ja jb].
move:(proj32 lnm) => mz; move:(ZS_succ mz) => smz.
move:(proj1 (zlt_succ mz)) => lmz.
have ii: intp (zpartial_sum c (BZsucc m)) by  apply:zpartial_sum_int.
move:(zleT lnm lmz) (zleR smz) => qa qb.
case: (zleT_el ii (proj31_1 jb)) => lb.
  by exists (BZsucc m).
move: (Hrec j (conj ja lb)) => [p [pa pb] pc].
exists p => //; split => //; exact: (zleT pb lmz).
Qed.

  
Definition ZN_int n a b :=
  interval_cc BZ_order (n -z (ZN a)) (n +z (ZN b)).
  
Definition ZN_oint n a b :=
  interval_co BZ_order (n -z (ZN a)) (n +z (ZN b)).

Lemma ZN_intP n a b: intp n -> natp a -> natp b ->
  forall x, inc x (ZN_int n a b) <-> zbetween_eq x (n -z (ZN a)) (n +z (ZN b)).
Proof.
move => nz aN bN x.
move: BZor_or BZor_sr  => or sr.
rewrite /ZN_int /interval_cc sr.
split; first by move/Zo_hi => [/zle_P ha /zle_P hb].
move =>[le1 le2].
by move: (proj31 le2) => xz;apply: (Zo_i xz); split; apply/zle_P.
Qed.


Lemma ZN_ointP n a b: intp n -> natp a -> natp b ->
   forall x, inc x (ZN_oint n a b) <-> zbetween x (n -z (ZN a))(n +z (ZN b)).
Proof.
move => nz aN bN x.
move: BZor_or BZor_sr  => or sr.
rewrite /ZN_oint /interval_co sr.
split; first by move/Zo_hi => [/zle_P ha /zlt_P hb].
move =>[le1 le2]; move: (proj31_1 le2) => xz; apply: (Zo_i xz).
by split; [apply/zle_P | apply /zlt_P].
Qed.

Definition fin_disj_fam A :=
   [/\ fgraph A, domain A = BZ, mutually_disjoint A &  allf A finite_set].

Definition fin_disj_fam_card A := Lg BZ (fun z => cardinal (Vg A z)).

Definition simple_enum x := equipotent_ex x (cardinal x).

Definition fin_disj_fam_rank A x :=
 select (fun z =>  inc x (Vg A z)) BZ.

Definition fin_disj_fam_enum A x := let i :=  (fin_disj_fam_rank A x) in
  zpartial_sum (fin_disj_fam_card A) i
   +z ZN (Vf (simple_enum (Vg A i)) x).


           
Lemma fin_disj_fam_prop1 A x (i := (fin_disj_fam_rank A x)):
  fin_disj_fam A -> inc x (unionb A) ->
  inc x (Vg A i) /\ intp i. 
Proof.
move =>[qa qb qc qd] /setUb_P [k]; rewrite qb => kd kv.
apply: select_pr; first by exists k.
hnf; rewrite - qb; move =>  i1 i2 i1z i1v i2z i2v.
move: (qc i1 i2 i1z i2z); case => // fi; empty_tac1 x.
Qed.

Lemma fin_disj_fam_prop1_bis A x i:
  fin_disj_fam A -> intp i -> inc x (Vg A i) ->
  inc x (unionb A) /\ (fin_disj_fam_rank A x) = i.
Proof.
move => h iz xx; move: (h) =>[qa qb qc qd].
have xU: inc x (unionb A) by apply/setUb_P; exists i => //; ue.
move: (fin_disj_fam_prop1 h xU) =>[pa pb].
split => //; move: (qc (fin_disj_fam_rank A x) i); rewrite qb => h1.
case: (h1 pb iz) => // dd; empty_tac1 x.
Qed.


  
Lemma fin_disj_fam_prop2 A: fin_disj_fam A -> znat_fam (fin_disj_fam_card A).
Proof.
rewrite /fin_disj_fam_card; move =>[qa qb qc qd]; saw; fprops.
move => i; aw => iz; rewrite (LgV iz); apply card_finite_setP.
apply:qd; ue.
Qed.
  
Lemma simple_enump x: bijection_prop (simple_enum x) x (cardinal x).
Proof. by apply:equipotent_ex_pr1; rewrite double_cardinal. Qed.

Lemma simple_enump2 x y (i := (Vf (simple_enum x) y)):
  finite_set x -> inc y x ->  natp i /\ i <c (cardinal x).
Proof.
move => / card_finite_setP cN yx.
move: (simple_enump x) => [/proj1 /proj1 ff sf tf].
rewrite - sf in yx; move: (Vf_target ff yx); rewrite tf => /(NltP cN) h.
split => //. apply: (NS_lt_nat h cN).
Qed.

Lemma fin_disj_fam_prop3 A x (i := (fin_disj_fam_rank A x)):
  fin_disj_fam A -> inc x (unionb A) ->
  zbetween (fin_disj_fam_enum A x)
           (zpartial_sum (fin_disj_fam_card A) i)
           (zpartial_sum (fin_disj_fam_card A) (BZsucc i)).
Proof.
move => h1 h2.
move: (fin_disj_fam_prop2 h1).
move: (fin_disj_fam_prop1 h1 h2).
rewrite /fin_disj_fam_enum -/i.
set c:= (fin_disj_fam_card A).
move => [pa pb] pc.
have fsai: finite_set (Vg A i) by move: h1 =>[qsa qb qc qd]; apply: qd; ue.
move: (simple_enump2 fsai  pa); set u := Vf _ _; move => [uN le1].
have le2:  u <c Vg c i by  rewrite /c /fin_disj_fam_card; bw.
move: (zpartial_sum_int pc pb); rewrite (zpartial_sum_rec pc pb) => h3.
split; first exact:(BZsum_Mp h3  (BZ_of_natp_i uN)).
have qa: natp (Vg c i) by  move:pc =>[ra rv rc]; apply: rc; ue.
by apply/(BZsum_lt2l (ZNz uN) (ZNz qa) h3); apply/ zlt_cN.
Qed.

Lemma fin_disj_fam_prop4 A i e: fin_disj_fam A -> intp i ->
  zbetween e (zpartial_sum (fin_disj_fam_card A) i)
     (zpartial_sum (fin_disj_fam_card A) (BZsucc i)) ->
  exists2 x, inc x (unionb A) & e = fin_disj_fam_enum A x.
Proof.
move => h1 iz.
move: (fin_disj_fam_prop2 h1);
set c:= (fin_disj_fam_card A) => cf.
move: (zpartial_sum_int cf iz); rewrite (zpartial_sum_rec cf iz).
move => az [le1 lt2].
move: (proj32 le1) => ez.
move/(zle_diffP az ez): le1; move: (BZ_valN (ZS_diff  ez az)).
move: (BZsum_diff1 az ez).
set d := e -z _ => dv dN dp.
move: (BZp_hi_pr dp) => eq1.
have qa: natp (Vg c i) by  move:cf =>[ra rv rc]; apply: rc; ue.
move: lt2; rewrite - {1} dv BZsumC.
move/(BZsum_lt2l (BZp_sBZ dp) (ZNz qa) az); rewrite - eq1.
move/(zlt_cN dN qa) => /(NltP qa) lt3.
have fsai: finite_set (Vg A i) by move: h1 =>[qsa qb qc qd]; apply: qd; ue.
move: (simple_enump (Vg A i)).
have -> : (cardinal (Vg A i))  = Vg c i by  rewrite /c /fin_disj_fam_card; bw.
move => [[_ sjf] sf tf].
rewrite -tf in lt3; move: (proj2 sjf _ lt3); rewrite sf; move => [x x1 etc].
move: (fin_disj_fam_prop1_bis h1 iz x1) => [xu idx]; exists x => //.
by rewrite /fin_disj_fam_enum idx - etc eq1  BZsum_diff.
Qed.


Definition fin_disj_fam_enum_range A:=
  Zo BZ (fun i => exists2 x, inc x (unionb A) & fin_disj_fam_enum A x = i).

Lemma fin_disj_fam_enum_range_p1 A x:
 fin_disj_fam A -> inc x (unionb A) ->
  inc (fin_disj_fam_enum A x) (fin_disj_fam_enum_range A).
Proof.
move => ha hb.
move:  (proj32(proj1 (fin_disj_fam_prop3 ha hb))) => h; apply: (Zo_i h).
by (exists x).
Qed.


Lemma fin_disj_fam_prop5  A e1 e2 j (I := fin_disj_fam_enum_range A):
  fin_disj_fam A -> inc e1 I -> inc e2 I -> zbetween_eq j e1 e2 ->
  inc j I.
Proof.
move => ha /Zo_hi [x1 x1u eq1] /Zo_hi [x2 x2u eq2] [le1 le2].
move: (fin_disj_fam_prop3 ha x1u) (fin_disj_fam_prop3 ha x2u).
move: (fin_disj_fam_prop2 ha).
set c:= (fin_disj_fam_card A); rewrite eq1 eq2 => cf.
move: (fin_disj_fam_prop1 ha x1u).
set r1 := (fin_disj_fam_rank A x1); move =>[pa pb].
move: (fin_disj_fam_prop1 ha x2u).
set r2 := (fin_disj_fam_rank A x2); move =>[pa2 pb2].
move: (zpartial_sum_rec cf pb2) => eq0.
rewrite (zpartial_sum_rec cf pb)  eq0.
set s1 := zpartial_sum c r1; set s2 := zpartial_sum c r2.
move => [lea leb] [lec led].
move: (zleT lea le1) (zle_ltT le2 led); rewrite -eq0 => lj1 lj2.  
move:(zpartial_sum_mon_spec cf pb pb2 (conj lj1 lj2)).
move =>[p [pra prb] prc].
move: (fin_disj_fam_prop4 ha (proj31 prb) prc) =>[x xa ->].
apply: (fin_disj_fam_enum_range_p1 ha xa).
Qed.

Lemma fin_disj_fam_prop6 A: fin_disj_fam A ->
   {inc  (unionb A) &, injective (fin_disj_fam_enum A)}.
Proof.
move => Ha a b au bu sv.
move: (fin_disj_fam_prop3 Ha au)(fin_disj_fam_prop3 Ha bu). 
move: (fin_disj_fam_prop1 Ha au)(fin_disj_fam_prop1 Ha bu). 
move: (fin_disj_fam_prop2 Ha).
set u := (fin_disj_fam_rank A a).
set v := (fin_disj_fam_rank A b).
set c := (fin_disj_fam_card A).
rewrite - sv; move => cf [au1 uz] [bu1 vz] [la lb][lc ld].
have luv: u <=z v.
  move:(zle_ltT la ld).
  set x := zpartial_sum c u. set y := zpartial_sum c (BZsucc v) => lxx.
  move: (zpartial_sum_mon_spec cf uz vz (conj (zleR (proj31_1 lxx)) lxx)).
  move => [p [pa pb] _]; apply: (zleT pa pb).
have lvu: v <=z u.
  move:(zle_ltT lc lb).
  set x := zpartial_sum c v. set y := zpartial_sum c (BZsucc u) => lxx.
  move: (zpartial_sum_mon_spec cf vz uz (conj (zleR (proj31_1 lxx)) lxx)).
  move => [p [pa pb] _]; apply: (zleT pa pb).
move: (zleA luv lvu) => euv.
move: sv.
have fsA: finite_set (Vg A u).
  apply/card_finite_setP; move: cf =>[qa qb qc].
  have ->: cardinal (Vg A u) = Vg c u by  rewrite /c /fin_disj_fam_card; bw.
  apply: qc; ue.
have sa := proj1 (simple_enump2 fsA au1).
rewrite - euv in bu1.
have sb := proj1 (simple_enump2 fsA bu1).
rewrite /fin_disj_fam_enum -/c -/u -/v - euv. 
move /(BZsum_eq2l (zpartial_sum_int cf uz) (ZNz sa) (ZNz sb)).
move/BZ_of_nat_inj.
move: (simple_enump (Vg A u)) =>[[[_ fi] _] sf _].
by apply: fi; rewrite sf.
Qed.


Lemma fin_disj_fam_prop7_aux A k: fin_disj_fam A -> intp k ->
   Vg (fin_disj_fam_card A) k <> \0c ->
   inc (zpartial_sum (fin_disj_fam_card A) k) (fin_disj_fam_enum_range A).
Proof.
move => ha kz cnz. 
move:(simple_enump (Vg A k)); set f := (simple_enum _).
move => [bf sf tf].
have ztf: inc \0c (target f).
  move: cnz; rewrite /fin_disj_fam_card; bw => // cnz.
  by move: (card_ne0_pos (CS_cardinal (Vg A k)) cnz) => /oclt /olt_i; ue.
move: (inverse_V bf ztf) (inverse_Vis bf ztf); rewrite sf.
set y := Vf (inverse_fun f) \0c => vy ys.
move:(fin_disj_fam_prop1_bis ha kz ys) =>[yu ry].
set (x := zpartial_sum (fin_disj_fam_card A)).
move:(zpartial_sum_int (fin_disj_fam_prop2 ha)  kz) => hh.
have ->: x k = (fin_disj_fam_enum A y).
  by rewrite /fin_disj_fam_enum ry vy  (BZsum_0r).
by apply: (fin_disj_fam_enum_range_p1 ha yu).
Qed.

Lemma fin_disj_fam_prop7 A i j (x := zpartial_sum (fin_disj_fam_card A)):
  fin_disj_fam A -> i <=z j -> x i <z x j ->
  inc (x i) (fin_disj_fam_enum_range A).
Proof.
move => ha lij lvij.
move: (fin_disj_fam_prop2 ha); set c := (fin_disj_fam_card A) => cf.
move: (lij) =>[iz jz _].
have: exists k, [/\ i <=z k, x i = x k & x k <z x (BZsucc k)].   
  ex_middle bad.
  have h: forall k, i <=z k -> x i = x k.
    apply: BZ_induction_pos => // n lin Hr.
    rewrite Hr;ex_middle ne; case: bad; exists n; split => //; split => //.
    have le: n <=z BZsucc n by apply: (BZsum_Mp (proj32 lin) (BZps_sBZp ZpsS1)).
    exact: (zpartial_sum_mon cf le). 
  by case: (proj2 lvij); apply: h.
move =>[k [/proj32 kz ->]].
rewrite {2}/x (zpartial_sum_rec cf kz) -/x; move=>[le1].
case: (equal_or_not (Vg c k) \0c) => dz ww.
  by move: ww; rewrite dz (BZsum_0r (proj31 le1)); case.
exact:(fin_disj_fam_prop7_aux  ha kz dz). 
Qed.


Definition supp_left_unbounded c :=
  forall i, intp i -> exists2 j, j <=z i & Vg c j <> \0c.
Definition supp_right_unbounded c :=
  forall i, intp i -> exists2 j, i <=z j & Vg c j <> \0c.

Lemma supp_left_unbounded_p1 c b: znat_fam c -> intp b ->
  supp_left_unbounded c ->
  exists2 i, intp i & zpartial_sum c i <=z b.
Proof.
move => ha bz hyp.
have h := ZS0.
case/BZ_i2P: bz => bzz.
  move/zlt0xP: bzz => /proj1 bzz.
  by exists \0z; [apply:h | rewrite zpartial_sum_00].
move: (BZ_valN (BZm_sBZ bzz)) => nN.
rewrite - (BZm_hi_pr bzz).
move: (P b) nN; clear b bzz; apply: Nat_induction.
  exists \0z => //.
  by rewrite /ZNo (Y_true (erefl \0c)) zpartial_sum_00; apply: (zleR h).
move => n nN [i iN le1]. 
move:(ZS_pred iN) => piz.
move: (hyp _ piz) => [j lij etc]; move: (proj31 lij) => jz.
exists j => //.
have wz :=  (zpartial_sum_int ha jz).
have le2: BZsucc j <=z i.
  by rewrite - (BZsucc_pred iN); apply/ (BZsum_le2r jz piz ZS1).
apply/(zle_diffP wz (BZm_of_nat_i (NS_succ nN))). 
rewrite - BZopp_p /BZdiff - (BZoppD (ZNz (NS_succ nN)) wz).
apply: BZopp_negative2; rewrite BZsumC -(BZsucc_N nN).
apply/zge0xP; rewrite (BZsumA wz (ZNz nN) ZS1).
move: (zleT (zpartial_sum_mon ha le2) le1).
rewrite (zpartial_sum_rec ha jz).
have vN: natp (Vg c j) by  move: ha => [_ qa qb]; apply: qb; ue.
move: (ZNz vN) => vz.
move/(zle_diffP (ZSs wz vz) (BZm_of_nat_i nN)).
rewrite - BZopp_p /BZdiff - (BZoppD (ZNz nN) (ZSs wz vz)).
move/BZopp_positive2; rewrite (BZopp_K (ZSs (ZNz nN) (ZSs wz vz))).
move/zge0xP; rewrite BZsumC (BZsum_AC wz vz (ZNz nN)).
apply: zleT.
apply/(BZsum_le2l ZS1 vz (ZSs wz (ZNz nN))).   apply/(zle_cN NS1 vN).
apply: (cge1 (CS_nat vN) etc).
Qed.

Lemma supp_right_unbounded_p1 c b: znat_fam c -> intp b ->
  supp_right_unbounded c ->
  exists2 i, intp i & b <=z zpartial_sum c i.
Proof.
move => ha bz hyp.
have h := ZS0.
case/BZ_i0P: bz => bzz.
  move/zgt0xP: bzz => /proj1 bzz.
  by exists \0z; [apply:h | rewrite zpartial_sum_00].
move: (BZ_valN (BZp_sBZ bzz)) => nN.
rewrite - (BZp_hi_pr bzz).
move: (P b) nN; clear b bzz; apply: Nat_induction.
  exists \0z => //; rewrite zpartial_sum_00; apply: (zleR h).
move => n nN [i iN le1]. 
move: (hyp i iN) => [j lij etc]; move: (proj32 lij) => jz.
exists (BZsucc j); first by apply: ZS_succ.
rewrite (zpartial_sum_rec ha jz).
move: (zleT le1 (zpartial_sum_mon ha lij)) => le2.
move/ (BZsum_le2r (proj31 le2) (proj32 le2) ZS1): (le2).
rewrite -/(BZsucc _) (BZsucc_N nN) => le3; apply: (zleT le3).
have vN: natp (Vg c j) by  move: ha => [_ qa qb]; apply: qb; ue.
apply/(BZsum_le2l ZS1 (ZNz vN)  (proj32 le2)); apply/(zle_cN NS1 vN).
apply: (cge1 (CS_nat vN) etc).
Qed.


Lemma supp_left_unbounded_p2 c: znat_fam c ->
  ~ supp_left_unbounded c -> 
  exists2 i, intp i & forall j, j <=z i -> zpartial_sum c j = zpartial_sum c i.
Proof.
move => ha hn.
case:(all_exists_dichot1 (fun i =>exists2 j, j <=z i & Vg c j <> \0c) BZ)=>//.
move => [i iz].
case:(all_exists_dichot2 (fun j => j <=z i /\ Vg c j <> \0c) BZ); last first.
  by move => [j ja [jb jc]]; case; exists j.
move => hyp _.
have h: forall j, j <=z i -> Vg c j = \0c.
  by move => j le;ex_middle bad; case: (hyp _ (proj31 le)).
exists i => //.
apply: BZ_induction_neg => // j lij; move: (proj31 lij) => jz.
rewrite - {1} (BZsucc_pred jz). 
have aux: BZpred j <=z i. exact (zleT (proj1 (zlt_pred jz)) lij).
rewrite (zpartial_sum_rec ha (ZS_pred jz)) (h _ aux).
by rewrite (BZsum_0r (zpartial_sum_int ha (ZS_pred jz))).
Qed.

Lemma supp_right_unbounded_p2 c: znat_fam c ->
  ~ supp_right_unbounded c -> 
  exists2 i, intp i & forall j, i <=z j -> zpartial_sum c j = zpartial_sum c i.
Proof.
move => ha hn.
case:(all_exists_dichot1 (fun i =>exists2 j, i <=z j & Vg c j <> \0c) BZ)=>//.
move => [i iz].
case:(all_exists_dichot2 (fun j => i <=z j /\ Vg c j <> \0c) BZ); last first.
  by move => [j ja [jb jc]]; case; exists j.
move => hyp _.
have h: forall j, i <=z j -> Vg c j = \0c.
  by move => j le;ex_middle bad; case: (hyp _ (proj32 le)).
exists i => //.
apply: BZ_induction_pos => // j lij.
rewrite (zpartial_sum_rec ha (proj32 lij)) (h _ lij).
by rewrite (BZsum_0r (zpartial_sum_int ha (proj32 lij))).
Qed.


Lemma supp_left_unbounded_p3 c (x := zpartial_sum c):
  znat_fam c ->
  ~ supp_left_unbounded c ->  (exists2 i, intp i & Vg c i <> \0c) ->
  exists i, [/\ intp i, x i <z x (BZsucc i)  &
    forall j, intp j -> x i <=z x j] .
Proof.
move => ha hb [k kz xnz].
move:(supp_left_unbounded_p2 ha hb) =>[i]; rewrite -/x => iz ip.
have la: x k <z x (BZsucc k).
  rewrite  /x (zpartial_sum_rec ha kz). 
  apply: (BZsum_Mps (zpartial_sum_int ha kz)).
  have h: natp  (Vg c k) by  move: ha =>[qa qb qc]; apply: qc; ue.
  by move:(cpred_pr h xnz) =>[qa ->]; apply:  BQpsS_fromN1.
case:(zleT_el iz kz); last first.
  move/(zlt_succ2P kz iz) => lb.
  case: (proj2 la);  rewrite (ip _ lb).
  exact:  (ip _ (zleT (proj1 (zlt_succ kz)) lb)).
move => lik.
set A := Zo Nat (fun j => x (i +z (ZN j)) <z x (BZsucc (i +z (ZN j)) )). 
have AN : sub A Nat by apply: Zo_S.
have AE: nonempty A.
  move/(zle_diffP iz kz): lik => dp.
  move:(BZ_valN (ZS_diff kz iz)) => dN.
  by exists (P (k -z i)); apply: Zo_i => //; rewrite (BZp_hi_pr dp) BZsum_diff.
move: (inf_Nat AN AE); set j := intersection _. 
move => [/Zo_P [jN ja] jb].
move:(ZSs iz (ZNz jN)) => rz.
exists (i +z ZN j); split => //.
move => n nz.
suff  -> : x (i +z ZN j) = x i.
  case:(zleT_ee nz iz).
    move/ip => -> ;exact: (zleR (zpartial_sum_int ha iz)).
  by move/(zpartial_sum_mon ha).
suff: forall m, natp m -> m <=c j -> x (i +z ZN m) = x i.
  apply => //; apply:(cleR (CS_nat jN)).
apply: Nat_induction; first by rewrite (BZsum_0r iz).
move => m mN Hrec le. 
rewrite - (Hrec (cleT (cleS mN) le)); ex_middle bad.
move/ (cleSltP mN): le => /cltNge; case.
have le2: (i +z ZN m) <=z (i +z ZN (csucc m)).
  apply /(BZsum_le2l (ZNz mN) (ZNz (NS_succ mN)) iz).
  apply/(zle_cN mN (NS_succ mN)); apply: (cleS mN).
have /jb //: inc m A.
apply: (Zo_i mN).
have<- : (i +z ZN (csucc m)) = (BZsucc (i +z ZN m)).
  by rewrite /BZsucc- (BZsumA iz (ZNz mN) ZS1) - (BZsucc_N mN).
exact: (conj (zpartial_sum_mon ha le2) (nesym bad)).
Qed.


  
  

Lemma fin_disj_fam_prop8l A s t (I :=  (fin_disj_fam_enum_range A)):
  fin_disj_fam A -> supp_left_unbounded (fin_disj_fam_card A) ->
  inc t I -> s <=z t -> inc s I. 
Proof.
move => ha hb ti lst.
move:(fin_disj_fam_prop2 ha)  => cf.
pose x := zpartial_sum (fin_disj_fam_card A).
move: (supp_left_unbounded_p1 cf (proj31 lst) hb) =>[i iz ip]. 
have lt1: BZpred (x i) <z (x i).
  by apply:(BZsum_Mms (proj31 ip)); apply: (BZopp_positive1 ZpsS1).
move: (supp_left_unbounded_p1 cf (proj31_1 lt1) hb) =>[j jz jp]. 
move: (zle_ltT jp lt1) => lt2.
move: (zpartial_sum_mon_bis cf jz iz lt2) => /proj1 lij.
move: (fin_disj_fam_prop7 ha lij lt2) => qr.
apply: (fin_disj_fam_prop5  ha qr ti).
by split => //; exact: (zleT (proj1 lt2) ip).
Qed.

Lemma fin_disj_fam_prop8r A s t (I :=  (fin_disj_fam_enum_range A)):
  fin_disj_fam A -> supp_right_unbounded (fin_disj_fam_card A) ->
  inc t I -> t <=z s -> inc s I. 
Proof.
move => ha hb ti lst.
move:(fin_disj_fam_prop2 ha)  => cf.
pose x := zpartial_sum (fin_disj_fam_card A).
move: (supp_right_unbounded_p1 cf (proj32 lst) hb) =>[i iz ip]. 
have lt1: x i <z  (BZsucc (x i)) by  apply:(BZsum_Mps (proj32 ip) ZpsS1).
move: (supp_right_unbounded_p1 cf (proj32_1 lt1) hb) =>[j jz jp]. 
move: (zlt_leT lt1 jp) => lt2.
move: (zpartial_sum_mon_bis cf iz jz lt2) => /proj1 lij.
move: (fin_disj_fam_prop7 ha lij lt2) => qr.
by apply: (fin_disj_fam_prop5  ha ti qr).
Qed.

Lemma fin_disj_fam_prop9l A (I :=  (fin_disj_fam_enum_range A)):
  fin_disj_fam A -> ~ supp_left_unbounded (fin_disj_fam_card A) ->
  exists2 i, intp i & forall a, inc a I -> i <=z a. 
Proof.
move => ha hb.
move:(fin_disj_fam_prop2 ha)  => cf.
move: (supp_left_unbounded_p2 cf hb)  =>[i iz ]. 
set x := zpartial_sum (fin_disj_fam_card A) => jp.
have xiz: intp (x i) by  apply: zpartial_sum_int.
exists (x i) => // e /Zo_P [ez [a au ea]].
move:(fin_disj_fam_prop1 ha au); set j := (fin_disj_fam_rank A a).
move => [aAi jz].
move:(fin_disj_fam_prop3 ha au); rewrite  ea -/x -/j; move => [qa qb].
case: (zleT_el iz jz) => lij.
   exact: (zleT (zpartial_sum_mon cf lij) qa).
case: (proj2(zle_ltT qa qb)); rewrite (jp _  (proj1 lij)).
by move/(zlt_succ2P jz iz): lij => /jp ->.
Qed.
  
Lemma fin_disj_fam_prop9r A (I :=  (fin_disj_fam_enum_range A)):
  fin_disj_fam A -> ~ supp_right_unbounded (fin_disj_fam_card A) ->
  exists2 i, intp i & forall a, inc a I -> a <z i. 
Proof.
move => ha hb.
move:(fin_disj_fam_prop2 ha)  => cf.
move: (supp_right_unbounded_p2 cf hb)  =>[i iz ]. 
set x := zpartial_sum (fin_disj_fam_card A) => jp.
have xiz: intp (x i) by  apply: zpartial_sum_int.
exists (x i) => // e /Zo_P [ez [a au ea]].
move:(fin_disj_fam_prop1 ha au); set j := (fin_disj_fam_rank A a).
move => [aAi jz].
move:(fin_disj_fam_prop3 ha au); rewrite  ea -/x -/j; move => [qa qb].
case: (zleT_el iz jz) => lij.
  case: (proj2(zle_ltT qa qb)).
  by rewrite (jp _  lij) (jp _ (zleT lij (proj1(zlt_succ jz)))).
by move/(zlt_succ2P jz iz): lij => /(zpartial_sum_mon cf); apply: zlt_leT.
Qed.

Lemma fin_disj_fam_prop9l1 A (I :=  (fin_disj_fam_enum_range A)):
  fin_disj_fam A -> ~ supp_left_unbounded (fin_disj_fam_card A) ->
  nonempty I -> 
  exists2 i, inc i I & forall a, inc a I -> i <=z a. 
Proof.
move => ha hc [u uI].
pose M d := (forall a, inc a I -> d <=z a).
case:(all_exists_dichot2 M I) => // H.
move:(fin_disj_fam_prop9l ha hc) => [b bz bp].
have  aux: forall i, b <=z i -> M (BZsucc i).  
  apply:BZ_induction_pos.
    move => a aI. apply/(zlt_succ2P bz (Zo_S aI)); split; first by apply: bp.
    by move => ba; case: (H a aI); rewrite - ba.
  move => n bn Ms a ai; move: (Ms a ai) => q.
  apply/(zlt_succ2P (ZS_succ (proj32 bn)) (proj32 q)); split => // ee.
  by case:(H a ai); rewrite - ee.
case:(H u uI); move:(bp _ uI); case (equal_or_not b u) => ee; first by ue.
move => ll; move: (proj32 ll) => uz.
by move/ (zlt_pred1P bz (proj32 ll)): (conj ll ee) => /aux; rewrite BZsucc_pred.
Qed.

Lemma fin_disj_fam_prop9r1 A (I :=  (fin_disj_fam_enum_range A)):
  fin_disj_fam A -> ~ supp_right_unbounded (fin_disj_fam_card A) ->
  nonempty I -> 
  exists2 i, inc i I & forall a, inc a I -> a <=z i. 
Proof.
move => ha hc [u uI].
pose M d := (forall a, inc a I -> a <=z d).
case:(all_exists_dichot2 M I) => // H.
move:(fin_disj_fam_prop9r ha hc) => [b bz bp].
move/(zlt_pred1P (Zo_S uI) bz): (bp u uI) => ll.
have  aux: forall i, i <=z (BZpred b) -> M i. 
  apply:BZ_induction_neg.
    by move => a aI; apply /(zlt_pred1P (Zo_S aI) bz); apply: bp.
  move => n na mn a aI.
  move:(mn a aI); case: (equal_or_not a n) => ean.
    by  case: (H _ aI); rewrite ean.
  by move => lan; apply/(zlt_pred1P(proj31 lan) (proj32 lan)).
case:(H u uI); exact: (aux _ ll).
Qed.

Definition zint_k1 x := x = BZ.
Definition zint_k2 x := x = emptyset.
Definition zint_k3 x := exists2 a, intp a & forall t, inc t x <-> a <=z t.
Definition zint_k4 x := exists2 a, intp a & forall t, inc t x <-> t <=z a.
Definition zint_k5 x :=
  exists a b, a <=z b /\ forall t, inc t x <-> zbetween_eq t a b.

Lemma fin_disj_fam_prop10a A (c := fin_disj_fam_card A):
  fin_disj_fam A -> 
  supp_left_unbounded c -> supp_right_unbounded c ->  
  zint_k1 (fin_disj_fam_enum_range A).
Proof.
move => ha hb hc.
set_extens t; [ by move/Zo_S | move => tz].
set I := (fin_disj_fam_enum_range A).
have [u uI]: nonempty I.
  move: (hb _ ZS0) =>[j /proj31 jz /(fin_disj_fam_prop7_aux ha jz) w]; ex_tac.
case:(zleT_ee tz (Zo_S uI)) => ll.
  exact:(fin_disj_fam_prop8l  ha hb uI ll).
exact:(fin_disj_fam_prop8r ha hc uI ll).
Qed.

Lemma fin_disj_fam_prop10b A (c := fin_disj_fam_card A):
  fin_disj_fam A -> 
  supp_left_unbounded c -> ~supp_right_unbounded c ->  
  zint_k4 (fin_disj_fam_enum_range A).
Proof.
move => ha hb hc.
set I := (fin_disj_fam_enum_range A).
have nei: nonempty I.
  move: (hb _ ZS0) =>[j /proj31 jz /(fin_disj_fam_prop7_aux ha jz) w]; ex_tac.
move: (fin_disj_fam_prop9r1 ha hc nei) =>[d di dp].
exists d; first exact(Zo_S di).
move => t; split; [by apply: dp | move => lrd].
exact:(fin_disj_fam_prop8l ha hb di lrd).
Qed.

Lemma fin_disj_fam_prop10c A (c := fin_disj_fam_card A):
  fin_disj_fam A -> 
  ~ supp_left_unbounded c -> supp_right_unbounded c ->  
  zint_k3 (fin_disj_fam_enum_range A).
Proof.
move => ha hb hc.
set I := (fin_disj_fam_enum_range A).
have nei: nonempty I.
   move: (hc _ ZS0) =>[j /proj32 jz /(fin_disj_fam_prop7_aux ha jz) w]; ex_tac.
move: (fin_disj_fam_prop9l1 ha hb nei) =>[d di dp].
exists d; first exact(Zo_S di).
move => t; split; [by apply: dp | move => lrd].
exact:(fin_disj_fam_prop8r ha hc  di lrd).
Qed.
  
  
Lemma fin_disj_fam_prop10d A (c := fin_disj_fam_card A):
  fin_disj_fam A -> 
  ~ (exists2 i, intp i & nonempty (Vg A i)) ->
  zint_k2 (fin_disj_fam_enum_range A).
Proof.
move => ha hb; apply/set0_P => i /Zo_P [iz [x /setUb_P [k ka kb]]].
case: hb; exists k; [by rewrite /intp - (proj42 ha) | ex_tac ].
Qed.

  
Lemma fin_disj_fam_prop10e A (c := fin_disj_fam_card A):
  fin_disj_fam A -> 
  (exists2 i, intp i & nonempty (Vg A i)) ->
  ~ supp_left_unbounded c -> ~ supp_right_unbounded c ->  
  zint_k5 (fin_disj_fam_enum_range A).
Proof.
move => ha [i0 i9z nn] hb hc.
have ru: inc (rep (Vg A i0)) (unionb A).
  by apply/setUb_P; exists i0; [ rewrite (proj42 ha) | apply: rep_i].
move:(fin_disj_fam_enum_range_p1 ha ru).
set k := fin_disj_fam_enum _ _ => kI.
have neI: nonempty (fin_disj_fam_enum_range A) by exists k.
move: (fin_disj_fam_prop9l1 ha hb neI) =>[l li lp].
move: (fin_disj_fam_prop9r1 ha hc neI) =>[r ri rp].
move: (zleT (lp _ kI) (rp _ kI)) => llr.
exists l, r; split => // z; split.
  move => zI; split; [exact:(lp _ zI) |  exact:(rp _ zI)].
move => q; exact:(fin_disj_fam_prop5 ha  li ri q).
Qed.

Definition fdfc := fin_disj_fam_card. 

Definition Exercise6_32_in A B k0 :=
  forall n l, intp n -> natp l -> \1c <=c l ->
     csumb (ZN_int n \0c l) (Vg (fdfc A)) <=c
     csumb (ZN_int n k0 (l +c k0)) (Vg (fdfc B)).

Definition Exercise6_32_hyp A B k0 :=
 [/\ fin_disj_fam A,  fin_disj_fam B,
  Exercise6_32_in A B k0 & Exercise6_32_in B A k0].


Lemma  Ex6_32p0 n: intp n ->  (n -z ZN \0c) = n.
Proof.
by move => nz; rewrite -/ \0z /BZdiff BZopp_0 (BZsum_0r nz). 
Qed.

Lemma Ex6_32p1 n: intp n ->  ZN_int n \0c \1c = doubleton n (BZsucc n).
Proof.
move => nz.
move: (ZN_intP nz NS0 NS1); rewrite (Ex6_32p0 nz) => H.
move: (proj1 (zlt_succ nz)) => la.
set_extens t.
  move/H =>[ha hb]; case: (equal_or_not t (BZsucc n)) => ee.
    rewrite ee; apply: set2_2.
  move/(zlt_succ1P (proj32 ha) (proj31 ha)): (conj hb ee) => ltn.
  by rewrite - (zleA ha ltn); apply: set2_1.
case/set2_P => ->.
  by apply/H; split => //; apply:(zleR nz).
by apply/H; split => //; apply: (zleR (ZS_succ nz)).
Qed.

Lemma Ex6_32p2 n f: intp n ->
    csumb (ZN_int n \0c \1c) f = f n +c f (BZsucc n).
Proof.
move => nz.
have h: ~ inc (BZsucc n) (singleton n).
  by move:(nesym (proj2 (zlt_succ nz))) => /set1_P.
by rewrite(Ex6_32p1 nz) - setU2_11 (csumA_setU1 _ h) csum_trivial3 csum2cl.
Qed.

Lemma Ex6_32p3 n f: intp n -> cardinalp (f n) ->
  f n <=c csumb (ZN_int n \0c \1c) f.
Proof.
by move => ha hb; rewrite (Ex6_32p2 _ ha); apply: csum_M0le.
Qed.


Lemma Ex6_32p3' n f: intp n -> cardinalp (f (BZsucc n)) ->
  f (BZsucc n) <=c csumb (ZN_int n \0c \1c) f.
Proof.
by move => ha hb; rewrite (Ex6_32p2 _ ha); apply: csum_Mle0.
Qed.

Lemma Ex6_32pk0 A B: Exercise6_32_hyp A B \0c ->
  forall n, intp n -> Vg A n =c Vg B n.
Proof.
move => [Ap Bp Ha Hb] n nz.
have ra: forall f m, intp m -> 
   csumb (ZN_int m \0c \2c) f = (f m +c f (BZsucc m)) +c f (BZsucc (BZsucc m)).
  move => f m mz.
  have eq1: m +z (ZN \2c) =   (BZsucc (BZsucc m)).
    by rewrite /BZsucc - (BZsumA mz ZS1 ZS1) (BZsum_cN NS1 NS1) csum_11.
  set I := (ZN_int m \0c \1c).
  move: (zlt_succ mz) => la. 
  move: (proj1 (zlt_succ (ZS_succ mz))) => lb.
  have Is: ~ inc (BZsucc (BZsucc m))  I.
    move/(ZN_intP mz NS0 NS1) =>[_ ].
    by move/(zleSSP (ZS_succ mz) mz); apply: zltNge. 
  have ->: (ZN_int m \0c \2c) = I +s1  (BZsucc (BZsucc m)).
    set_extens t.
      move/(ZN_intP mz NS0 NS2) =>[qa]; rewrite eq1; case/zle_eqVlt.
        move ->; apply: setU1_1.
      move/(zlt_succ1P (proj32 qa) (ZS_succ mz)) => qb.
      by apply: setU1_r;  apply(ZN_intP mz NS0 NS1).
    move => h; apply /(ZN_intP mz NS0 NS2); rewrite eq1.
    case/setU1_P:h.
      move/(ZN_intP mz NS0 NS1) => [qa qb]; split => //; exact: (zleT qb lb).
      move ->; split; last exact:(zleR (ZS_succ (ZS_succ mz))).
    rewrite (Ex6_32p0 mz); exact: (zleT (proj1 la) lb).
  by rewrite (csumA_setU1 _ Is) (Ex6_32p2 _ mz).
pose Ac := (fin_disj_fam_card A).
pose Bc := (fin_disj_fam_card B).
have rb m: intp m ->
   csumb (ZN_int m \0c \2c) (Vg Ac) = csumb (ZN_int m \0c \2c) (Vg Bc).
   move => mz.
   move:(Ha m \2c mz NS2 (proj1 clt_12)) (Hb _ _  mz NS2 (proj1 clt_12)).
   by rewrite (csum0r CS2);apply: cleA.
have rc m: intp m ->
   csumb (ZN_int m \0c \1c) (Vg Ac) = csumb (ZN_int m \0c \1c) (Vg Bc).
   move => mz.
   move:(Ha _ _  mz NS1 (cleR CS1)) (Hb _ _  mz NS1 (cleR CS1)).
   by rewrite  (csum0r CS1);apply: cleA.
move: (ZS_pred (ZS_pred nz))  (ZS_pred nz) => mz smz.
move: (rc _ mz) (rb _ mz). 
rewrite (ra _ _ mz) (ra _ _ mz) (Ex6_32p2 _ mz) (Ex6_32p2 _ mz).
move ->.
rewrite (BZsucc_pred smz) (BZsucc_pred nz).
set v := (Vg Bc (BZpred (BZpred n)) +c Vg Bc  (BZpred n)).
move: (fin_disj_fam_prop2 Bp) => [qa qb qc].
have vN: natp v by apply:NS_sum; apply:qc; rewrite qb.
have Ann: natp (Vg Ac n). 
  case:  (fin_disj_fam_prop2 Ap) => [sa sb sc]; apply: sc; ue.
have Bnn:  natp (Vg Bc n) by apply: qc; ue. 
by move/(csum_eq2l vN Ann Bnn); rewrite /Ac /Bc /fin_disj_fam_card; bw.
Qed.


Lemma Ex6_32p4a A B k0 n:  Exercise6_32_hyp A B k0 -> natp k0 -> intp n ->
  Vg (fdfc A) n <=c csumb (ZN_int n k0 (\1c +c k0)) (Vg (fdfc B)).
Proof.
move => [ha hb hc hd] kN nz.
have h: cardinalp (Vg (fdfc A) n)
  by rewrite /fdfc /fin_disj_fam_card; bw; fprops.
exact: (cleT (Ex6_32p3 nz h) (hc _ _ nz NS1 (cleR CS1))).
Qed.


Lemma Ex6_32p4a' A B k0 n:  Exercise6_32_hyp A B k0 -> natp k0 -> intp n ->
  Vg (fdfc A) (BZsucc n) <=c csumb (ZN_int n k0 (\1c +c k0)) (Vg (fdfc B)).
Proof.
move => [ha hb hc hd] kN nz. move:(ZS_succ nz) => q.
have h: cardinalp (Vg (fdfc A) (BZsucc n))
  by rewrite /fdfc /fin_disj_fam_card; bw; fprops.
exact: (cleT (Ex6_32p3' nz h)  (hc _ _ nz NS1 (cleR CS1))).
Qed.

Lemma Ex6_32_HS A B k0:  Exercise6_32_hyp A B k0 ->
  Exercise6_32_hyp B A k0.
Proof. by move =>[qa qb qc qd]; split. Qed.


Lemma Ex6_32p4b  A B k0 i:  Exercise6_32_hyp A B k0 -> natp k0 ->
  intp i -> (forall k, i <=z k -> Vg (fdfc A) k = \0c) ->
   forall k, i +z (ZN k0) <=z k ->  Vg (fdfc B) k = \0c.
Proof.
move => /Ex6_32_HS Hab kN zi H k k1.
move: (Ex6_32p4a Hab kN (proj32 k1)); rewrite /csumb; set s := csum _.
suff: s = \0c by move => -> /cle0.
have k0z := ZNz kN.
have k2: i <=z k -z ZN k0.
   move/ (BZsum_le2r (ZSs zi k0z) (proj32 k1) (ZSo k0z)): k1.
   by rewrite -/(_ -z _) BZsumC BZdiff_sum.
apply / csum_zero_unit_bis => j; aw => jj; bw => //.
move/(ZN_intP (proj32 k1) kN (NS_sum NS1 kN)): jj => /proj1 ww.
by apply: H; move: (zleT k2 ww).
Qed.


Lemma Ex6_32p4b'  A B k0 i:  Exercise6_32_hyp A B k0 -> natp k0 ->
  intp i -> (forall k, k <=z i -> Vg (fdfc A) k = \0c) ->
   forall k, k <=z i -z (ZN k0) ->  Vg (fdfc B) k = \0c.
Proof.
move => /Ex6_32_HS Hab kN zi H k k1.
have kz := (proj31 k1).
move: (Ex6_32p4a' Hab kN (ZS_pred kz)); rewrite /csumb; set s := csum  _.
rewrite (BZsucc_pred kz).
suff: s = \0c by move => -> /cle0.
have k0z := ZNz kN.
have k2: k +z ZN k0 <=z i.
   move/(BZsum_le2r kz (proj32 k1) k0z): k1.
   by rewrite BZsum_diff1.
apply / csum_zero_unit_bis => j; aw => jj; bw => //.
move /(ZN_intP (ZS_pred kz) kN (NS_sum NS1 kN)): jj => /proj2.
rewrite - (BZsum_cN NS1 kN) (BZsumA (ZS_pred kz) ZS1 k0z).
rewrite -/(BZsucc _) (BZsucc_pred kz) => ww.
by apply: H; move: (zleT ww k2).
Qed.


Lemma Ex6_32p4c1  A B k0:  Exercise6_32_hyp A B k0 -> natp k0 ->
  ~ supp_left_unbounded (fdfc A) -> ~ supp_left_unbounded (fdfc B).
Proof.
move => Hab kn hh. 
case:(all_exists_dichot2
        (fun a  => forall x, x <=z a -> Vg (fdfc A) x = \0c) BZ).
   move => H; case: hh => i iz.
   case:(all_exists_dichot2 (fun j => j <=z i /\  Vg (fdfc A) j <> \0c) BZ).
     move => HH; case: (H _ iz) => x xx; ex_middle bad.
     by case:(HH _ (proj31 xx)).
   by move => [j _ [HA HB]]; exists j.
move =>[a az etc].
move: (Ex6_32p4b' Hab kn az etc) => Ha bad.
by move: (bad _ (ZS_diff az (ZNz kn))) => [j lja]; case; apply: Ha.
Qed.

Lemma Ex6_32p4c2  A B k0:  Exercise6_32_hyp A B k0 -> natp k0 ->
  ~ supp_right_unbounded (fdfc A) -> ~ supp_right_unbounded (fdfc B).
Proof.
move => Hab kn hh. 
case:(all_exists_dichot2
        (fun a  => forall x, a <=z x -> Vg (fdfc A) x = \0c) BZ).
   move => H; case: hh => i iz.
   case:(all_exists_dichot2 (fun j => i <=z j /\  Vg (fdfc A) j <> \0c) BZ).
     move => HH; case: (H _ iz) => x xx; ex_middle bad.
     by case:(HH _ (proj32 xx)).
   by move => [j _ [HA HB]]; exists j.
move =>[a az etc].
move: (Ex6_32p4b Hab kn az etc) => Ha bad.
by move: (bad _ (ZSs az (ZNz kn))) => [j lja]; case; apply: Ha.
Qed.


Lemma Ex6_32p4c3  A B k0:  Exercise6_32_hyp A B k0 -> natp k0 ->
 supp_left_unbounded (fdfc A) -> supp_left_unbounded (fdfc B).
Proof.
move => /Ex6_32_HS ha hb hc; ex_middle hd.
by case:(Ex6_32p4c1 ha hb hd). 
Qed.


Lemma Ex6_32p4c4  A B k0:  Exercise6_32_hyp A B k0 -> natp k0 ->
  supp_right_unbounded (fdfc A) -> supp_right_unbounded (fdfc B).
Proof.
move => /Ex6_32_HS ha hb hc; ex_middle hd.
by case:(Ex6_32p4c2 ha hb hd). 
Qed.

Lemma Ex6_32p4d  A B k0:  Exercise6_32_hyp A B k0 -> natp k0 ->
  (exists2 i, intp i & nonempty (Vg B i)) ->
  exists2 i, intp i & nonempty (Vg A i).
Proof.
move => ha hb [i iz /card_nonempty1 nai]; move: (ZNz hb) => kz.
case:(all_exists_dichot2 (fun j => nonempty (Vg A j)) BZ) => // H.
have h: forall j, j <=z i +z (ZN k0) -> (Vg (fdfc A) j) = \0c.
  move => j /proj31 jz; rewrite (LgV jz); move:(H j jz) => /nonemptyP.
  by case: (equal_or_not (Vg A j) emptyset) => // -> _; rewrite cardinal_set0.
case: nai;move:(Ex6_32p4b' ha hb  (ZSs iz kz) h).
rewrite (BZdiff_sum1 kz iz) => h1.
by move: (h1 _ (zleR iz)); rewrite (LgV iz). 
Qed.


Definition fdfer := fin_disj_fam_enum_range.

Lemma Ex6_32p5a  A B k0:  Exercise6_32_hyp A B k0 -> natp k0 ->
  supp_left_unbounded (fdfc A) -> supp_right_unbounded (fdfc A) ->
  zint_k1 (fdfer A) /\ zint_k1 (fdfer B).
Proof.
move => ha hb hc hd.
move:(ha) =>[qa qb _ _].
split; apply:fin_disj_fam_prop10a => //.
  by apply:  (Ex6_32p4c3 ha hb hc).
by apply:  (Ex6_32p4c4 ha hb hd).
Qed.


Lemma Ex6_32p5b  A B k0:  Exercise6_32_hyp A B k0 -> natp k0 ->
  supp_left_unbounded (fdfc A) -> ~supp_right_unbounded (fdfc A) ->
  zint_k4 (fdfer A) /\ zint_k4 (fdfer B).
Proof.
move => ha hb hc hd.
move:(ha) =>[qa qb _ _].
split; apply:fin_disj_fam_prop10b => //.
  by apply:  (Ex6_32p4c3 ha hb hc).
by apply:  (Ex6_32p4c2 ha hb hd).
Qed.


Lemma Ex6_32p5c  A B k0:  Exercise6_32_hyp A B k0 -> natp k0 ->
  ~ supp_left_unbounded (fdfc A) -> supp_right_unbounded (fdfc A) ->
  zint_k3 (fdfer A) /\ zint_k3 (fdfer B).
Proof.
move => ha hb hc hd.
move:(ha) =>[qa qb _ _].
split; apply:fin_disj_fam_prop10c => //.
  by apply:  (Ex6_32p4c1 ha hb hc).
by apply:  (Ex6_32p4c4 ha hb hd).
Qed.


Lemma Ex6_32p5d  A B k0:  Exercise6_32_hyp A B k0 -> natp k0 ->
  ~ (exists2 i, intp i & nonempty (Vg A i)) -> 
  zint_k2 (fdfer A) /\ zint_k2 (fdfer B).
Proof.
move => ha hb hc.
move:(ha) =>[qa qb _ _].
split; apply:fin_disj_fam_prop10d => //.
move => hh; case: hc; exact: (Ex6_32p4d ha hb hh).
Qed.


Lemma Ex6_32p5e  A B k0:  Exercise6_32_hyp A B k0 -> natp k0 ->
  (exists2 i, intp i & nonempty (Vg A i)) -> 
  ~ supp_left_unbounded (fdfc A) -> ~supp_right_unbounded (fdfc A) ->
  zint_k5 (fdfer A) /\ zint_k5 (fdfer B).
Proof.
move => ha hb hc hd he. 
move:(ha) =>[qa qb _ _].
move: (Ex6_32p4d (Ex6_32_HS ha) hb hc) => hc'.
split; apply:fin_disj_fam_prop10e => //.
  by apply:  (Ex6_32p4c1 ha hb hd).
by apply:  (Ex6_32p4c2 ha hb he).
Qed.

Definition Exercise6_32_conc A B k0:=
  exists f, [/\ bijection_prop f (unionb A) (unionb B),
    forall i x, intp i -> inc x (Vg A i) ->
      exists2 j, inc j (ZN_int i k0 k0) & inc (Vf f x) (Vg B j) &
    forall i x, intp i -> inc x (Vg B i) ->
      exists2 j, inc j (ZN_int i k0 k0) & inc (Vf (inverse_fun f) x) (Vg A j) ].

Definition opp_seq A := Lg BZ (fun i => Vg A (BZopp i)).

Lemma  Exercise6_32_sym A B k0:
   Exercise6_32_conc A B k0 -> Exercise6_32_conc B A  k0. 
Proof.
move => [f [fa fb fc]].
move: (inverse_bij_bp fa)  => fai.
exists (inverse_fun f); split => // i k iz kp.
move:(fb i k iz kp) =>[j ja jb]; exists j => //.
by rewrite (ifun_involutive  (proj1 (proj1 (proj31 fa)))).
Qed.

Lemma opp_seq_p1 A: fin_disj_fam A -> fin_disj_fam (opp_seq A).
Proof. 
rewrite /opp_seq; move =>[qa qb qc qd]; split.
- fprops.
- by aw.
- move => i j; aw; move => iz jz; bw => //.
  move:(ZSo iz) (ZSo jz); rewrite /intp - qb => sa sb.
  by case:(qc _ _ sa sb); [ move/(BZopp_inj iz jz); left | right ].
- move => i; aw =>  iz; bw => //. apply:qd; rewrite qb; exact:(ZSo iz).
Qed.

Lemma opp_seq_p2 A: fin_disj_fam A -> opp_seq (opp_seq A) = A.
Proof. 
move =>[qa qb qc qd]; rewrite/opp_seq; apply: fgraph_exten; aww.
move => i iz; bw => //; [ by rewrite BZopp_K | by apply: ZSo].
Qed.

Lemma opp_seq_p3 A n a b: intp n -> natp a -> natp b ->
  csumb (ZN_int n a b) (Vg A) = csumb (ZN_int (BZopp n) b a) (Vg (opp_seq A)).
Proof.
move => nz aN bN.
move: (ZSo nz) => mz.
set I := (ZN_int (BZopp n) b a).
set J :=  (ZN_int n a b).
have Iz i: inc i I -> intp i by move /(ZN_intP mz bN aN)/ proj1 /proj32.
move: (ZNz aN) (ZNz bN) => az bz. 
suff aux: quasi_bij BZopp I J.
  rewrite (csum_Cn2 _ aux); rewrite /csumb; congr csum; apply: Lg_exten.
  by move => i /Iz iz; rewrite /opp_seq; bw.
split.
- move => i /(ZN_intP mz bN aN) [qa qb]; apply/(ZN_intP nz aN bN).
  split. 
    by move: (zle_opp qb); rewrite (BZoppD mz az) (BZopp_K nz).
  move: (zle_opp qa); rewrite (BZoppD mz (ZSo bz)).
  by rewrite (BZopp_K nz) (BZopp_K bz).
- by move => i j /Iz iz /Iz jz; move/(BZopp_inj iz jz).
- move => i /(ZN_intP nz aN bN) [qa qb].
  move:(proj32 qa) => iz; move:(BZopp_K iz) => mmi.
  exists (BZopp i) =>  //.
  apply/(ZN_intP mz bN aN); split.
    by rewrite /BZdiff - (BZoppD nz bz); apply: zle_opp.
  by rewrite -  (BZopp_K az) - (BZoppD nz (ZSo az));  apply: zle_opp.
Qed.
  
                                 
Lemma opp_seq_p4 A B k :  Exercise6_32_hyp A B k -> natp k ->
     Exercise6_32_hyp (opp_seq A) (opp_seq B) k.
Proof. 
move => [qa qb qc qd] kN.
have Ha i: intp i -> i +z ZN \0c = i by move => iz; rewrite BZsum_0r.
have Hb i: intp i -> i -z ZN \0c = i by move => iz; rewrite BZdiff_0r.
have kz := (ZNz kN).
have aux A1 B1: Exercise6_32_in A1 B1 k
  -> Exercise6_32_in (opp_seq A1) (opp_seq B1) k.
  move => hc => n l nz lN lg1.
  move: (ZSo nz) (ZNz lN) => mz lz.
  rewrite (opp_seq_p3 _ nz NS0 lN).
  rewrite (opp_seq_p3 _ nz kN (NS_sum lN kN)).
  have ra: intp (BZopp n -z ZN l) by apply: (ZS_diff mz lz).
  move: (hc ((BZopp n) -z (ZN l)) l ra lN lg1). 
  have ->: (ZN_int (BZopp n -z ZN l) \0c l) = (ZN_int (BZopp n) l \0c).
    by rewrite /ZN_int (Ha _ mz) (Hb _ ra) (BZsum_diff1 lz mz). 
  have -> :(ZN_int (BZopp n -z ZN l) k (l +c k)) = 
      (ZN_int (BZopp n) (l +c k) k).
    rewrite /ZN_int.
    rewrite - (BZsumA mz (ZSo lz) (ZNz (NS_sum lN kN))).
    rewrite - (BZsum_cN lN kN) (BZsumC (BZopp (ZN l))) -/(_ -z _).
    rewrite (BZdiff_sum lz kz) BZdiff_diff2 //.
  congr (_ <=c _); rewrite /csumb; apply: f_equal; apply: Lg_exten => //.
    move => i /(ZN_intP mz lN NS0) /proj1/proj32 iz; move: (ZSo iz) => miz.
    by rewrite /fdfc /opp_seq /fin_disj_fam_card;bw => //; rewrite (BZopp_K iz).
   move => i /(ZN_intP mz (NS_sum lN kN) kN) /proj1/proj32 iz.
   move: (ZSo iz) => miz.
   by rewrite /fdfc /opp_seq /fin_disj_fam_card;bw => //; rewrite (BZopp_K iz).
move: (aux _ _ qc) (aux _ _ qd) => r1 r2.
by move: (opp_seq_p1 qa)(opp_seq_p1 qb) => ra rb; split.
Qed.
                         
Lemma opp_seq_p5 A B k : fin_disj_fam A -> fin_disj_fam B ->
  Exercise6_32_conc A B k -> natp k ->
  Exercise6_32_conc (opp_seq A) (opp_seq B) k.
Proof. 
move => [qa qb qc qd][eara rb rc rd][f [bf ha hb]] kN.
move:(ZNz kN) => kz.
exists f; split.
   have ->: (unionb (opp_seq A)) =  unionb A.
    set_extens t => /setUb_P [y ya yb]; apply/setUb_P.
       move: ya yb; rewrite /opp_seq; aw => yz; rewrite(LgV yz) qb.
       exists  (BZopp y) => //; exact: (ZSo yz).
     rewrite qb in ya;move:(ZSo ya) => yc; rewrite /opp_seq; aw.
     by exists (BZopp y) => //; bw => //; rewrite (BZopp_K ya).
   have -> //: (unionb (opp_seq B)) =  unionb B.
   set_extens t => /setUb_P [y ya yb]; apply/setUb_P.
     move: ya yb; rewrite /opp_seq; aw => yz; rewrite(LgV yz) rb.
     exists  (BZopp y) => //; exact: (ZSo yz).
   rewrite rb in ya;move:(ZSo ya) => yc; rewrite /opp_seq; aw.
   by exists (BZopp y) => //; bw => //; rewrite (BZopp_K ya).
- move => i x iz; rewrite /opp_seq; bw => // xi.
  move:(ZSo iz) => oiz.
  move:(ha _ _ oiz xi) => [j /(ZN_intP oiz kN kN) [ja jb] jc].
  move: (proj31 jb) => jz; move:(ZSo jz) => njz.
   exists (BZopp j); last by bw => //; rewrite (BZopp_K jz).
  apply/(ZN_intP iz kN kN); split.
    by  move:(zle_opp jb); rewrite (BZoppD oiz kz) (BZopp_K iz).
  by move:(zle_opp ja); rewrite (BZoppD oiz (ZSo kz))(BZopp_K iz)(BZopp_K kz).
- move => i x iz; rewrite /opp_seq; bw => // xi.
  move:(ZSo iz) => oiz.
  move:(hb _ _ oiz xi) => [j /(ZN_intP oiz kN kN) [ja jb] jc].
  move: (proj31 jb) => jz; move:(ZSo jz) => njz.
   exists (BZopp j); last by bw => //; rewrite (BZopp_K jz).
  apply/(ZN_intP iz kN kN); split.
    by  move:(zle_opp jb); rewrite (BZoppD oiz kz) (BZopp_K iz).
  by move:(zle_opp ja); rewrite (BZoppD oiz (ZSo kz))(BZopp_K iz)(BZopp_K kz).
Qed.

                     
Lemma opp_seq_p6 A:
  supp_left_unbounded (fdfc A) -> ~supp_right_unbounded (fdfc A) ->
  ~ supp_left_unbounded (fdfc (opp_seq A)) /\
  supp_right_unbounded (fdfc (opp_seq A)).
Proof. 
move => ha hb; split.
  dneg h => i iz. move:(h _ (ZSo iz)) =>[j ja jb]; exists (BZopp j).
    by move:(zle_opp ja); rewrite (BZopp_K iz).
  move: (proj31 ja) => jz; move:(ZSo jz) => ojz.
  by move: jb; rewrite /opp_seq /fdfc /fin_disj_fam_card; bw.
move => i iz. move:(ha _ (ZSo iz)) =>[j ja jb]; exists (BZopp j).
  by move:(zle_opp ja); rewrite (BZopp_K iz).
move: (proj31 ja) => jz; move:(ZSo jz) => ojz.
move: jb; rewrite /opp_seq /fdfc /fin_disj_fam_card; bw => //.
by rewrite (BZopp_K jz).
Qed.

Definition zpartial_sum_least x :=
  select (fun i => x i <z x (BZsucc i) /\ forall j , intp j -> x i <=z x j) BZ.

Lemma supp_left_unbounded_p4 c
      (x := zpartial_sum c) (i := zpartial_sum_least x):
  znat_fam c ->
  ~ supp_left_unbounded c ->  (exists2 i, intp i & Vg c i <> \0c) ->
   [/\ intp i, x i <z x (BZsucc i), 
      forall j, j <=z i -> x j = x i &
      forall j, intp j -> x i <=z x j] .
Proof.
move => pa pb pc.
pose p := (fun i => x i <z x (BZsucc i) /\ forall j , intp j -> x i <=z x j).
have Ha: (exists2 i, intp i & p i).
  move:(supp_left_unbounded_p3 pa pb pc) => [j [ia ib ic]].
  by exists j.
have Hb: singl_val2 (inc^~ BZ) p.
  move => a b az p_a bz p_b.
  case:(zleT_ell az bz) =>  //.
     move => /(zlt_succ2P az bz) /(zpartial_sum_mon pa) la.
    case: (zltNge (zlt_leT (proj1 p_a) la) (proj2 p_b a az)).
  move => /(zlt_succ2P bz az) /(zpartial_sum_mon pa) la.
  case: (zltNge (zlt_leT (proj1 p_b) la) (proj2 p_a b bz)).
move: (select_pr Ha Hb). rewrite - [select p BZ]/i; move => [[ia ib] ic].
move;split => // j leji.
exact: (zleA (zpartial_sum_mon pa leji) (ib _ (proj31 leji))).
Qed.

Lemma Exercise6_6_32case2 A B k:
  Exercise6_32_hyp A B k -> natp k ->
~ (exists2 i, intp i & nonempty (Vg A i)) -> 
  Exercise6_32_conc A B k.
Proof.
move => ha hb hc.
case: (p_or_not_p (exists2 i : Set, intp i & nonempty (Vg B i))) => hd.
   by move: (Ex6_32p4d ha hb hd).
move: (proj42 (proj41 ha)) (proj42 (proj42 ha)) => dA dB.
case: (emptyset_dichot (unionb A)) => Ae; last first.
  move:(rep_i Ae) => /setUb_P; rewrite dA; move =>[y ya yb].
  case: hc; exists y => //; ex_tac.
case: (emptyset_dichot (unionb B)) => Be; last first.
  move:(rep_i Be) => /setUb_P; rewrite dB; move =>[y ya yb].
  case: hd; exists y => //; ex_tac.
exists empty_function; rewrite Ae Be; split.
- move:empty_function_function =>[ea eb ec].
  split => //; split;split => //.
    by rewrite eb => i j /in_set0.
  by rewrite ec => j /in_set0.
- move => i x iz xx; case: hc; exists i => //; ex_tac.
- move => i x iz xx; case: hd; exists i => //; ex_tac.
Qed.

Definition fdfe := fin_disj_fam_enum.
Definition fdfe_inv A i :=
  select (fun x => fdfe A x = i) (unionb A).

Lemma fdfe_inv_prop A i (x := fdfe_inv A i):
  fin_disj_fam A ->  inc i (fdfer A) ->
   fdfe A x = i /\ inc x (unionb A). 
Proof.
move => ha /Zo_hi hb.
apply:(select_pr hb) => j k jz <- kz /esym kp.
apply: (fin_disj_fam_prop6 ha jz kz kp).
Qed.

Definition Ex6_32_fctL_aux A B q := 
  (fun x => fdfe_inv B ((fdfe A x) +z q)).
Definition Ex6_32_fctL_gen A B q := 
  Lf  (Ex6_32_fctL_aux A B q) (unionb A) (unionb B).


Lemma Ex6_32p6 A B k0 q:  Exercise6_32_hyp A B k0 -> natp k0 -> intp q ->
  supp_left_unbounded (fdfc A) -> supp_right_unbounded (fdfc A) ->
  bijection_prop (Ex6_32_fctL_gen A B q) (unionb A) (unionb B).
Proof.
move => ha kz qz hb hc. 
move: (ha) =>[Ap Bp relA relB].
move: (Ex6_32p5a ha kz hb hc) =>[rA rB].
rewrite /Ex6_32_fctL_gen; split; aw => //.
apply: lf_bijective.
- move => t tu. rewrite /Ex6_32_fctL_aux. 
  move: (ZSs (Zo_S (fin_disj_fam_enum_range_p1 Ap tu)) qz).
  rewrite /intp - rB => aux; exact: (proj2 (fdfe_inv_prop Bp aux)).
- move => u v uua vua.
  move: (Zo_S (fin_disj_fam_enum_range_p1 Ap uua)) => pu.
  move: (Zo_S (fin_disj_fam_enum_range_p1 Ap vua)) => pv.
  move: (ZSs pu qz) (ZSs pv qz); rewrite /intp - rB => pu1 pv1.
  move: (fdfe_inv_prop Bp pu1) (fdfe_inv_prop Bp pv1).
  rewrite /Ex6_32_fctL_aux; set a := fdfe_inv B _; set b := fdfe_inv B _.
  move =>[ra rb] [rc rd] eab.
  move: rc; rewrite  - eab ra => /(BZsum_eq2r pu pv qz).
  by move/(fin_disj_fam_prop6 Ap uua vua).
move => y yub.
move: (Zo_S (fin_disj_fam_enum_range_p1 Bp yub)) => pu.
move:(ZS_diff pu qz); rewrite /intp - rA.
set i := _ -z _; move/Zo_P =>[iz [x xu iv]].
exists x => //.
rewrite /Ex6_32_fctL_aux /fdfe iv /i (BZsum_diff1 qz pu).
rewrite - rB in pu.
move: (fdfe_inv_prop Bp pu) =>[wa wb].
by move/(fin_disj_fam_prop6 Bp wb yub): wa. 
Qed.

          
  

  

(* ----------------- *)





(** Exercise 6 33 *)

Lemma CIS_next x: infinite_c x -> infinite_c (cnext x).
Proof.
move => icx. move: (cnext_pr1 (proj1 icx)) => [_  [ha _] _].
exact: (cle_inf_inf icx ha).
Qed.

Lemma csum_pr1_bnd X f c: (forall i, inc i X -> cardinal (f i) <=c c) ->
  cardinal (unionf X f) <=c  c *c X.
Proof.
move => H.
move: (csum_pr1 (Lg X f)).
have ->: unionb  (Lg X f) = unionf X f.
  rewrite /unionb; aw;apply:setUf_exten => x xs;rewrite LgV//.
rewrite /csumb Lgd  - csum_of_same.
set f1 := Lg  _ _ => l1.
set f2 := cst_graph  X c.
have sd: domain f1 = domain f2 by  rewrite /f1/f2/cst_graph; aw.
have pb: (forall x, inc x (domain f1) -> Vg f1 x <=c Vg f2 x).
  by rewrite /f1/f2/cst_graph;aw => x xa; rewrite !LgV//; apply:H.
exact: (cleT l1 (csum_increasing sd pb)). 
Qed.

Section Exercise6_33.
Variables a b F: Set.
Hypothesis ha: \2c <=c a.
Hypothesis hb: \1c <=c b.
Hypothesis iab: infinite_c a \/ infinite_c b.
Hypothesis HF1: a ^c b <c cardinal F.
Hypothesis HF2: forall x, inc x F -> cardinal x <=c b.
Definition Ex6_33_conc:= 
   exists G q, [/\ sub G F , a ^c b <c cardinal G &
   forall a b, inc a G -> inc b G -> a <> b -> a \cap b = q].

Definition E6_33_c := cnext (a ^c b).
Let c := E6_33_c.

Lemma Exercise6_33a: infinite_c (a ^c b).
Proof.
have bnz := nesym (proj2(clt_leT clt_01 hb)).
case iab => iiab; [apply: (CIS_pow iiab bnz) | apply:(CIS_pow3 ha iiab) ].
Qed.

Lemma Exercise6_33aP x: x <c c <->  x <=c a ^c b. 
Proof. exact:  (cnext_pr4P (CS_pow a b) x). Qed.

Lemma Exercise6_33b : a ^c b  <c c.
Proof. exact (cnext_pr2 (proj1 (Exercise6_33a))). Qed.

Lemma Exercise6_33c: infinite_c c.
Proof. exact: (CIS_next Exercise6_33a). Qed.


Lemma Exercise6_33a1: a ^c (b *c b)  =  a ^c b.
Proof.
case: (finite_or_infinite (proj32 hb)) => fb; last by rewrite csquare_inf.
case: iab => fa; last by rewrite csquare_inf.
move: fb => /NatP fb.
by rewrite cpow_pow {1} (cpow_inf fa fb (nesym (proj2(clt_leT clt_01 hb)))).
Qed.

Lemma Exercise6_33a2: (a ^c b) ^c b  =  a ^c b.
Proof. by rewrite - cpow_pow Exercise6_33a1. Qed.


Lemma Exercise6_33a3: b <c a ^c b.
Proof. exact: (clt_leT (cantor (proj32 hb)) (cpow_Mleeq b ha card2_nz)). Qed.

Lemma Exercise6_33a4: b <c c.
Proof. apply/Exercise6_33aP; exact (proj1 Exercise6_33a3). Qed.

Lemma Exercise6_33a5 x : x <=c c -> x <=c a^c b \/ x = c.
Proof. by case/ cle_eqVlt; [ right | move/Exercise6_33aP; left]. Qed.

Lemma Exercise6_33a6 (bb := cnext b) :
  [/\ ordinalp bb, bb <c c, 
    forall t, ordinalp t -> (t <o bb <-> cardinal t <=c b) &
    forall t, inc t bb -> ordinalp t /\ cardinal t <=c b ].
Proof.
move:  (cnext_pr1 (proj32 hb)) =>[qa qb qc].
have obb: ordinalp bb by case: qa.
have bbc: bb <c c by apply/Exercise6_33aP; apply/ qc; exact: Exercise6_33a3.
have aux t: ordinalp t -> t <o bb <-> cardinal t <=c b.
  move => ot; move: (ocle2P qa ot) => h; split => //.
    by move/h => hh; apply: (cnext_pr4 (proj32 hb)).
  by move => hh; apply/h; apply: (cle_ltT hh qb).                
split => // t /(oltP obb) tlb; move: (proj31_1 tlb) => ot.
by split => //;apply/ (aux t ot).
Qed.


Definition E6_33_X := 
   choose (fun f => injection_prop f c  (F -s1 emptyset)).
Let X := E6_33_X.
Definition E6_33_M := unionb (Lg c (Vf X)).
Let M := E6_33_M.


Lemma Exercise6_33d:  injection_prop X c (F -s1 emptyset).
Proof.
suff:exists f0, injection_prop f0 c (F -s1 emptyset) by apply:choose_pr.
apply/eq_subset_cardP1.
move:(cle_inf_inf Exercise6_33a (proj1 HF1)) => /infinite_setP iF.
rewrite - (card_setC1_inf _ iF) (card_card (proj1 Exercise6_33c)).
by apply/(cnext_pr5P (proj31_1 HF1)).
Qed.

Lemma Exercise6_33d1 n: inc n c -> inc (Vf X n) F.
Proof.
move: Exercise6_33d => [[fx ix] <- tx] ns.
by move: (Vf_target fx ns); rewrite tx => /setC1_P [].
Qed.

Lemma Exercise6_33d2 n: inc n c -> cardinal (Vf X n) <=c b.
Proof. by move /Exercise6_33d1; apply: HF2. Qed.

Lemma Exercise6_33d3 n: inc n c -> nonempty (Vf X n).
Proof.
move: Exercise6_33d => [[fx ix] <- tx] ns.
by move: (Vf_target fx ns); rewrite tx => /setC1_P [_] /nonemptyP.
Qed.


Lemma Exercise6_33e n: inc n c -> sub (Vf X n) M.
Proof.
move: Exercise6_33d => [[fx ix] sx tx].
rewrite /E6_33_M => nc t tw; apply /setUb_P; aw;ex_tac;rewrite LgV//. 
Qed.

Lemma Exercise6_33f: cardinal M = c.
Proof.
have bnz := nesym (proj2(clt_leT clt_01 hb)).
have le: cardinal M <=c c.
  set f := (Lg E6_33_c (fun z => Vf X z)).
  apply: (cleT (csum_pr1 f)). 
  set f1 := (Lg (domain f) (fun z => cardinal (Vg f z))). 
  set g := cst_graph c b.
  have f1x: fgraph f1 by rewrite /f1/cst_graph; fprops.
  have gx: fgraph g by rewrite /g/cst_graph; fprops.
  have sd: domain f1 = domain g by  rewrite /f1 /g /f /cst_graph; aw.
  have le1: (forall x, inc x (domain f1) -> Vg f1 x <=c Vg g x).
    rewrite /f1/f/g/cst_graph; aw => x xd; rewrite !LgV//. 
    by apply: HF2; apply:Exercise6_33d1.
  move: (csum_increasing sd le1);rewrite [csum g] csum_of_same. 
  by rewrite cprodC (cprod_inf (proj1 Exercise6_33a4) Exercise6_33c bnz).
case: (Exercise6_33a5 le) => //le1.
set T1:= fun_image (functions b M) Imf; set T := T1 +s1 emptyset.
move: (Exercise6_33d) => [[fx ix] sx tx].
have pa: forall i, inc i  c -> inc (Vf X i) T.
  move => i ic.
  move: (ic); rewrite - sx => ic'.
  move: ((Vf_target fx) _ ic'); rewrite tx =>/setC1_P [wf _].
  move: (HF2 wf) => cl.
  case: (emptyset_dichot (Vf X i))=> wne; first by rewrite wne /T; fprops.
  apply /setU1_P; left; aw.
  move: cl; rewrite - {1} (card_card (proj32 hb)) => le2.
  have /set_leP [c2 cb ecb]:  (Vf X i) <=s b.
    apply /(eq_subset_cardP); exact: (cardinal_le_aux1 le2).
  have [f [bf sf tf]]: c2 \Eq Vf X i by apply: EqS.
  pose g z := Yo (inc z c2) (Vf f z) (rep (Vf X i)).
  have pa: forall z, inc (g z)  (Vf X i).
    move => z; rewrite /g; Ytac zc; last by  apply: rep_i.
    rewrite -tf; Wtac; fct_tac.
  have pb: forall z, inc z (Vf X i) -> exists2 i, inc i b & g i = z.
    rewrite -tf; move=> z ztf; move: ((proj2 (proj2 bf)) _ ztf)=> [y ysf ->].
    rewrite sf in ysf; exists y;  [by apply: cb | by rewrite /g; Ytac0].
    have pc:  lf_axiom g b M.
    by move => z zb; move: (pa z) => i1; apply /setUb_P; aw; ex_tac; bw.
  set G := Lf g b M.
  have fg: function G by apply: lf_function.
  have pd: inc G (functions b M).  
    by rewrite /G;apply /functionsP;saw.
  apply /funI_P;ex_tac; symmetry;set_extens t.
    move /(Imf_P fg) => [u usg ->]. 
    by rewrite /G;aw; rewrite LfV//; move: usg; rewrite /G; aw. 
  move =>  tw; move: (pb _ tw) => [z zi <-]; apply /(Imf_P fg).
  by exists z; rewrite /G; aw;bw.
have : c <=s T.
  exists (Lf (fun z => (Vf X z))  c  T); saw.
  apply: lf_injective; first by apply: pa.
  by rewrite - sx; apply: ix.
move /eq_subset_cardP1; rewrite (card_card (proj32 le)) => eq1.
set aa:= (functions b M).
have sj: (surjection (Lf Imf aa (fun_image aa Imf))).
  apply: lf_surjective.
    by move=> t ta; apply /funI_P;exists t.
  by move=> y /funI_P.
move: (image_smaller (proj1 sj)).
move: (surjective_pr0 sj); aw;  move => ->; rewrite /aa  -/T1.
rewrite cpow_pr1 (card_card (proj32 hb)).
have -> : cardinal T1 = cardinal T.
  case: (inc_or_not emptyset T1) => eT. 
    by rewrite /T (setU1_eq eT).
  move: Exercise6_33c => i1.
  move: (cle_inf_inf Exercise6_33c eq1) => /infinite_setP it.
  by rewrite (card_setC1_inf emptyset it) /T (setU1_K eT).
move => l2; move: (cleT eq1 l2) => l3.
case: (equal_or_not (cardinal M) \0c) => mz. 
  by move:l3; rewrite mz (cpow0x bnz) => h; symmetry; apply: cle0.
move: (cpow_Mleeq b le1 mz);  rewrite Exercise6_33a2 => l1.
case: (cltNge  Exercise6_33b (cleT l3 l1)).
Qed.


Definition E6_33_x:= equipotent_ex c M.
Definition E6_33_r :=  
  Vfs (ext_to_prod E6_33_x E6_33_x) (ordinal_o c).
Definition E6_33_rho n := ordinal (induced_order E6_33_r (Vf X n)).
Let rho :=  E6_33_rho.

Lemma Exercise6_33g : bijection_prop E6_33_x c  M.
Proof.
apply:equipotent_ex_pr; apply/card_eqP.
by rewrite Exercise6_33f (card_card (proj1 Exercise6_33c)). 
Qed.

Lemma Exercise6_33h (x := E6_33_x) (r:= E6_33_r):
  [/\ worder_on r M,
  order_isomorphism x  (ordinal_o c) r &
  (forall a b, inc a c -> inc b c ->
     (a <=o b <-> gle r (Vf x a) (Vf x b)))].
Proof.
have oc:= (proj1 (proj1 Exercise6_33c)).
move: (ordinal_o_wor oc) => wo1; move: (wo1) => [o1 _].
have sr1:= (ordinal_o_sr c).
move: Exercise6_33g; rewrite -/x; move => [bx sx tx].
rewrite -{2} sx in sr1.
move: (order_transportation bx (conj o1 sr1)); rewrite /x -/ E6_33_r -/r => oi1.
move: (oi1) => [_ or [_ _ sr2] xinc].
have wo: worder r by apply: worder_invariance wo1; exists  E6_33_x.
rewrite tx in sr2; split => //.
move => u v ux vx.
move: (xinc u v); rewrite sx => H; apply: iff_trans (H ux vx).
move: (ordo_leP c u v) => H1; split =>h.
  by apply/H1; split => //; case: h.
by move/H1: h =>[ _ _ hØ]; split => //; apply: (Os_ordinal oc).
Qed.

Lemma Exercise6_33i n: inc n c ->
  [/\ worder (induced_order E6_33_r (Vf X n)),
   \0o <o rho n & inc (rho n) (cnext b) ].
Proof.
move => ni; rewrite /E6_33_rho.
set r := induced_order _ _.
move: Exercise6_33h => [[wo1 sr] oi oie].
move: (Exercise6_33e ni); rewrite - sr => pa.
have wor: worder r by move: (induced_wor wo1 pa).
move: Exercise6_33d => [[fx ix] ss tx]; rewrite - ss in ni.
move: (Vf_target fx ni); rewrite tx => /setC1_P [/HF2 hc hd].
have he: ordinal r <> \0o.
  move => h2; move:(ordinal0_pr2 wor h2); rewrite /r iorder_sr;fprops.
have or: ordinalp (ordinal r) by apply OS_ordinal.
have op: \0c <o  (ordinal r) by apply: ord_ne0_pos.
have aux: cardinal (ordinal r) <=c b.
  by rewrite (cardinal_of_ordinal wor) (iorder_sr (proj1 wo1) pa).
by move/(proj43 (Exercise6_33a6) _ or): aux => /olt_i h.
Qed.

Definition E6_33_y n := the_ordinal_iso (induced_order E6_33_r (Vf X n)).
Let y := E6_33_y.
Definition E6_33_Mi m := Zo M
    (fun z => exists n, [/\ inc n c, inc m (source (y n)) &
      z = Vf (y n) m]).
Let Mi := E6_33_Mi.
Definition E6_33_alpha := 
   intersection (Zo (cnext b) (fun m => (cardinal (Mi m) = c))).
Let alpha := E6_33_alpha.

Lemma Exercise6_33j n (r := induced_order E6_33_r (Vf X n)):
  inc n c -> 
    [/\ order_isomorphism (y n) (ordinal_o (rho n)) r,
     source (y n) = rho n & target (y n) =  (Vf X n)].
Proof.
move=> nc. 
have pa: order_isomorphism (y n) (ordinal_o (rho n)) r.
  by apply: the_ordinal_iso1; move: (Exercise6_33i nc) => [].
move: (pa) =>  [_ _ [_ -> ->] _].
move: (Exercise6_33h) => [[pe pf] _ _].
by rewrite  ordinal_o_sr /r (iorder_sr (proj1 pe)) // pf;apply: Exercise6_33e.
Qed.

Lemma Exercise6_33k n u v: inc n c -> inc u (rho n) -> inc v (rho n) ->
   (u <=o v <-> gle  E6_33_r  (Vf (y n) u) (Vf (y n) v)).
Proof.
move => nc us vs.
have or: ordinalp (rho n).
  exact: (proj32_1 (proj32 (Exercise6_33i nc))).
move: (Exercise6_33j nc) =>[[qa qb qc qd] st ty].
have usy:  inc u (source (y n)) by ue.
have vsy: inc v (source (y n)) by ue.
move: (qd u v usy vsy) => H.
split => la.
  have: gle (ordinal_o (rho n)) u v.
    by apply/(ordo_leP (rho n) u v); split => //; case:la.
  by move/H; move/iorder_gle1.
have fy: function (y n) by move: (proj31 qc) => bjy; fct_tac.
have:gle (induced_order E6_33_r (Vf X n)) (Vf (y n) u) (Vf (y n) v).
  apply/iorder_gleP; split => //; Wtac.
move:(Os_ordinal or us) (Os_ordinal or vs) => ou ov.
by move/H /ordo_leP/proj33 => suv.
Qed.

Lemma Exercise6_33l: M = unionf (cnext b) Mi.
Proof.
set_extens x; last by move /setUf_P => [t yp /Zo_S].
move: Exercise6_33d => [[fc ix] sx tx].
move => xM; move: (xM) => /setUb_P; aw; move => [t ts]; rewrite LgV// => xW.
move: (Exercise6_33j ts) => [[o1 o2 [bf sf tf] _] sy ty].
rewrite - ty in xW.
move: (proj2 (proj2 bf) _ xW) => [n ns xv].
move:(ordinal_transitive (proj41 (Exercise6_33a6)) (proj33(Exercise6_33i ts))).
rewrite - sy => qa.
by apply /setUf_P; exists n; [apply: qa | apply: (Zo_i xM); exists t].
Qed.


Lemma Exercise6_33m x: inc x (cnext b) -> cardinal (Mi x) <=c c.
Proof.
move => xs.
have s1: sub (Mi x) M
  by move =>t ti; rewrite Exercise6_33l; apply /setUf_P; ex_tac. 
by move: (sub_smaller s1); rewrite Exercise6_33f.
Qed.


Lemma Exercise6_33n: exists2 m, 
  inc m (cnext b) & (cardinal (Mi m)) = c.
Proof.
ex_middle pa; case: (cltNge (Exercise6_33b)).
move /Exercise6_33aP: (proj42 Exercise6_33a6) => hc.
have h: (forall i, inc i (cnext b) -> cardinal (Mi i) <=c a ^c b).
  move => i xab.
  move:(Exercise6_33m xab); case/Exercise6_33a5 => // ee; case: pa; ex_tac.
move:(csum_pr1_bnd h); rewrite - Exercise6_33l Exercise6_33f => q.
rewrite - (csquare_inf Exercise6_33a).
by apply: (cleT q); apply: cprod_Meqle.
Qed.

Lemma Exercise6_33o :
  [/\ inc alpha (cnext b), cardinal (Mi alpha) =  c &
   forall m, inc m alpha -> cardinal (Mi m) <c c].
Proof.
rewrite /alpha/E6_33_alpha; set Z := Zo _ _.
have oab: ordinalp (cnext b) by case : Exercise6_33a6.
have nez: nonempty Z.
   move: Exercise6_33n => [m  ml]; exists m; apply: Zo_i=> //.
have oz: ordinal_set Z by move=> t => /Zo_P [/(Os_ordinal oab) tab _].
move: (least_ordinal0 oz nez) => [_  /Zo_P [lt pb] hz].
split => // m mc.
have xab:= (ordinal_transitive oab lt mc).
case/cle_eqVlt: (Exercise6_33m xab) => // cc.
have /hz bad: inc m Z by apply: Zo_i.
case: (ordinal_decent oab xab (proj33 bad _ mc)).
Qed.

Lemma Exercise6_33p:
   cardinal (unionf alpha Mi) <c c.
Proof.
apply/Exercise6_33aP.
have [h1 h2 h3]:=Exercise6_33o.
move: Exercise6_33a6=>[sa svb sc sd].
have h5 :=  (cleT (proj2 (sd _ h1)) (proj1 (Exercise6_33a3))).
move: (cprod_inf1 h5 Exercise6_33a); rewrite cprod2cr.
apply: cleT; apply:csum_pr1_bnd => m mi.
by apply/Exercise6_33aP;apply: h3. 
Qed.


Definition E6_33_N0 := fun_image (Mi alpha)
   (fun t => rep (Zo c 
      (fun n =>  inc alpha (source (y n)) /\ Vf (y n) alpha = t))).
Let N0 :=  E6_33_N0.


Lemma Exercise6_33q  (Ma := Mi alpha):
  [/\ forall t, inc t N0 -> 
    [/\ inc t c, inc alpha (source (y t))& inc (Vf (y t) alpha) Ma],
    (forall t1 t2, inc t1 N0 -> inc t2 N0 -> 
      (Vf (y t1) alpha)  = (Vf (y t2) alpha)  -> t1  = t2),
    (forall s, inc s Ma -> exists2 t, inc t N0 & s = (Vf (y t) alpha)),
    sub N0 c &
  cardinal N0 =  c].
Proof.
pose Z z := Zo c
         (fun n =>
          inc alpha (source (y n)) /\ Vf (y n) alpha  = z).
have znz: forall z,  inc z (Mi alpha) -> nonempty (Z z).
  by move => z /Zo_P [zM [n [nc als zv]]]; exists n; apply: Zo_i.
have pa: forall t, inc t N0 -> 
  [/\ inc t c, inc alpha (source (y t)) & inc (Vf (y t) alpha) Ma].
  move => t /funI_P  [z z1 rz].
 move: (rep_i (znz _ z1)); rewrite rz; move /Zo_P => [pa [pb pc]].
 split => //; rewrite pc //.
have pb: (forall t1 t2, inc t1 N0 -> inc t2 N0 -> 
      (Vf (y t1) alpha) = (Vf (y t2) alpha) -> t1  = t2).
  move => t1 t2 t1n t2n sv.
  move: t1n => /funI_P [z z1 rz]. 
  move: (rep_i (znz _ z1)); rewrite rz; move => /Zo_hi  [_ pc].
  move: t2n => /funI_P [z' z1' rz']. 
  move: (rep_i (znz _ z1')); rewrite rz'; move /Zo_hi => [_ pc'].
  by move: pc pc' sv; rewrite - {1}rz - {1} rz' -/alpha  => -> -> ->.
have pc: (forall s, inc s Ma -> exists2 t, inc t N0 & s = Vf (y t) alpha).
  move => s sm.
  set u := rep (Z s).
  have un: inc u N0 by apply /funI_P; rewrite -/Ma; exists s => //.
  exists u => //.
   by move: (rep_i (znz _ sm)) => /Zo_P [_ [_ ->]].
split => //.
  move => t tn; exact: (proj31 (pa _ tn)).
set f:= Lf (fun  t => Vf (y t) alpha) N0 Ma.
have bf: bijection f.
  by apply: lf_bijective => // t ta; move: (pa _ ta) => [_ _ ok].
have: (source f \Eq target f) by exists f; split => //.
rewrite /f; aw; move /card_eqP.
by rewrite - (proj32 Exercise6_33o).
Qed.



Definition E6_33_yr n :=
  Lf (fun t => Vf (y n) t)  alpha (unionf alpha Mi).
Let yr := E6_33_yr.

Lemma  Exercise6_33r n: inc n N0 ->
  [/\ sub alpha (source (y n)),
      inc (yr n) (functions alpha (unionf alpha Mi)) &
   forall i, inc i alpha -> Vf (y n) i = Vf (yr n) i].
Proof.
move => nN.
move: Exercise6_33q => [sa _ _ sd se].
move: (sa _ nN) => [nc asy _ ].
move: (Exercise6_33j nc) => [ [_ _ [bjy _ _] _] sy ty].
have fy: function (y n) by fct_tac.
have osy: ordinalp (source (y n)).
  rewrite sy; exact: (proj32_1 (proj32 (Exercise6_33i nc))).
have Ha t: inc t alpha -> inc t (source (y n)).
  by move/ (oltP osy): asy => /proj1/proj33; apply.
have ax: lf_axiom [eta Vf (y n)] alpha (unionf alpha Mi).
  move => t ta; move: (Ha t ta) => ts.
  move: (Vf_target fy ts); rewrite ty; move/ (Exercise6_33e nc) => qa.
  by apply/setUf_P; exists t => //;  apply: Zo_i => //; exists n.
rewrite /yr /E6_33_yr;split => //.
      by apply /functionsP; saw; apply: lf_function.
by move => i ia; bw. 
Qed.

Definition E6_33_N_prop N z :=
    [/\ cardinal N = c, sub N N0 ,
       inc z (functions alpha (unionf alpha Mi)) &
       forall i, inc i N -> yr i = z].

Lemma  Exercise6_33s: exists N z,  E6_33_N_prop N z.
Proof.
move: Exercise6_33r; set T := functions _ _; move => Ha.
pose f x := Zo N0 (fun n => yr n = x).
have fi i j: inc i T -> inc j T -> i = j \/ disjoint (f i) (f j).
   move => iN jN. mdi_tac u => x /Zo_hi xi /Zo_hi xj.
   by case: u; rewrite - xi xj.
move: (@csum_pr4_bis T f fi).
have ->: (unionf T f) = N0.
  set_extens t.
     by move => /setUf_P [i iN /Zo_P[qa qb]].
  move => tn; apply /setUf_P; exists (yr t); last by apply: Zo_i.
  by move: (proj32 (Ha _ tn)). 
case: (all_exists_dichot1 (fun i=> cardinal (f i) <=c a ^c b) T) => H.
  move: (cltNge Exercise6_33b) => bad.
  pose fa := Lg T (fun x => (cardinal (f x))).
  pose fb := Lg T (fun x => a ^c b).
  have dd: domain fa = domain fb by rewrite /fa /fb; aw.
  have cp: (forall x, inc x (domain fa) -> Vg fa x <=c Vg fb x).
    by rewrite /fa/fb; aw => x xd; bw => //;  apply: H.
  move: Exercise6_33q =>[_ _ n_ _ ->] => eq1.
  move: (csum_increasing dd cp).
  rewrite /fa /fb  -/(csumb _ _) -/(csumb _ _) - eq1 csum_of_same.
  rewrite - cprod2cr  /T - /(cpow _ _) - (cpowcr _ alpha).
  rewrite -  (cpowcl (unionf _ _)).
  case: (equal_or_not (cardinal (unionf alpha Mi)) \0c) => Ms.
    rewrite Ms; case: (equal_or_not (cardinal alpha) \0c) => As.
      by rewrite As cpow00 cprod1r; fprops => w; case: bad.
    rewrite cpow0x // cprod0r => /cle0 cz.
    by case: (infinite_nz (Exercise6_33c)).
  move: (proj2((proj44 (Exercise6_33a6)) _ (proj31 (Exercise6_33o)))) => lab.
  move: Exercise6_33p => /Exercise6_33aP qa.
  move: (cpow_Mlele Ms qa lab);  rewrite - cpow_pow  Exercise6_33a1.
  set w := _ ^c _ => hc hd.
  by move: (cleT hd (cprod_inf1 hc Exercise6_33a)) => cs; case: bad.
case: H => z zT lt1 _.
set N := f z.
have sN0: sub N N0 by apply: Zo_S.
move: (sub_smaller sN0). 
move: Exercise6_33q =>[_ _ _ _ cn0]; rewrite cn0.
case/ cle_eqVlt; [move => cn | by move/(cnext_pr4 (CS_pow a b)) ].
by exists N, z; split => // i /Zo_P[qa qb].
Qed.



Definition E6_33_N := P( choose (fun z => E6_33_N_prop (P z) (Q z))).
Definition E6_33_z := Q( choose (fun z => E6_33_N_prop (P z) (Q z))).
Let N := E6_33_N.

Lemma  Exercise6_33t: E6_33_N_prop N  E6_33_z.
Proof.
set p := (fun z => E6_33_N_prop (P z) (Q z)).
have h: (exists y, p y).
  move: Exercise6_33s =>[n [z etc]]; exists (J n z).
  by rewrite /p; aw.
by move: (choose_pr h).
Qed.

Definition E6_33_Q := Imf E6_33_z.

Lemma Exercise6_33u n: inc n N  -> sub  E6_33_Q (Vf X n).
Proof.
move =>  nN.
move: (Exercise6_33t) => [qa qb qc qd].
rewrite / E6_33_Q - (qd _ nN) => t.
have nn0: inc n N0 by apply: qb.
move: (Exercise6_33r nn0) =>[sc qe qf].
move/functionsP: qe =>[fyr syr tyr].
move/(Imf_P fyr); rewrite syr; move =>[m ma ->].
rewrite - (qf _ ma) .
move: Exercise6_33q =>[_ _ _] snc _.
move: (Exercise6_33j  (snc _ nn0)) => [sa sb <-].
move: sa =>[_ _ /proj31 byn _].
have fyn: function (y n) by fct_tac.
Wtac. 
Qed.

Definition E6_33_res_prop A i :=
   inc i (N -s A) /\
   forall n t, inc n A -> inc t (Vf X n) ->  glt E6_33_r t (Vf (y i) alpha).
Definition E6_33_choose A :=
  choose (fun i =>  E6_33_res_prop A i).


Lemma Exercise6_33v A: sub A N  -> cardinal A <c c ->
  exists i, E6_33_res_prop A i. 
Proof.
move=> sAN cA.
have ic := Exercise6_33c.
have cc := proj1 ic.
move:Exercise6_33q =>[E33q1 E33q2 _ E33q4 _].  
have sNc: sub N c.
  by apply: sub_trans E33q4; case: Exercise6_33t.
set B := unionf A (Vf X). 
have lcBc: cardinal B <c c.
  pose f := Lg A (fun i => cardinal (Vf X i)).
  pose g := Lg A (fun i => b).
  have sd:  domain f = domain g by rewrite /f /g; aw. 
  have la x:  inc x (domain f) -> Vg f x <=c Vg g x.
    rewrite /f /g; aw => xd; bw => //; apply: Exercise6_33d2.
    by apply: sNc; apply: sAN.
  move: (csum_increasing sd la).
  rewrite /g -/(csumb _ _) csum_of_same.
  move: (csum_pr1_bis A (Vf X)); rewrite -/B  /f -/(csumb _ _) => lb lc.
  move: (cleT lb lc).  rewrite - cprod2cr => le.
  exact: (cle_ltT le (cprod_inf5 Exercise6_33a4 cA ic)).
have sbM: sub B M.
  by move => t/setUf_P [u uA etc]; apply: (Exercise6_33e (sNc _ (sAN u uA))).
move: Exercise6_33h; simpl.
set r :=  E6_33_r. set f :=  E6_33_x.
move =>[orM [o1 o2 fbp _] iso].
move: fbp. rewrite (proj2 orM)ordinal_o_sr=> h.
move: (inverse_bij_bp h) => [bif sif tif].
move:h =>[bf sf tf].
have ff: function f by fct_tac.
have fif: function (inverse_fun f) by fct_tac.
have sbM': sub B (source (inverse_fun f)) by ue.
move: (cardinal_image sbM' (proj1 bif)).
set C := Vfs (inverse_fun f) B => cc1.
have sCc:  sub C c by rewrite - tif; apply:fun_image_Starget1.
have cc2: cardinal C <=c a ^c b  by apply/Exercise6_33aP; ue.
move: (cnext_sup Exercise6_33a cc2 sCc) => ra.
pose D := N -s A.
set D1 := fun_image D (fun t => Vf (y t) alpha).
have cD: cardinal D = c.
  move: (proj41 (Exercise6_33t)) => r3.
  have r1: infinite_set N by apply/infinite_setP; rewrite r3.
  have r2:  cardinal A <c cardinal N by rewrite r3.
  by move: (infinite_compl r1 r2); rewrite r3.
have sdd: sub D N0.
  by move => t /setC_P [ta _]; apply: (proj42 (Exercise6_33t)).
have cD1: cardinal D1 = c.
  rewrite - cD; apply: cardinal_fun_image.
  by move => u v uS vD; apply: E33q2; apply: sdd.
have sdM: sub D1 M.
  move => u /funI_P [ t ta ->].
  by move: (E33q1 _ (sdd _ ta)) =>[_ _  /Zo_S mc].
have sdM': sub D1 (source (inverse_fun f)) by ue.
move: (cardinal_image sdM' (proj1 bif)).
set D2 := Vfs (inverse_fun f) D1 => cc3.
have sDc:  sub D2 c by rewrite - tif; apply:fun_image_Starget1.
have cc4: cardinal D2 = c by rewrite cc3.
pose ma := osucc (union C). 
have mac: inc ma c by exact:(proj33 (infinite_card_limit2 Exercise6_33c) _ ra).
have cic := (proj1 Exercise6_33c).
move /cardinalP: (cic) =>[sa sb].
case: (all_exists_dichot1  (fun z => z <o ma) D2) => hu.
  move/(oltP sa): (mac) => /proj1/proj33/sub_smaller; case/cle_eqVlt => la1.
    by move: (sb _ mac); case/card_eqP.
  have: sub D2 ma by move =>t /hu /olt_i.
  by move/sub_smaller; rewrite cc4; case/cleNgt; rewrite - (card_card cic).
move: hu =>[mb mbd bad].
case: (oleT_el (Os_ordinal sa mac) (Os_ordinal sa (sDc _ mbd))) => // la.
have mbp i: inc i C ->  i <o mb.
   move => oic. apply: olt_leT  la; apply /oltSleP; apply: ord_sup_ub => //.
   by move => t /sCc /(Os_ordinal sa).
pose mc := Vf f mb.
have md1: inc mc D1.
  have s1: sub D1 (source (inverse_fun f)) by ue.
  rewrite /mc; move/(Vf_image_P fif s1): mbd => [u ud1 ->].
  by rewrite inverse_V //; rewrite tf; apply: sdM.
have m3s i: inc i B -> glt r i mc.
  move => iB.
  set j := Vf (inverse_fun f) i.  
  have jC: inc j C by  apply/(Vf_image_P fif sbM'); ex_tac.
  move: (mbp _ jC) =>[ta tb].
  move:  (sCc _ jC) (sDc _ mbd) => jc mcc.
  have: glt r (Vf f j) (Vf f mb).
    split;  [by move/(iso j mb jc mcc): ta |  dneg b2 ].
    by rewrite - sf in jc mcc; move: (proj2 (proj1 bf) j mb jc mcc b2). 
  by rewrite /j inverse_V //; ue.
move/funI_P: md1 =>[i uA ee]; exists i; split => //.
by move => n t qa qb; rewrite - ee; apply:m3s; apply/setUf_P; ex_tac.
Qed.

Lemma Exercise6_33w A: sub A N  -> cardinal A <c c ->
   E6_33_res_prop A (E6_33_choose A).
Proof.
by move => qa qb; apply: choose_pr; apply: Exercise6_33v.    
Qed.

Lemma Exercise6_33x
  (T0 := fun z  => E6_33_choose (target z))
  (T := Imf (transfinite_defined (ole_on N) T0)):
  [/\ sub T N,  cardinal T = c &
    forall u v, inc u T -> inc v T -> u <> v -> Vf X u \cap Vf X v = E6_33_Q].
Proof.
move: Exercise6_33t =>[pa pb _ _]. 
move: Exercise6_33q => [_ _ _ pc _].
have pd := sub_trans pb pc.
have oc:=(proj1 (proj1 Exercise6_33c)).
have pe: ordinal_set N by move => t/pd /(Os_ordinal oc).
move: (wordering_ole_pr pe).
set r := (ole_on N); move =>[wor sr].
case: (transfinite_defined_pr T0 wor); set f := transfinite_defined _ _.
rewrite sr; move => sjf sf fprop.
pose fr x :=(restriction1 f (segment r x)).
have axf x: inc x N -> sub (segment r x) (source f).
  move => xn; rewrite sf - sr; apply: sub_segment.
have ff: function f by fct_tac.
have frs x: inc x N -> surjection (fr x).
  move => xN; apply: (restriction1_fs ff (axf _ xN)).
have fri x: inc x N -> Imf (fr x) = target (fr x).
  by  move =>  /frs xn; apply:  surjective_pr0.
have sfr x: inc x N -> source (fr x) = segment r x.
  by move => xN; move: (proj32 (restriction1_prop ff (axf _ xN))).
have ffr x: inc x N -> function (fr x) by move/frs/proj1.
have frsi x: inc x N -> cardinal (target (fr x)) <c c.
  move => xN; rewrite - (fri _ xN).
  move: (ffr _ xN) (sfr _ xN) => fra frb.
  move: (image_smaller fra) => q; apply: (cle_ltT q).
  rewrite frb.
  have: sub  (segment r x) x.
    move => t/segmentP [ /graph_on_P1/proj33 qa qb].
    by apply/(oltP (proj32 qa)).
  move/sub_smaller => q';apply: (cle_ltT q').
  apply:(colt1 (proj1 Exercise6_33c) (pd _ xN)).
pose pr x := sub (target (fr x)) N /\ cardinal (target (fr x)) <c c. 
have prp x: inc x N -> pr x -> inc (Vf f x) N.
  move => xN [qa qb].
  move /setC_P: (proj1 (Exercise6_33w qa qb)) => /proj1.
  by rewrite (fprop _ xN).
set U := Zo N (fun x => ~ pr x).
case: (emptyset_dichot U) => Ue; last first.
  have sU: sub U (substrate r) by rewrite sr; apply: Zo_S.
  move: (worder_prop wor sU Ue) =>[x /Zo_P [xN npx] etc].
  case: npx; split; last by apply: frsi.
  move: (ffr _ xN) (sfr _ xN) => qa qb.
  rewrite - (fri _ xN) => t /(Imf_P qa).
  move => [u us ->]; rewrite qb in us.
  rewrite (restriction1_V ff (axf _ xN) us).
  have lux: glt r u x by apply/segmentP.
  have uN: inc u N by move: (arg1_sr (proj1 lux)); rewrite sr.
  apply: (prp u uN); split; last by apply:   frsi.
  case: (inc_or_not u U) => uU. 
   case: (not_le_gt (proj1 wor) (etc u uU) lux).    
  case: (p_or_not_p (pr u)) => prf; first by case: prf.
  case: uU;  apply: Zo_i => //.
have prs x: inc x N -> pr x.
  by move => xN;ex_middle bad; empty_tac1 x; apply:Zo_i.
have prq x: inc x N ->
  E6_33_res_prop (target (fr x)) (Vf f x).               
  move => xN; move: (prs _ xN) => [qa qb].
  move: (Exercise6_33w qa qb).
  by rewrite fprop.  
have finj: injection f.
  split => // u v; rewrite sf => uN vN sv.
  move: (proj2 (worder_total wor)); rewrite sr => h.
  ex_middle ne.
  wlog: u v uN vN ne sv /(gle r  u v).
    move => H; case: (h u v uN vN) => le1; first by apply:H.
    by symmetry; apply: H => //; apply:nesym.
  move => luv. 
  move: (prq _ vN) =>[/setC_P [ea eb] _]; case: eb.
  have usv: inc u (segment r v) by apply/segmentP.
  rewrite - (fri _ vN); apply/(Imf_P (ffr _ vN)).
  rewrite (sfr _ vN); ex_tac.
  by rewrite (restriction1_V ff (axf _ vN) usv) sv.
have imf x: inc x N -> inc (Vf f x) N.
  by move => xN; case/setC_P: (proj1 (prq _ xN)).
have cp1 u v t: glt r u v -> inc t (Vf X (Vf f u)) -> inc t (Vf X (Vf f v)) -> 
    inc t E6_33_Q.
  move => lt1 tt ttv.
  move: (arg1_sr (proj1 lt1)) (arg2_sr (proj1 lt1)); rewrite sr => uB vN.
  have usc: inc u (segment r v) by  apply/segmentP.
  have qa: inc (Vf f u) (target (fr v)).
    rewrite -(fri _ vN); apply/(Imf_P (ffr _ vN)); exists u=> //.
      by rewrite (sfr _ vN).
    by rewrite (restriction1_V ff (axf _ vN) usc).
  move: (proj2 (prq _ vN) _ _  qa tt) => lta.
  move: (Exercise6_33t) =>[_  NN0  /functionsP [fz sz rz] zv].
  move: Exercise6_33q =>[qpa qpb qbc N0c _].
  have vN0: inc   (Vf f v) N0  by  apply: NN0; apply: imf.
  move: (qpa _ vN0) =>[vc iar _]. 
  move: (Exercise6_33j vc) =>[ya yb yc].
  pose p := (Vf (inverse_fun (y (Vf f v))) t).
  move: (ya) =>[_ _ /proj31 bp mor].
  have ps: inc p (rho (Vf f v)).
    by rewrite /p -yb; apply/inverse_Vis => //; rewrite yc.
  have tp: t = Vf (y (Vf f v)) p by rewrite inverse_V //; ue.
  move: (lta); rewrite tp=> -[le ne].
  rewrite yb in iar.
  move/ (Exercise6_33k vc ps iar): le; case/ ole_eqVlt => lpa.
     by  case: ne; rewrite lpa.
  apply/(Imf_P fz); rewrite sz.
  move: (olt_i lpa) => ipa; exists p => //.
  rewrite -  (zv _ (imf _ vN)). 
  by rewrite (proj33 (Exercise6_33r vN0) _ ipa).
have Ra: sub (Imf f) N.
  by move => t /(Imf_P (proj1 finj)) [ u usf ->]; apply: imf; rewrite - sf.
have Rb: cardinal (Imf f) = c.
  by rewrite (cardinal_range finj) sf. 
  have Rc u v: inc u (Imf f)  -> inc v (Imf f) -> u <> v ->
               (Vf X u) \cap (Vf X v)  = E6_33_Q.
  move/(Imf_P ff) =>[i isf ->] /(Imf_P ff) [j jsf ->].
  rewrite sf in isf jsf.
  move: (proj2 (worder_total wor)); rewrite sr => h.
  wlog: i j isf jsf / gle r i j.
  move => H; case: (h i j isf jsf) => le1; first by apply:H.
    by move/nesym => neq; rewrite setI2_C; apply: H.
  move => leij nej.
  have lij: glt r i j by  split => //  bad; case: nej; rewrite bad.
  set_extens t.
    by move/setI2_P => [tf1 tf2]; move: (cp1 i j t lij tf1 tf2).
  move => tq; apply/setI2_P; split.
    by apply: (Exercise6_33u (imf _ isf)).
  by apply: (Exercise6_33u (imf _ jsf)).
done.
Qed.

Lemma  Exercise6_33y: Ex6_33_conc.
Proof.
case:  Exercise6_33x; set T := Imf _; set q := E6_33_Q => ra rb rc.
exists (Vfs X T), q.
move: Exercise6_33d  =>[iX sX _].
move: Exercise6_33q =>[_ _ _ N0c _].
have sNc: sub N c by apply: sub_trans N0c; case: Exercise6_33t.
have sTc: sub T c by apply: (sub_trans ra sNc).
have stX: sub T (source X) by ue.
split.
- move => t. move/(Vf_image_P (proj1 iX) stX) => [u uT ->].
  by apply: Exercise6_33d1; apply: sTc.
- move: (cardinal_image stX iX); rewrite rb=> ->; apply:Exercise6_33b.
- move => i j /(Vf_image_P (proj1 iX) stX) [u uT ->].
  move /(Vf_image_P (proj1 iX) stX) =>[v vT ->] ns.
  apply: rc => //; dneg ww; ue.
Qed.


End Exercise6_33.

End Exercise6.

(** ** The von Neuman ordinals *)
Module VonNeumann. 

(** A [numeration] is a functional graph [f] such that [f(x)] 
is the set of all [f(y)] 
where [y<x] for [r]. A set is [numerable] if well-ordered and there is a 
[numeration]. 
*)


Definition numeration r f:=
  [/\ fgraph f, domain f = substrate r &
  forall x, inc x (domain f) ->  Vg f x = direct_image f (segment r x)].
Definition  numerable r :=
   worder r /\ exists f, numeration r f.

(** Each set has at most one numeration *)
Lemma direct_image_exten f f' a:
  fgraph f -> fgraph f' -> (forall x, inc x a -> Vg f x = Vg f' x) ->
  sub a (domain f) -> sub a (domain f') ->
  direct_image f a = direct_image f' a.
Proof.
move=> fgf fgf' sVVg adf adf'.
set_extens x; move /dirim_P => [u us Jg]; apply /dirim_P; ex_tac.
  move: (pr2_V fgf Jg); aw; move=> ->; rewrite (sVVg _  us). 
  by apply: fdomain_pr1 =>//;  apply: adf'. 
move: (pr2_V fgf' Jg); aw; move=> ->; rewrite -(sVVg _  us). 
by apply: fdomain_pr1 =>//;  apply: adf. 
Qed.

Lemma numeration_unique r f f':
  worder r -> numeration r f -> numeration r f' -> f = f'.
Proof.
move=>  [or wor] [fgf df Vf][fgf' df' Vf'].
set A :=Zo (substrate r)(fun x=> Vg f x <> Vg f' x).
case: (emptyset_dichot A)=> neA.
  apply: (fgraph_exten fgf fgf'); rewrite df => // a xdf.
  by ex_middle nVV; empty_tac1 a; apply: Zo_i.
have sAs: sub A (substrate r) by apply: Zo_S.
move: (wor _ sAs neA)=> [y []]; rewrite iorder_sr// => yA leyA.
move: (sAs _ yA)=> ysr.
have srp: forall z, inc z (segment r y) -> Vg f z = Vg f' z.
  move=> z /segmentP zy; ex_middle nVV. 
  have zA: (inc z A) by  apply: Zo_i=>//; order_tac.
  move: (iorder_gle1 (leyA _ zA)) => yz; order_tac.
have nyA: Vg f y = Vg f' y.  
  rewrite df in Vf; rewrite df' in Vf'. 
  rewrite Vf // Vf' //.
  apply: direct_image_exten =>//.
    rewrite df;  apply: sub_segment.
    rewrite df';  apply: sub_segment.
by move: yA => /Zo_P [_ []]. 
Qed.

(** A numeration of a segment is obtained by restriction *)

Lemma sub_numeration r f x:
  let r' := induced_order r (segment r x) in
  worder r ->  numeration r f -> inc x (substrate r) ->
  numeration r' (restr f (segment r x)).
Proof.
move=> r' wor num xsr.
have sss:= (@sub_segment r x).
have wor':=(induced_wor wor sss).
have [fgf df pf]:= num.
have sr':substrate r' = (segment r x) by rewrite /r' iorder_sr; fprops.
have ssd: sub (segment r x) (domain f) by ue.
have dr:domain (restr f (segment r x)) = substrate r' by aw.
split; aww => a asr.
have sra: (segment r' a = segment r a).
  apply: segment_induced_a =>//; fprops. 
  apply: segment_segment; fprops.
rewrite sra (restr_ev _ asr) pf; last by apply:ssd.
have ssad: sub (segment r a) (domain f) by rewrite df; apply:sub_segment.
have sax: sub (segment r a) (segment r x).
  move=> t; move: asr => /segmentP p1  /segmentP p2. 
  have or: order r by fprops.
  apply /segmentP;order_tac.
apply: direct_image_exten; aww.
by move=> z zs; rewrite restr_ev => //; apply: sax. 
Qed.

(** If all segments are numerable so is the whole set *)

Lemma segments_numerables r:
  let r' := fun x => induced_order r (segment r x) in
  worder r -> (forall x, inc x (substrate r)-> numerable (r' x)) ->
  numerable r.
Proof.
move=> r' wor aln.
set f:= (fun x =>  choose (fun y=> numeration (r' x) y)).
have fp: forall x, inc x (substrate r) -> numeration (r' x) (f x). 
  by move=> x xsr; move: (aln _ xsr)=> [_ c];rewrite /f;apply: choose_pr.  
have or: order r by fprops.
have restrp: forall x y, glt r y x ->
   f y = restr (f x) (substrate (r' y)).
  move=> x y ryx.
  have sss: sub (segment r x) (substrate r) by apply: sub_segment.
  have ssy: sub (segment r y) (substrate r) by apply: sub_segment.
  have p6: worder (r' y) by apply: induced_wor =>//.
  apply: (numeration_unique p6); first by apply:  fp; order_tac.
  have <-: (segment (r' x) y) = substrate (r' y).
    rewrite /r' iorder_sr//; try apply: sub_segment; rewrite segment_induced //.
  have p1: worder (r' x) by rewrite /r'; apply: induced_wor =>//.
  have p2: numeration (r' x) (f x) by apply: fp; order_tac.
  have p3: inc y (substrate (r' x)) by rewrite /r' iorder_sr//; apply /segmentP.
  move: (sub_numeration p1 p2 p3).
  have -> //: induced_order (r' x) (segment (r' x) y) = r' y.
  rewrite /r' segment_induced // iorder_trans //.
  apply: (segment_monotone or (proj1 ryx)).
have gp: forall x y, glt r y x -> range (f y) = Vg (f x) y.
  move=> x y yx.
  have xsr: (inc x (substrate r)) by order_tac.
  have ysr: (inc y (substrate r)) by order_tac.
  move: (fp _ xsr) => [fg df vf].
  move: df; rewrite /r' iorder_sr// => df; last by apply: sub_segment.
  have ysrx: (inc y (segment r x)) by  apply /segmentP.
  rewrite df in vf; rewrite (vf _ ysrx)  (restrp _ _ yx).
  have ->: (segment (r' x) y) = (substrate (r' y)).
    rewrite /r' iorder_sr//; [ by rewrite segment_induced | apply: sub_segment].
  have gr: sgraph (restr (f x) (substrate (r' y))) by fprops.
  have fgr: fgraph (restr (f x) (substrate (r' y))) by fprops.
  have hh: sub (substrate (r' y)) (domain (f x)). 
    rewrite df; rewrite /r' (iorder_sr or (@sub_segment r y)). 
    apply:(segment_monotone or (proj1 yx)).
  set_extens u.
    move /(range_gP fgr); aw; move => [z pa pb]; apply /dirim_P; exists z => //.
    by move: pb;rewrite LgV// => ->; apply:(fdomain_pr1 fg); apply: hh.
  move /dirim_P => [z za zb];apply /(range_gP fgr); exists z;aw; bw => //.
  by move: (pr2_V fg zb); aw.
split =>//; exists (Lg (substrate r) (range \o f)).
red; aw; split;fprops.
move=> x xsr; rewrite LgV//.
move: (fp _ xsr) => [ff df vf].
move: df; rewrite /r' iorder_sr// => df; last by apply: sub_segment.
have gf: sgraph (f x) by fprops.
have p0: sub (segment r x) (substrate r) by apply: sub_segment.
have fgL: fgraph (Lg (substrate r) (range \o f)) by fprops.
set_extens t.
  move=> /(range_gP ff) [z pa pb]; apply /dirim_P; exists z; first ue.
  move: pa; rewrite df => /segmentP h; rewrite pb - (gp _ _ h); apply: Lg_i.
  order_tac.
move /dirim_P => [z xs JL]; move: (p0 _ xs) => zs.
move /segmentP: (xs) => lt1. 
move: (pr2_V fgL JL); aw; rewrite LgV//  => -> /=; rewrite (gp _ _ lt1). 
by apply /(range_gP ff); exists z => //; ue.
Qed. 

(** Any well-ordered is numerable *)

Lemma worder_numerable r:
  worder r ->  numerable r.
Proof.
move=> wor; apply: segments_numerables =>// x xsr.
set r' := fun x => induced_order r (segment r x).
set (A:= Zo (substrate r)(fun z=> ~numerable (r' z))).
case: (p_or_not_p (numerable (induced_order r (segment r x)))) =>// h.
have sA: (sub A (substrate r)) by apply: Zo_S.
have neA: nonempty A  by exists x; apply/Zo_P.
move: (wor)=> [or aux]; move: (aux _ sA neA)=> [y []]; rewrite iorder_sr// => ys yp.
have rec: forall z, glt r z y -> numerable (r' z).
  move=>z zy; case: (p_or_not_p (numerable (r' z))) =>// nnz.
  have zA: (inc z A) by rewrite /A; apply: Zo_i=>//; order_tac.
  move: (iorder_gle1 (yp _ zA)) => yz; order_tac.
move: ys => /Zo_P [ys ny]; case: ny.
have sss: sub (segment r y) (substrate r) by apply: sub_segment.
apply: segments_numerables; first by  apply: induced_wor.
rewrite /r' iorder_sr//; move=> z zy.
have rzy: glt r z y by apply /segmentP.
rewrite segment_induced // iorder_trans //;first by apply: rec.
apply: segment_monotone =>//; order_tac.
Qed.

(** The previous result is obvious by [transfinite_defined] *)

Lemma worder_numerable_bis  r:
  worder r -> numeration r (graph (ordinal_iso r)).
Proof. 
move=> wor.
move: (transfinite_defined_pr target wor) => [suf sf vf].
have ff:= proj1 suf. 
hnf; rewrite (domain_fg ff) sf; split; fprops.
move=> x xsr; move: (vf _ xsr); rewrite /Vf; move=> ->; apply:corresp_t.
Qed.


End VonNeumann. 

(** ---- *)


Module OrderType.

(** ** Bourbaki Exercices Order Types*)

(* lemmas about orderd sets *)
  
Lemma osum_assoc2 a b c:
  order a -> order b -> order c ->
  (order_sum2 a (order_sum2 b c))  \Is (order_sum2 (order_sum2 a b) c).
Proof.
move=> oa ob oc.
have oab: order (order_sum2 a b) by apply: orsum2_or.
have obc: order (order_sum2 b c) by apply: orsum2_or.
set E:= substrate (order_sum2 a (order_sum2 b c)).
set F:= substrate (order_sum2 (order_sum2 a b) c).
set A:= substrate a; set B := substrate b; set C := substrate c.
have Ev: E = canonical_du2 A (canonical_du2 B C).
  by rewrite /E ! orsum2_sr.
have Fv: F = canonical_du2 (canonical_du2 A B) C.
  by rewrite /F ! orsum2_sr.
move: C1_ne_C0 => nT.
move: C0_ne_C1 => nT1.
set f := fun z => Yo (Q z = C0) (J (J (P z) C0) C0)
          (Yo (Q (P z) = C0) (J (J (P (P z)) C1) C0) (J  (P (P z)) C1)).
have p1: forall x, inc x E -> inc (f x) F.
  move => x; rewrite Ev Fv; move /candu2P => [px]; case.
   by move=> [PA Qa]; rewrite /f; Ytac0; apply: candu2_pra; apply: candu2_pra.
  move => [] /candu2P [pPx alt] Qb.
  have nQa: Q x <> C0 by rewrite Qb. 
  rewrite /f; Ytac0.
  case: alt;move => [Ppx Qpx]. 
   by Ytac0; apply: candu2_pra; apply: candu2_prb.
   rewrite (Y_false); [ apply: candu2_prb => // |  rewrite Qpx; fprops].
have p2: forall y, inc y F -> exists2 x, inc x E & y  = f x.
  move => y; rewrite Ev Fv;  move /candu2P => [px]; case.
    move=> []  /candu2P [pPy aux] Qpy; case: aux.
      move=> [PPa QP]; exists (J (P (P y)) C0).
        by apply: candu2_pra.
      rewrite /f pr2_pair;  Ytac0; aw.
      apply: pair_exten =>//; fprops; aw; try ue.
    move=> [PPy QPy]; exists (J (J (P (P y)) C0) C1).
      by apply: candu2_prb;  apply: candu2_pra.
    rewrite /f !(pr1_pair, pr2_pair); Ytac0; Ytac0. 
    apply: pair_exten =>//; fprops; aw; try ue.
  move=> [Py Qy]; exists (J (J (P y) C1) C1).
     by apply: candu2_prb;  apply: candu2_prb.
   rewrite /f !(pr2_pair, pr1_pair); Ytac0; Ytac0.
   apply: pair_exten =>//;aww.
have p3: forall x y, inc x E -> inc y E -> f x = f y -> x = y.
  move => x y; rewrite Ev;  move /candu2P => [px hx] /candu2P  [py hy].
  rewrite /f;case: hx.
    move => [PxA Qxa]; Ytac0.
    case: hy.
      move => [PyA Qya]; Ytac0 => sf; move:(pr1_def sf).
      by rewrite - {1} Qxa - Qya px py.
    move=> [_ ] Qy; rewrite Qy; Ytac0; Ytac h1.
      move => h2;case: nT1; exact: (pr2_def(pr1_def h2)). 
       move => h2;case: nT1; exact: (pr2_def h2).
   move => [] /candu2P [pPx auxx] Qx; rewrite Qx; Ytac0.
   case: hy.
     move=> [_ Qy]; Ytac0; Ytac h.
       move => h2;case: nT; exact: (pr2_def(pr1_def h2)). 
     move => h2;case: nT; exact: (pr2_def h2).
  move=> [] /candu2P [pPy auxy] Qy; rewrite Qy; Ytac0.
  case: auxx; move=> [PPx Qpx].
    Ytac0.
      case: auxy; move=> [PPy Qpy].
         Ytac0 => sf; move: (pr1_def (pr1_def sf)) => sf1.
         apply: pair_exten =>//; try ue.
         apply: pair_exten =>//; try ue.
    rewrite Qpy;Ytac0=> sf; case: nT1; exact: (pr2_def sf).
  case: auxy; move=> [_ Qpy]. 
     rewrite Qpx Qpy; Ytac0; Ytac0 => sf; case: nT; exact: (pr2_def sf).
  rewrite Qpx Qpy; Ytac0; Ytac0.
  move=> sf; move: (pr1_def sf) => sf1.
  apply: pair_exten =>//; try ue.
  apply: pair_exten =>//; try ue.
exists (Lf f E F); split.
    by apply: orsum2_or.
  by apply: orsum2_or.
rewrite ! orsum2_sr //; saw; first  by apply: lf_bijective.
red; rewrite lf_source;move=> x y xE yE; rewrite !LfV//.
move: (xE); rewrite Ev ; move=> /candu2P [px hx].
move: (yE); rewrite Ev ; move=> /candu2P [py hy].
split.
  move /orsum2_gleP => [_ _ h]; apply /orsum2_gleP; rewrite  orsum2_sr //.
  split => //; first by  move: (p1 _ xE); rewrite Fv.
     by  move: (p1 _ yE); rewrite Fv.
  case: h.
      move=> [Qx Qy le]; constructor 1; rewrite /f  (Y_true Qx) (Y_true Qy).
      rewrite ! pr1_pair  ! pr2_pair; split => //.
      apply /orsum2_gleP;split => //; last by aw; constructor 1. 
         apply candu2_pra; order_tac.
      apply candu2_pra; order_tac.
    move => [hxa hxb]  /orsum2_gleP  [_ _].
    case: hx; move => [pxa qxa]; first by case: hxa.
    case: hy; move => [pya qya]; first by case: hxb.
    case; last first.
        by move => [sa sb]; constructor 3; rewrite /f; do 4 Ytac0; aw.
      by move => [sa sb sc];constructor 2; rewrite /f; do 4 Ytac0; aw.
    move => [sa sb sc]; constructor 1; rewrite /f; do 4 Ytac0; aw.
    case /candu2P: pxa => _ [] [ta tb]; last by case: nT; rewrite - sa - tb.
    case /candu2P: pya => _ [] [ta' tb']; last by case: nT; rewrite - sb - tb'.
    split => //; apply/orsum2_gleP; split => //.
        by apply: candu2_prb.
      by apply: candu2_prb.
    aw; by constructor 2.
  move=> [Qxa Qyb].
  case: hy; move => [pya qya]; first by case: Qyb.
  case: hx; move => [pxa qxa]; last by case: nT; ue. 
  move /candu2P: pya =>[_]; case; move => [sa sb].
     constructor 1; rewrite /f; Ytac0; Ytac0; Ytac0; aw; split => //.
     apply /orsum2_gleP; split => //.
     - by apply candu2_pra.
     - by apply candu2_prb.
     - by constructor 3; aw. 
  by constructor 3;  rewrite /f sb; Ytac0; Ytac0; aw; Ytac0;aw.
move /orsum2_gleP => [_ _ h]; apply /orsum2_gleP.
rewrite  orsum2_sr // -/A -/B -/C - Ev;split => //.
case: hx; move => [Px Qx].
  have fx: f x =  (J (J (P x) C0) C0) by rewrite /f Y_true.
  case: hy; move => [Py Qy].
    have fy: f y =  (J (J (P y) C0) C0) by rewrite /f Y_true.
    constructor 1; split => //.
    move: h; rewrite fx fy ! pr1_pair ! pr2_pair; case.
    - move=> [_ _] /orsum2_gleP [_ _]; case; aw; first by move => [_ _ s].
      + by  move=> [_ bad _].
      + by  move=> [_ bad].
    - by move=> [_ bad _]. 
    - by move=> [_ bad].
  constructor 3; rewrite Qx Qy; split; exact.
case: hy; move => [Py Qy].
  case: (nT); case: h.
    move=> [Qfx Qfy] /orsum2_gleP [Pfx Pfy].
      have -> : Q (P (f y)) = C0 by rewrite /f; Ytac0; aw.
      case; [ | move => [_ pa _] | move => [_ pa]]; try by case: pa.
      by move=> [h1 _]; move: h1 Qfx; rewrite /f  Qx (Y_false) //;Ytac ww; aw.
    by move => [_ pa _]; move: pa; rewrite /f; Ytac0; aw.
  by move => [ _ ]; rewrite /f; Ytac0; aw.
rewrite Qx Qy; constructor 2; split => //.
apply /orsum2_gleP; split => //.
move: Px Py => /candu2P [pPx hpx] /candu2P [pPy hpy].
case: hpx; move => [pa pb].
  case: hpy; move => [pc pd]; last by constructor 3; rewrite pd;split => //.
  constructor 1; split => //; move: h; rewrite /f Qx Qy; do 4 Ytac0. 
  case; [move => [_ _ ba] | move => [ba _] | move=> [_ ba]]; move: ba; aw => //.
  move /orsum2_gleP => [_ _];rewrite !pr1_pair !pr2_pair.
  by case; [ move => [sa _] |  move => [_ _] |  move => [sa _]].
constructor 2; rewrite pb; move: h; rewrite /f Qx Qy pb.
Ytac0; Ytac0; Ytac0; case; first by move => [sa _]; move: sa; aw.
  Ytac ww; first by move => [_ qa _]; move: qa; aw.
  by move => [_ _]; aw. 
by move => [sa _]; move: sa; aw.
Qed.


Lemma oprod_assoc2  a b c:
  order a -> order b -> order c ->
  (order_prod2 a (order_prod2 b c))
  \Is (order_prod2 (order_prod2 a b) c).
Proof.
move=> oa ob oc.
have oab: order (order_prod2 a b) by apply: orprod2_or.
have obc: order (order_prod2 b c) by apply: orprod2_or.
set E:= substrate (order_prod2 a (order_prod2 b c)).
set F:= substrate (order_prod2 (order_prod2 a b) c).
set A:= substrate a; set B := substrate b; set C := substrate c.
have Ev: E = product2 (product2 C B) A.
  by rewrite /E ! orprod2_sr.
have Fv: F = product2 C (product2 B A).
  by rewrite /F ! orprod2_sr.
have CB_pr: forall z, inc z (product2 C B) <->
   [/\ fgraph z, domain z = C2, inc (Vg z C0) C & inc (Vg z C1) B].
   by move=> z; apply /setX2_P.
have BA_pr: forall z, inc z (product2 B A) <->
   [/\ fgraph z, domain z = C2, inc (Vg z C0) B & inc (Vg z C1) A].
   by move=> z;  apply /setX2_P.
set f :=  fun z => variantLc (Vg (Vg z C0) C0) 
     (variantLc (Vg  (Vg z C0) C1) (Vg z C1)).
have p01: forall x, inc x E -> inc (f x) F.
  move=> x; rewrite Ev Fv; move /setX2_P => [p1 p2 /setX2_P [p4 p5 p6 p7] p3].
  rewrite /f; aw; apply /setX2_P; split => //; aww.
  by apply /setX2_P; split;fprops; aw.
have p02: forall x y, inc x E -> inc y E -> f x = f y -> x = y.
  move=> x y; rewrite Ev; move /setX2_P => [p1 p2 /setX2_P [p4 p5 p6 p7] p3].
  rewrite /f;  move /setX2_P => [p1' p2' /setX2_P [p4' p5' p6' p7'] p3'] sf.
  move: (f_equal (Vg ^~ C0) sf) (f_equal (Vg ^~C1) sf); aw => sf1 sf2.
  move: (f_equal (Vg ^~C0) sf2) (f_equal (Vg ^~C1) sf2); aw => sf3 sf4.
  apply: fgraph_exten =>//; try ue.
  rewrite p2; move=> z zdx;try_lvariant zdx; trivial.
  apply: fgraph_exten =>//; try ue.
  by rewrite p5; move=> zz zdx; try_lvariant zdx.
have p03:  forall y, inc y F -> exists2 x, inc x E & y = f x.
  move=> y; rewrite Fv; move /setX2_P => [p1 p2 p3 /setX2_P [p4 p5 p6 p7]].
  exists (variantLc (variantLc  (Vg y C0)  (Vg (Vg y C1) C0))
       (Vg (Vg y C1) C1)).
     rewrite Ev;apply /setX2_P; split;aww.
     by apply /setX2_P; split;fprops; aw.
  rewrite /f; symmetry;apply: fgraph_exten => //; aww. 
  move=> x xtp;  try_lvariant xtp; trivial.
  apply: fgraph_exten => //; aw ; [fprops | by symmetry | ].
  by move=> z xtp; try_lvariant xtp.
exists (Lf f E F); split => //; fprops;aw.
      by apply: orprod2_or.
    by apply: orprod2_or.
  saw;apply: lf_bijective => //.
red; aw; move=> x y xE yE; rewrite ! LfV //.
move: (xE); rewrite Ev;move /setX2_P => [p1 p2 /setX2_P [p4 p5 p6 p7] p3].
move: (yE);rewrite Ev;move /setX2_P => [p1' p2' /setX2_P [p4' p5' p6' p7'] p3'].
split. 
  move: (p01 _ xE)(p01 _ yE) => xF yF.
  move: xF; rewrite Fv; case /setX2_P=>[q1 q2 q3 /setX2_P [q4 q5 q6 q7]].
  move: yF; rewrite Fv; case /setX2_P=>[r1 r2 r3 /setX2_P [r4 r5 r6 r7]].
  have x1: inc (Vg (f x) C1) (product2 B A) by rewrite  BA_pr.
  have y1: inc (Vg (f y) C1) (product2 B A) by rewrite  BA_pr.
  set hi1:= inc (Vg (f x) C1) (product2 B A).
  set hi2:= inc (Vg (f y) C1) (product2 B A).
  move => tmp; apply /(orprod2_gleP oab oc).
  rewrite orprod2_sr // -/A -/B -/C -Fv;split => //; try apply: p01 => //.
  move: tmp => /(orprod2_gleP oa obc) [_ _]; case.
     move => [pa pb];left; split; first by rewrite /f;aw;ue.
     apply /(orprod2_gleP oa ob);split => //;left. 
     by rewrite /f; aw;split => //; rewrite pa.
  move => [] /(orprod2_gleP ob oc) [_ _ aux'] nse. 
  case: aux'; last by move=> aux2; right; rewrite /f; aw.
  move=> [Vaa Vba]; left; split; first by rewrite /f; aw.
  apply /(orprod2_gleP oa ob);split => //; right. 
  rewrite /f ! LgV//; aww; split => //; dneg aux3.
  apply: fgraph_exten =>//; try ue.   
  by rewrite p5; move=> z zd; try_lvariant zd.
move /(orprod2_gleP oab oc) => [_ _ tmp].
apply/(orprod2_gleP oa obc); rewrite orprod2_sr // -/A -/B -/C -Ev;split => //. 
have x1: inc (Vg x C0) (product2 C B) by rewrite  CB_pr. 
have y1: inc (Vg y C0) (product2 C B) by rewrite  CB_pr.
case: tmp; last first.
  rewrite /f; aw; move=> [h1 h2]; right; split.
  apply /(orprod2_gleP ob oc);split => //; by right.
  by  dneg eql; rewrite eql.
rewrite /f; aw; move => [xaa] /(orprod2_gleP oa ob) [fxb fxa]; aw.
case.
    move=> [sVab le]; left; split =>//.
    apply: fgraph_exten => //; first by ue.
    by rewrite p5; move=> z zd; try_lvariant zd.
move=> [lt2 neq]; right;split; last by  dneg aux; rewrite aux.
by apply /(orprod2_gleP ob oc);split => //; left.
Qed.

Lemma osum_distributive a b c:
  order a -> order b -> order c ->
  (order_prod2 c (order_sum2 a b))
  \Is (order_sum2 (order_prod2 c a) (order_prod2 c b)).
Proof.
move=> oa ob oc.
move: (orsum2_or oa ob) => oab.
move: (orprod2_or oc oa) => oca.
move: (orprod2_or oc ob) => ocb.
move: (orprod2_or oc oab) => ocab.
move:(orsum2_or oca ocb) => ocacb. 
set (f := fun z => J (variantLc (P (Vg z C0)) (Vg z C1)) (Q (Vg z C0))).
set A := substrate a; set B := substrate b; set C := substrate c.
set E:= substrate (order_prod2 c (order_sum2 a b)).
set F:= substrate(order_sum2 (order_prod2 c a)(order_prod2 c b)).
have Ep: E = product2 (canonical_du2 A B) C.
   rewrite /E orprod2_sr // orsum2_sr //.
have Fp: F = canonical_du2 (product2 A C)(product2 B C).
  rewrite /F orsum2_sr // !orprod2_sr //.
have Ev: forall x, inc x E <-> [/\ fgraph x, domain x = C2,
    pairp (Vg x C0),
     ((inc (P (Vg x C0)) A /\ Q (Vg x C0) = C0) \/
      (inc (P (Vg x C0)) B /\ Q (Vg x C0) = C1))
     &inc (Vg x C1) C].
  move=> x; rewrite Ep; split.
     move /setX2_P => [pa pb pc pd]; move/candu2P: pc => [pe] [] [pf pg];
     split => //; [left | right ]; split => //.
  by move => [pa pb pc pd pe]; apply /setX2_P;split => //; apply/candu2P. 
have Fv: forall x, inc x F <-> [/\ pairp x, fgraph (P x),
    domain (P x) = C2, inc (Vg (P x) C1) C &
    ((inc (Vg (P x) C0) A /\ Q x = C0) \/
    (inc (Vg (P x) C0) B /\ Q x = C1))].
   move=> x; rewrite Fp; split.
     move /candu2P => [pa []] [] /setX2_P [pb pc pd pe] pf; split;fprops.
   move => [pa pb pc pd];case; move =>[pe pf]; 
    apply /candu2P;split => //; [left | right];
    split => //;apply /setX2_P; split; fprops.
have p1: forall x, inc x E -> inc (f x) F.
  move=> x /Ev [pa pb pc pd pe]; rewrite /f; apply/Fv; split; aww.
have p2: forall x y, inc x E -> inc y E -> f x = f y -> x = y.
  move=> x y /Ev [fgx dx px hx qx] /Ev [fgy dy py hy qy].
  rewrite /f => sf; move: (pr1_def sf)(pr2_def sf) => r1 r2.
  move: (f_equal (Vg ^~C0) r1)(f_equal (Vg ^~C1) r1); aw; move => r3 r4.
  apply: fgraph_exten =>//; [ ue | rewrite dx; move=> z zd; try_lvariant zd].
    by apply: pair_exten.
  done.
have p3: forall y, inc y F -> exists2 x, inc x E &  y = f x.
  move=> y /Fv [py fPy dPy Vby Vay].
  exists (variantLc (J (Vg (P y) C0) (Q y)) (Vg (P y) C1)). 
    apply /Ev; aw; split; fprops.
  rewrite /f; aw; apply: pair_exten => //; [fprops | aw | by  aw ].
  apply: fgraph_exten; [  exact| fprops  |  by aw |  aw].
  by rewrite dPy; move=> x xtp; try_lvariant xtp; aw.
  exists (Lf f E F); saw; first by saw;apply: lf_bijective.
red; aw;move=> x y xE yE; rewrite LfV // LfV //.
have r1: Q (f x) = Q (Vg x C0) by rewrite /f pr2_pair.
have r2: Q (f y) = Q (Vg y C0) by rewrite /f pr2_pair.
have r3: Vg (P (f x)) C0 = P (Vg x C0) by  rewrite /f; aw.
have r4: Vg (P (f y)) C0 = P (Vg y C0) by  rewrite /f; aw.
have r5: Vg (P (f x)) C1  = Vg x C1 by rewrite /f; aw.
have r6: Vg (P (f y)) C1  = Vg y C1 by rewrite /f; aw.
have pa: pairp (Vg x C0) by move /Ev: xE => [_  _  px _].
have pb: pairp (Vg y C0) by move /Ev:yE => [_ _  px _].
move: (xE) => /Ev  [fgx dx px hx qx].
move: (yE) => /Ev  [fgy dy py hy qy].
move: C0_ne_C1 => nab.
split.
  move /(orprod2_gleP oc oab) => [_ _ h]; apply /(orsum2_gleP).
  split; first by  move: (p1 _ xE); rewrite /F orsum2_sr.
     by  move: (p1 _ yE); rewrite /F orsum2_sr.
  rewrite r1 r2; case: h.
    move=> [q1 q2]; rewrite - q1.
    case: (equal_or_not (Q (Vg x C0)) C0)=> q3.
      case: hx; move=> [q4 q5]; last by case: nab ; rewrite - q3 - q5.
      constructor 1; rewrite  q3; split => //.
      apply /(orprod2_gleP oc oa).
      split; first  by apply/setX2_P; rewrite /f pr1_pair; aw;split;fprops.
         by apply/setX2_P; rewrite /f pr1_pair; aw;split;fprops; ue.
      left; rewrite r3 r4 r5 r6 q1; split =>//.
    constructor 2; split => //.
    case: hx; move=> [q4 q5]; first by case: q3.
    apply /(orprod2_gleP oc ob).
    split; first by apply/setX2_P; rewrite /f pr1_pair; aw;split;fprops.
      by apply/setX2_P; rewrite /f pr1_pair; aw;split;fprops; ue.
    left; rewrite r3 r4 r5 r6 - q1; split =>//.
  move => [] /(orsum2_gleP) [_ _ h1] h2; case: h1.
      move=> [q1 q2 q3]; constructor 1.
      split; [exact | exact | ].
      case: hx; move=> [q4 q5]; last by case: nab; rewrite - q1 - q5.
      case: hy; move=> [q4' q5']; last  by case: nab; rewrite - q2 - q5'.
      apply /(orprod2_gleP oc oa).
      split; first by apply/setX2_P; rewrite /f pr1_pair; aw; split;fprops.
         by apply/setX2_P; rewrite /f pr1_pair; aw; split;fprops.
      right; rewrite r3 r4;split => //;dneg aux. 
      apply: pair_exten => //; ue.
    move => [q1 q2 q3]; constructor 2.
    case: hx; move=> [q4 q5]; first by case: q1.
    case: hy; move=> [q4' q5'];  first by case: q2.
    split; [exact | exact | ].
    apply /(orprod2_gleP oc ob).
    split; first by  apply/setX2_P; rewrite /f pr1_pair; aw;split;fprops.
      by  apply/setX2_P; rewrite /f pr1_pair; aw;split;fprops.
    right; rewrite r3 r4; split => // sP; case: h2.
    by apply: pair_exten => //; rewrite q5 q5'.
  move=> res; constructor 3; exact.
move/(orsum2_gleP) => [_ _ h]; apply /(orprod2_gleP oc oab).
split; first by move: xE; rewrite /E orprod2_sr //.
  by move: yE; rewrite /E orprod2_sr //.
have pc: inc (Vg x C0) (canonical_du2 (substrate a) (substrate b)).
  by move: xE => /Ev [_ _ px' etc _]; apply/candu2P.
have pd: inc (Vg y C0) (canonical_du2 (substrate a) (substrate b)).
  by move: yE => /Ev [_  _ px'  etc _]; apply/candu2P.
case: h.
    move=> [q1 q2] /(orprod2_gleP oc oa) [q3 q4].
    rewrite r3 r4 r5 r6; case; move =>[q5 q6]; [left | right ].
      by split =>//; apply: pair_exten =>//; rewrite -r1 -r2 q1 q2.
    split =>//; last by dneg neq; rewrite neq.
    by apply /orsum2_gleP;split => //; constructor 1;rewrite -r1 -r2 q1 q2.
  move=> [q1 q2] /(orprod2_gleP oc ob) [q3 q4].
  case: hx; rewrite -r1; move => [_ sb]; first by case: q1.
  case: hy; rewrite -r2; move => [_ sb']; first by case: q2.
  rewrite r3 r4 r5 r6; case; move =>[q5 q6]; [left | right ].
    by split =>//; apply: pair_exten =>//; rewrite -r1 -r2 sb sb'.
  split =>//; last by dneg neq; rewrite neq.
  apply /orsum2_gleP;split => //; constructor 2; rewrite - r1 -r2;split => //.
move=> [q5 q6]; right; split.
  apply /orsum2_gleP;split => //; constructor 3; rewrite - r1 -r2;split => //.
by dneg neq; rewrite r2 -neq -r1.
Qed.

Lemma osum_increasing1 r f g:
  orsum_ax r f -> orsum_ax r g ->
  (forall x, inc x (domain f) -> (Vg f x) <=O (Vg g x)) ->
  (order_sum r f) <=O (order_sum r g).
Proof.
move => oa oa1 ale.
have o1: order (order_sum r f)  by fprops.
have o2: order (order_sum r g)  by fprops.
split => //; apply: (proj33 (order_le_alt o1 o2 _)).
set si:= fun j => choose (fun x =>  order_morphism x  (Vg f j) (Vg g j)).
have sip: forall j, inc j (domain f) -> 
       order_morphism (si j) (Vg f j) (Vg g j).
  move=> j jdf; move:(ale _ jdf) => [p1 p2 [f0 [x [ fx1 fx2]]]]. 
  move: (isomorphism_to_morphism p1 p2 fx1 fx2) => [res _].
  rewrite /si; apply choose_pr. 
  by exists (Lf (fun z => Vf f0 z) (substrate (Vg f j)) (substrate (Vg g j))).
have dfdg: domain f = domain g by move: oa oa1 => [_ s1 _] [_ s2 _]; ue.
set E := (substrate (order_sum r g)).
set F := (disjointU_fam (fam_of_substrates f)).
have p1: partition_w_fam F (substrate (order_sum r f)).
  rewrite orsum_sr //  /F /sum_of_substrates /disjointU.
  apply: partition_disjointU; rewrite /fam_of_substrates; fprops.
have p3: (domain F = domain f).
  by  rewrite /F/disjointU_fam /fam_of_substrates; aw.
set di:= fun i => ((substrate (Vg f i)) *s1 i).
set sj:= fun i => Lf (fun z => J (Vf (si i) (P z)) i) (di i) E.
have p0: forall i, inc i (domain f) ->
   lf_axiom (fun z => J (Vf (si i)  (P z)) i)  (di i) E.
  move=> i idf z zV.
  move: (sip _ idf) => [_ _ [ff sf tf] _].
  have aux: inc  (Vf (si i) (P z) ) (substrate (Vg g i)).
    Wtac;move: zV => /indexed_P [_ Ps _]; ue.
  rewrite /E orsum_sr //; apply: disjoint_union_pi1 => //; ue.
have FP: forall i, inc i (domain f) -> Vg F i = di i.
  move=> i idf; rewrite /F /disjointU_fam/fam_of_substrates Lgd  !LgV//.
have p2: forall i, inc i (domain F) -> 
   function_prop (sj i) (Vg F i) E.
  rewrite p3;move=> i idf; rewrite /sj FP => //; aw.
  by saw;apply: lf_function; apply: p0.
move: (extension_partition1 p1 p2).
  set G := common_ext _ _ _; move=> [[fG sG tG] alg].
rewrite p3 in alg.
have aux: forall x, inc x (source G) -> 
  [/\ inc (Q x) (domain f), inc x (di (Q x)), pairp x,
   inc (P x)(substrate (Vg f (Q x))) & Vf G x = J (Vf(si (Q x)) (P x)) (Q x)].
  rewrite sG orsum_sr //; move => x xs; move: (du_index_pr1 xs)=>  [Qxd Pxd px].
  have xdi: inc x (di (Q x)) by apply /indexed_P;split => //.
  split => //.
  move: (alg _ Qxd); rewrite /agrees_on; move=> [q1 q2 q3].
  move: (xdi); rewrite -FP // => q4. 
  move: (q3 _ q4); rewrite /sj; rewrite LfV; aw;trivial;apply: p0 => //.
exists G; split => //.
move=> x y xs ys.
move: (aux _ xs) (aux _ ys) => [Qx xdi px Px Wx][Qy ydi py Py Wy].
have qa: (sum_of_substrates f = source G) by rewrite sG orsum_sr.
have qb: (sum_of_substrates g = target  G) by rewrite tG /E orsum_sr //.
split; move /orsum_gleP =>[q1 q2 q3]; apply /orsum_gleP. 
  rewrite qb;split=> //; try Wtac; rewrite Wx Wy;red;aw; case: q3; first by left.
  move=> [Qxx le1]; right; split => //.
  rewrite -Qxx; move: (sip _ Qx) => [_ _ [_ sf tf] orf].
  rewrite - orf //; rewrite sf //; ue.
move: q3; rewrite /order_sum_r  Wx Wy !pr2_pair !pr1_pair.
move => q3; rewrite qa;split => //; case: q3; first by left.
move=> [Qxx]; rewrite - {1} Qxx => le1; right; split => //.
move: (sip _ Qx) => [_ _ [_ sf tf] orf].
apply /orf; rewrite ? sf //; ue.
Qed.

Lemma osum_increasing2 r f g: worder r ->
  substrate r = domain f -> substrate r = domain g ->
  (forall x, inc x (domain f) -> (Vg f x) <=o (Vg g x)) ->
  (osum r f) <=o (osum r g).
Proof.
move=> wor  sf sg alo.
have ha: worder_on r (domain g) by [].
have hb: worder_on r (domain f) by [].
apply /ordinal_le_P0; apply /order_le_compatible1.
    apply: orsum_wor => //; aw; trivial.
    hnf; aw;move=> i idf; rewrite ! LgV//; fprops; move: (alo _ idf) => [aa bb _]; fprops.
  apply: orsum_wor => //;aw; trivial.
  hnf; aw;rewrite - sg sf; move=> i idf; rewrite LgV//.
    move: (alo _ idf) => [aa bb _]; fprops.
  by rewrite - sg sf.
apply  osum_increasing1.
- split => //;aww; hnf; aw.
  move=> i idf; rewrite LgV//; move: (alo _ idf) =>[aa bb _]; fprops.
- rewrite /Lgcomp - sg sf;split;fprops;hnf; aw; trivial.
  move=> i idf; rewrite LgV//; move: (alo _ idf) =>[aa bb _]; fprops.
- aw => x xdf; move: (alo _ xdf) =>[aa bb le].
  have xdg: inc x (domain g) by rewrite - sg sf.
  rewrite !LgV //; apply/order_le_compatible1; fprops.
  by rewrite (ordinal_o_o aa)  (ordinal_o_o bb) ; apply/ordinal_le_P0.
Qed.


Lemma osum_increasing3 r f j:
  orsum_ax r f -> 
  sub j (domain f) -> 
  (order_sum (induced_order r j) (restr f j)) <=O (order_sum r f).
Proof.
move=> oa jd.
move:  (proj1 (proj1 set0_wor)) => eo.
move: (oa) => [or sr alo].
set (g:= Lg (domain f)  (fun z => Yo (inc z j) (Vg f z) emptyset)).
have dfdg: domain f = domain g by rewrite /g; aw.
have oa': orsum_ax r g.
  split => //; first by ue.
  hnf; rewrite - dfdg /g;move=> i idg; rewrite LgV//; Ytac ij;first by apply: alo.
  done.
have sjd': sub j (domain g) by ue.
have cz: (forall i, inc i ((domain g) -s j) -> Vg g i = \0o).
  by move=> i /setC_P; rewrite -dfdg /g; move=> [idf nij]; rewrite LgV//; Ytac0.
move: (osum_unit1 oa' sjd' cz).
have ->: (restr f j = restr g j).
  apply: Lg_exten => s sj;rewrite LgV//; rewrite /g; [ by Ytac0 | by apply:jd ].
move=> oi1.
have oi2: (order_sum r f) \Is (order_sum r f).
  by apply: orderIR; apply: orsum_or.
apply /(order_le_compatible oi1 oi2).
apply: osum_increasing1 => //.
rewrite -dfdg; move=> x xdg;  rewrite /g LgV//.
Ytac xj; first by  apply: order_leR=>//; apply: alo. 
split; fprops;exists (identity emptyset); exists emptyset.
have auw: sub emptyset (substrate (Vg f x)) by fprops.
split => //; split;fprops.
- apply: (proj1 (iorder_osr _ auw)); fprops.
- rewrite (iorder_sr (alo _ xdg)) // (proj2 set0_wor); apply:  identity_bp.  
- by move=> u v;  rewrite identity_s => /in_set0.
Qed.


Lemma osum_increasing4 r f j: 
   worder_on r (domain f) -> sub j (domain f) -> ordinal_fam f ->
  (osum (induced_order r j) (restr f j)) <=o (osum r f).
Proof.
move => [wor sr] sjf alo.
have sjr: sub j (substrate r) by ue.
have or: order r by move: wor => [or _].
have dr: (domain (restr f j)) = j by aw.
have ha:worder_on r (domain f) by [].
rewrite /osum; apply /ordinal_le_P0; apply /order_le_compatible1.
   apply: orsum_wor.
     by aw;split;[ apply: induced_wor => // ue | rewrite iorder_sr //  dr].
      hnf; rewrite /Lgcomp dr; aw; move=> i ij; rewrite ! LgV //; fprops.
  apply: orsum_wor => //; hnf; aw; trivial;move=> i idf; rewrite !LgV//; fprops.
set g:= (Lgcomp f ordinal_o).
have ->: (Lgcomp (restr f j) ordinal_o)  = restr g j.
  rewrite /Lgcomp; aw;apply: Lg_exten. 
  by rewrite /g;red; aw;move => x xj; rewrite !LgV//; apply: sjf.
apply: osum_increasing3 => //. 
rewrite /g;red; aw;split => //; hnf;aw; move=> i idf; rewrite LgV//; fprops. 
by rewrite /g; aw.
Qed.

Lemma oprod_increasing1 r f g:
  orprod_ax r f -> orprod_ax r g ->
  (forall x, inc x (domain f) -> (Vg f x) <=O (Vg g x)) ->
  (order_prod r f) <=O (order_prod r g).
Proof.
move => oa oa1 ale.
have o1: order (order_prod r f)  by fprops.
have o2: order (order_prod r g)  by fprops.
split => //; apply: (proj33 (order_le_alt o1 o2 _)).
set si:= fun j => choose (fun x =>  order_morphism x  (Vg f j) (Vg g j)).
have sip: forall j, inc j (domain f) -> 
       order_morphism (si j) (Vg f j) (Vg g j).
  move=> j jdf; move:(ale _ jdf) => [p1 p2 [f0 [x [fx1 fx2]]]]. 
  move: (isomorphism_to_morphism p1 p2 fx1 fx2) => [res _].
  rewrite /si; apply choose_pr.
  by exists (Lf (fun z => Vf f0 z) (substrate (Vg f j)) (substrate (Vg g j))).
have dfdg: domain f = domain g by move: oa oa1 => [_ s1 _] [_ s2 _]; ue.
set E:= substrate (order_prod r f).
set F := substrate(order_prod r g).
have Ep: E = (prod_of_substrates f) by apply: orprod_sr => //.
have Fp: F = (prod_of_substrates g) by apply: orprod_sr => //.
set h:= fun z => Lg (domain f) (fun i => Vf (si i) (Vg z i)).
have ta: lf_axiom h E F.
  rewrite Ep Fp ; move => t /prod_of_substratesP [fgt dt als].
  apply /prod_of_substratesP.
  rewrite - dfdg /h; aw;split;fprops;move=> i idf; rewrite LgV//.
  move: (sip _ idf) => [_ _ [fsi ssi tsi] _]. 
  by Wtac; rewrite ssi;apply: als.
have hi: forall u v, inc u E -> inc v E -> h u = h v -> u = v.
  rewrite Ep; move=> u v / prod_of_substratesP [fgu du alu]
     /prod_of_substratesP [fgv dv alv] sh.
  apply: fgraph_exten =>//; first by ue.
  rewrite du; move=> x xdf; move: (f_equal (Vg ^~x) sh); rewrite /h !LgV// => sW.
  move: (order_morphism_fi  (sip _ xdf)) => [_ insi].
  move: (sip _ xdf) => [_ _ [fsi ssi tsi] _].
  apply: insi =>//; rewrite  ssi; [ apply: alu => // |apply: alv => //].
exists (Lf h E F); red; aw; split => //.
  saw;by apply: lf_function.  
red; aw; move=> x y xE yE; rewrite /h !LfV//.
have srdf: substrate r = domain f by  move: oa => [_ sr _].
move: (xE); rewrite Ep; move /prod_of_substratesP => [fgx dx alx].
move: (yE); rewrite Ep; move /prod_of_substratesP => [fgy dy aly].
split. 
  move /(orprod_gleP oa) => [_ _ aux]; apply /(orprod_gleP oa1).
  rewrite -Fp;split; [by apply: ta | by apply: ta |].
  case: aux; first by move=>->; left.
  move=> [j [jsr jlt jle]]; right; ex_tac.
    rewrite srdf in jsr;move: jlt; rewrite ! LgV//.
    move: (order_morphism_fi  (sip _ jsr)) => [_ insi].
    move:  (sip _ jsr) => [_ _ [fsi ssi tsi] jsrp].
    have vsx: inc (Vg x j) (source (si j)) by rewrite  ssi; apply: alx => //.
    have vsy: inc (Vg y j) (source (si j)) by rewrite  ssi; apply: aly => //.
    rewrite /glt -jsrp //;move=> [p1 p2]; split =>//; dneg sV; apply: insi =>//.
  move=> i ij.
  have idf: inc i (domain f) by rewrite - srdf; order_tac.
  by move: (jle _ ij); rewrite !LgV//; move=> ->.
move /(orprod_gleP oa1) => [h1 h2 aux]; apply /(orprod_gleP oa).
rewrite -Ep; split=> //; case: aux.
  move => sh; left; apply: hi =>//.
move=> [j [jsr jlt jle]]; right; ex_tac.
rewrite srdf in jsr; move: jlt; rewrite !LgV//.
move:  (sip _ jsr) => [_ _ [fsi ssi tsi] jsrp].
rewrite /glt jsrp; first by move=> [p1 p2]; split =>//; dneg sV; ue. 
    rewrite ssi; apply: alx => //.
  rewrite ssi; apply: aly => //.
move=> i ij.
have idf: inc i (domain f) by rewrite - srdf; order_tac.
move: (jle _ ij); rewrite ! LgV//.
move: (order_morphism_fi  (sip _ idf)) =>[_ insi].
move: (sip _ idf) => [_ _ [fsi ssi tsi] jsrp].
apply: insi; rewrite  ssi;[ apply: alx => // | apply: aly => //].
Qed.

Lemma oprod_increasing2 r f g: worder r ->
  substrate r = domain f -> substrate r = domain g ->
  (forall x, inc x (domain f) -> (Vg f x) <=o (Vg g x)) ->
  finite_set (substrate r) ->
  (oprod r f) <=o (oprod r g).
Proof.
move=> wor sf sg alo fse.
apply/ordinal_le_P0; apply /order_le_compatible1.
    apply: orprod_wor => //; [ saw | hnf; aw ].
    move=> i idf; rewrite ! LgV//; move: (alo _ idf) => [aa bb _]; fprops.
  apply: orprod_wor => //; [saw | hnf;aw ].
  rewrite - sg sf; move=> i idf.
  have idg: inc i (domain g) by rewrite - sg sf.
  rewrite !LgV//; move: (alo _ idf) => [aa bb _]; fprops.
rewrite /Lgcomp - sg sf.
apply: oprod_increasing1.
    split => //; hnf; aw; trivial => i idf; rewrite LgV//;move: (alo _ idf) =>[aa bb _];fprops.
  split => //; hnf; aw; trivial.
  move => i idf; rewrite LgV//; move: (alo _ idf) =>[aa bb _]; fprops.
aw => x xdf; move: (alo _ xdf) =>[aa bb le].
apply /order_le_compatible1; rewrite !LgV//; fprops.
by rewrite (ordinal_o_o aa)  (ordinal_o_o bb); apply/ordinal_le_P0. 
Qed.

Lemma oprod_increasing3 r f j:
  orprod_ax r f -> 
  sub j (domain f) -> 
  (forall x, inc x  ((domain f) -s j) ->
     substrate (Vg f x) <> emptyset) ->
  (order_prod (induced_order r j) (restr f j)) <=O (order_prod r f).
Proof.
move=> oa jd  anot.
move: (oa) => [or sr alo].
set (g:= Lg (domain f)  (fun z => Yo (inc z j) (Vg f z) (ordinal_o \1o))).
have dfdg: domain f = domain g by rewrite /g; aw.
have oa': orprod_ax r g.
  hnf; rewrite /order_fam /allf - dfdg;split => //.
   move=> i idg; rewrite /g LgV//; Ytac ij; first by apply: alo.  
  by apply: (ordinal_o_or). 
have sjd': sub j (domain g) by ue.
have cz: (forall i, inc i ((domain g) -s j) -> 
  singletonp (substrate (Vg g i))).
  move=> i /setC_P;rewrite -dfdg /g; move=> [idf nij]; rewrite LgV//; Ytac0.
  by rewrite (ordinal_o_sr); exists emptyset.
move: (oprod_unit1 oa' sjd' cz).
have ->: (restr f j = restr g j).
  apply: Lg_exten; aw; move=> x xj; move: (jd _ xj) => xdf.
  by rewrite /g LgV//; Ytac0.
move=> oi1.
have oi2: (order_prod r f) \Is (order_prod r f).
  by apply: orderIR; apply: orprod_or.
apply /(order_le_compatible oi1 oi2).
apply: oprod_increasing1 => //.
rewrite -dfdg; move=> x xdg;  rewrite /g LgV//.
Ytac nij; first by apply: order_leR=>//; apply: alo. 
have p2: order (Vg f x) by move: oa => [q1 q2 q4]; apply: q4.
have [y yd]: nonempty (substrate (Vg f x)).
  case: (emptyset_dichot  (substrate (Vg f x))) => // p1.
  have xcz: inc x ((domain f) -s j) by apply /setC_P. 
  move: (anot _ xcz) => p4; contradiction.
have s1: sub (singleton y) (substrate (Vg f x)) by apply: set1_sub.
set h:= Lf (fun z => y) (singleton emptyset) (singleton y).
have ta: lf_axiom (fun _ : Set => y) (singleton emptyset) (singleton y).
   move=> t _ /=; fprops.
split => //; [fprops | exists h; exists (singleton y); split => //].
rewrite /h;split;fprops. 
    apply (proj1 (iorder_osr p2 s1)).
  rewrite iorder_sr // ordinal_o_sr.
  saw; apply: lf_bijective => //. 
    by move=> u v /set1_P -> /set1_P ->.
  move=> u /set1_P ->; exists emptyset; [fprops | done].
move => u v;rewrite lf_source => aa bb; rewrite ! LfV//.
move: aa bb => /set1_P -> /set1_P ->.
split;  move => _.
  by apply /iorder_gle0P; fprops; order_tac.
rewrite / \1o/ \1c;apply /ordo_leP;split;fprops.
Qed. 

Lemma oprod_increasing4 r f j:  
  worder_on r (domain f) -> sub j (domain f) -> ordinal_fam f ->
  finite_set (substrate r) ->
  (forall x, inc x ((domain f) -s j)  -> Vg f x <> \0o) ->
  (oprod (induced_order r j) (restr f j)) <=o (oprod r f).
Proof.
move => [wor sr] sjf alo fsr alnz.
have sjr: sub j (substrate r) by ue.
have or: order r by move: wor => [or _].
apply /ordinal_le_P0; apply /order_le_compatible1.
    apply: orprod_wor. 
    - aw; split;[ by apply: induced_wor | rewrite iorder_sr// ].
    - hnf; aw; move=> i ij; rewrite LgV// ? LgV//; aw; fprops.
    - rewrite iorder_sr //; apply: (sub_finite_set sjr fsr).
  apply: orprod_wor => //; [ saw | hnf;aw ].
  move=> i idf; rewrite LgV // ; fprops. 
set g:= (Lgcomp f ordinal_o).
have ->:(Lgcomp (restr f j) ordinal_o)  = restr g j.
    rewrite /Lgcomp; aw; apply: Lg_exten => x xj.
    by rewrite /g ! LgV//; apply: sjf.
apply: oprod_increasing3 => //. 
    rewrite /g;split=> //;hnf; aw;trivial; move=> i idf; rewrite !LgV// ; fprops. 
  by rewrite /g; aw.
move => x; rewrite {1} /g; aw => xd; move: (alnz _ xd).
move: xd => /setC_P [xdf _]; move: (alo _ xdf) => ov.
by rewrite /g LgV //  ordinal_o_sr.
Qed.

(** Order types *)


Parameter order_type_of: Set -> Set.
Axiom order_type_exists: 
  forall x, order x -> x \Is (order_type_of x).
Axiom order_type_unique:
  forall x y, x \Is y -> (order_type_of x = order_type_of y).
Definition order_type x := exists2 y, order y & x = order_type_of y.

Definition order_type_le x y:=
   [/\ order_type x, order_type y &
   exists f z, 
    sub z (substrate y) /\ order_isomorphism f x (induced_order y z)].

Notation "x <=t y" := (order_type_le x y) (at level 60).


Lemma OT_ordinal_compat x: worder x ->
  order_type_of x = order_type_of (ordinal_o (ordinal x)).
Proof.
by move=> wor; apply: order_type_unique;move:(ordinal_o_is  wor).
Qed.

Lemma OT_prop0 x: order x -> (order_type_of x) \Is x.
Proof. by  move=> ox; apply: orderIS; apply: order_type_exists. Qed.


Lemma OT_prop1 x: order x -> order_type (order_type_of x).
Proof. by move=>  ox; exists x. Qed.

Lemma OT_prop2 x:  order_type x -> order x.
Proof.
move=>  [y pa pb].
by move: (order_type_exists pa); rewrite -pb; move=> [f [oy ox _]].
Qed.

Lemma OT_prop3 x: order x -> order (order_type_of x).
Proof. by move =>  ox; apply: OT_prop2; apply: OT_prop1. Qed.

Lemma OT_prop4 x: order x -> 
  order_type_of (order_type_of x) = order_type_of x.
Proof.
move =>  ox.
by apply: order_type_unique; apply: orderIS; apply: order_type_exists.
Qed.

Lemma order_le_alt4 r r': r <=O r' ->
   (exists f, order_morphism f r r').
Proof.
move=>  [o1 o2 [f [z [sr [oa ob [[ [ff injf] sjf] sf tf] etc]]]]].
move: tf; rewrite iorder_sr // => tf.
have ta: lf_axiom (Vf f)  (substrate r) (substrate r').
   rewrite - sf; move=> t tsf; apply: sr; Wtac.
exists (Lf (Vf f) (substrate r) (substrate r')).  
split => //;first saw.
  by apply: lf_function. 
red; aw;move=> x y xsr ysr; rewrite ! LfV//;rewrite - sf in xsr ysr. 
split => h; first by move/(etc _ _ xsr ysr): h => t; exact (iorder_gle1 t).
apply /(etc _ _ xsr ysr); apply /iorder_gle0P => //; Wtac. 
Qed.

Lemma order_le_alt3P r r':
  r <=O r' <-> (exists f, order_morphism f r r').
Proof.
split.
  apply: order_le_alt4.
 move => h; move: (h) => [_ [or or' _ _]]. 
by apply: order_le_alt.
Qed.

Lemma order_le_transitive x y z:
  x <=O y -> y <=O z -> x <=O z.
Proof.
move=>  [ox oy [f [y1 [pa pb]]]] [_ oz [g [z1 [pc pd]]]].
split => //.
move: pb => [orx oix [[[ff injf] sjf]  sf tf] etcf].
move: pd => [ory oiy [[[fg injg] sjg] sg tg] etcg].
move: tf tg; rewrite ! iorder_sr// => tf tg.
set z2:= Vfs g y1.
have y1sg: sub y1 (source g) by ue.
have sz2z1: sub z2 z1 by rewrite - tg /z2; apply: fun_image_Starget1.
have sz2: sub z2 (substrate z) by apply: (sub_trans sz2z1). 
set h:= Lf (fun t => (Vf g (Vf f t))) (substrate x) z2.
have ta: lf_axiom (fun t => Vf g(Vf f t)) (substrate x) z2.
  rewrite - sf;move=> t rx; apply /(Vf_image_P fg y1sg).
  exists (Vf f t) => //; Wtac.
move: (iorder_osr oz sz2) => [pa1 pb1].
exists h; exists z2; split => //; rewrite /h; split;fprops.
  rewrite pb1;saw;apply: lf_bijective => //.
    rewrite - sf => u v ux vx sw; apply: injf => //.
    apply: injg =>//; rewrite sg; apply: pa; rewrite - tf;Wtac.
  move=> u /(Vf_image_P fg y1sg) [a ay1] ->.
  move: ay1; rewrite - tf => af; move: ((proj2 sjf) _ af).
  move=> [b bsf ->]; exists b => //; ue.
red; aw;move => a b asf bsf; rewrite !LfV //.
move: (ta _ asf)  (ta _ bsf) => ta1 ta2.
rewrite - sf in asf bsf.
have wa: inc (Vf f a) y1 by rewrite - tf; Wtac.
have wb: inc (Vf f b) y1 by rewrite - tf; Wtac.
have wa1: inc (Vf f a) (source g) by ue.
have wb1: inc (Vf f b) (source g) by ue. 
set H1 := (etcf _ _ asf bsf); set Hb := (etcg _ _ wa1 wb1).
split.
 move /H1 => p1; apply /iorder_gle0P => //.
 move: (iorder_gle1 p1); move /Hb => p2; exact :(iorder_gle1 p2).
move => p2; apply /H1;apply /iorder_gle0P => //; apply /Hb.
move: (iorder_gle1 p2) => p1.
by apply /iorder_gle0P => //; apply: sz2z1.
Qed.

Lemma OTorder_le_altP r r':
  r <=t r' <-> [/\ order_type r, order_type r' &
    exists f, order_morphism f r r'].
Proof.
split;move=> [o1 o2 etc]; split => //.
  apply /order_le_alt3P.
  by split => //; by apply: OT_prop2.
by move: (order_le_alt (OT_prop2 o1)(OT_prop2 o2) etc) => [_ _].
Qed.

Lemma OTorder_le_compat1 r: order r ->
  r <=O (order_type_of r).
Proof.
move=> or; apply /order_le_alt3P.
move: (order_type_exists or) => [f oi]; exists f => //.
by apply: order_isomorphism_w.
Qed.

Lemma OTorder_le_compat2 r: order r ->
  (order_type_of r) <=O r.
Proof.
move=> or; apply /order_le_alt3P.
move: (OT_prop0 or) => [f oi]; exists f => //.
by apply: order_isomorphism_w.
Qed.

Lemma OTorder_le_compatP r r': order r -> order r' ->
  (r <=O r' <-> (order_type_of r) <=O (order_type_of r')).
Proof.
move=> or or'. 
split => h.
  apply: (@order_le_transitive _ r).
   apply: OTorder_le_compat2 => //.
  apply: (@order_le_transitive _ r') => //.
  apply: OTorder_le_compat1 => //.
apply: (@order_le_transitive _ (order_type_of r)).
   apply: OTorder_le_compat1 => //.
  apply: (@order_le_transitive _ (order_type_of r')) => //.
apply: OTorder_le_compat2 => //.
Qed.

Lemma OT_order_le_reflexive x: order_type x -> x <=t x.
Proof.
move=> ox; split => //; exists (identity (substrate x)); exists (substrate x).
split; first by fprops.
move: (OT_prop2 ox) => orx.
rewrite (iorder_substrate orx); exact: (identity_is orx).
Qed.

Lemma OTorder_le_alt2P r r':
  r <=t r' <-> [/\ order_type r, order_type r' & r <=O  r'].
Proof.  
split; first by move /OTorder_le_altP => [pa pb /order_le_alt3P pc]. 
by move => [pa pb /order_le_alt3P pc]; apply /OTorder_le_altP.
Qed.

Lemma OT_order_le_transitive x y z: 
  x <=t y -> y <=t z -> x <=t z.
Proof.
move /OTorder_le_alt2P => [pa pb pc] /OTorder_le_alt2P [pd pe pf].
apply /OTorder_le_alt2P. 
split => //; apply: (order_le_transitive pc pf).
Qed.

Definition OT_sum r g :=  
   order_type_of (order_sum r (Lg (domain g) (fun z => (order_type_of (Vg g z))))).
Definition OT_prod r g :=  
   order_type_of (order_prod r (Lg (domain g) (fun z => (order_type_of (Vg g z))))).
Definition OT_sum2 a b := 
  order_type_of (order_sum2 (order_type_of a) (order_type_of b)).
Definition OT_prod2 a b := 
  order_type_of (order_prod2 (order_type_of a) (order_type_of b)).


Notation "x +t y" := (OT_sum2 x y) (at level 50).
Notation "x *t y" := (OT_prod2 x y) (at level 40).

Lemma OT_sum2_pr a b:
  a +t b = OT_sum canonical_doubleton_order (variantLc a b).
Proof. 
rewrite /OT_sum2 /OT_sum /order_sum2.
by rewrite variantLc_comp.
Qed.

Lemma OT_prod2_pr a b:
  a *t b = OT_prod canonical_doubleton_order (variantLc b a).
Proof.
rewrite /OT_prod2 /OT_prod /order_prod2.
by rewrite variantLc_comp.
Qed.

Lemma OT_sum2_pr2 a b: order a -> order b ->
  OT_sum2 (order_type_of a) (order_type_of b) = 
  order_type_of (order_sum2 a b).
Proof.
move => oa ob; symmetry.
rewrite /OT_sum2  OT_prop4 // OT_prop4 //; apply: order_type_unique. 
by apply: orsum_invariant4; apply: order_type_exists.
Qed.

Lemma OT_prod2_pr2 a b: order a -> order b ->
  OT_prod2 (order_type_of a) (order_type_of b) = 
  order_type_of (order_prod2 a b).
Proof.
move => oa ob; symmetry.
rewrite /OT_prod2  OT_prop4 // OT_prop4 //; apply: order_type_unique. 
by apply: orprod_invariant4; apply: order_type_exists.
Qed.

Lemma OT_sum_ordertype r g:
  order r -> substrate r = domain g -> order_fam g ->
   order_type (OT_sum r g).
Proof.
move=>  or sr  alo; apply: OT_prop1.
apply: orsum_or; split => //; aw; trivial.
by hnf; aw; move=> i idg; rewrite LgV//; apply:  OT_prop3; apply: alo.
Qed.

Lemma OT_prod_ordertype r g:
  worder r -> substrate r = domain g -> order_fam g
  -> order_type (OT_prod r g).
Proof.
move=> or sr alo; apply: OT_prop1.
apply: orprod_or; split => //; hnf; aw; trivial.
by move=> i idg; rewrite LgV//;apply:  OT_prop3; apply: alo.
Qed.


Lemma OT_sum2_ordertype a b: order_type a -> order_type b ->
  order_type (a +t b).
Proof. 
move=> wo1 wo2;rewrite /OT_sum2; apply: OT_prop1. 
by apply: orsum2_or;apply: OT_prop3; apply: OT_prop2.
Qed.

Lemma OT_prod2_ordertype a b: order_type a -> order_type b ->
  order_type (a *t b).
Proof. 
move=> wo1 wo2;rewrite /OT_prod2; apply: OT_prop1.
by apply: orprod2_or; apply: OT_prop3; apply: OT_prop2.
Qed.

Lemma OT_sum_invariant3 r g:
  order r -> substrate r = domain g -> order_fam g ->
  order_type_of (order_sum r g) = 
    OT_sum r (Lg (substrate r) (fun i => order_type_of (Vg g i))).
Proof.
move => or sr alo.
rewrite /OT_sum;apply: order_type_unique.
apply: orsum_invariant2; fprops;aw; trivial.
rewrite sr;move=> i isr ; rewrite !LgV//; move: (alo _ isr) => oi.
by rewrite OT_prop4 //; apply: order_type_exists.
Qed.

Lemma OT_prod_invariant3 r g:
  worder r -> substrate r = domain g -> order_fam g ->
  order_type_of (order_prod r g) = 
    OT_prod r (Lg (substrate r) (fun i => order_type_of (Vg g i))).
Proof.
move => or sr alo.
rewrite /OT_prod;apply: order_type_unique.
apply: orprod_invariant2;fprops;aw; trivial.
rewrite sr;move=> i isr ; rewrite !LgV//; move: (alo _ isr) => oi.
by rewrite OT_prop4 //; apply: order_type_exists.
Qed.


Lemma OT_sum_invariant5 a b c: order a -> order b -> order c ->
  (order_sum2 a b) \Is c ->
  (order_type_of a) +t (order_type_of b) = order_type_of c.
Proof.
move=> oa ob oc => h. 
rewrite /osum2; apply: order_type_unique.
rewrite OT_prop4 // OT_prop4 //.
by apply: (@orderIT  (order_sum2 a b)) => //;
   apply: orsum_invariant4;apply: OT_prop0.
Qed.

Lemma OT_prod_invariant5 a b c: order a -> order b -> order c ->
  (order_prod2 a b) \Is c ->
  (order_type_of a) *t (order_type_of b) = order_type_of c.
Proof.
move=> oa ob oc => h. 
rewrite /osum2; apply: order_type_unique.
rewrite OT_prop4 // OT_prop4 //.
by apply: (@orderIT  (order_prod2 a b)) => //;
   apply: orprod_invariant4;apply: OT_prop0.
Qed.


Definition order_type_fam g := (allf g order_type).

Lemma OT_sum_assoc1 r g r' g':
  order r -> substrate r = domain g  -> order_type_fam g ->
  order r' -> substrate r' = domain g' ->   order_fam g' ->
  r = order_sum r' g' ->
  let order_sum_assoc_aux :=
    fun l =>
    OT_sum (Vg g' l) (Lg (substrate (Vg g' l)) (fun i => Vg g (J i l))) in
  OT_sum r g = OT_sum r' (Lg (domain g') (order_sum_assoc_aux)).  
Proof.
move=>  wor sr alB wor' sr' alw oal osa.
rewrite /OT_sum. 
have oa': orsum_ax r' g' by [].
apply: order_type_unique.
set g'' := (Lg (domain g) (fun z => order_type_of (Vg g z))).
have oa: orsum_ax r g''. 
  rewrite /g'';red;aw; split => //;hnf; aw;  move=> i idg; rewrite !LgV//. 
  by move: (OT_prop3 (OT_prop2 (alB _ idg))).
move: (orsum_assoc_iso oa oa' oal) => /=.
set aux' := fun l =>
    order_sum (Vg g' l) (Lg (substrate (Vg g' l)) (fun i => Vg g'' (J i l))).
set f:= Lf _ _ _. 
move => oi1; move: (oi1) => [o1 o2 _ _].
apply: (@orderIT (order_sum r' (Lg (domain g') aux'))); first by exists f. 
apply: orsum_invariant2 =>//; aww.
rewrite sr';move=> i isr;  rewrite !LgV//; rewrite /osa /OT_sum; aw.
set s := order_sum _ _.
have os: order s.
  rewrite /s; apply: orsum_or; split => //; aw;trivial; first  by apply: alw.
  hnf; aw;move=> j js; rewrite !LgV//.
  have jdg: inc (J j i) (domain g).
    by rewrite - sr oal  (orsum_sr oa'); apply: disjoint_union_pi1.
  apply: (OT_prop3 (OT_prop2 (alB _ jdg))).
have -> : (aux' i = s).
  rewrite /aux' /s; apply: f_equal.
  apply: Lg_exten => //;move=> j js.
  have pd: inc (J j i) (domain g). 
    by rewrite - sr oal (orsum_sr oa');  by apply: disjoint_union_pi1.
  rewrite /g'' ! LgV//.
by rewrite OT_prop4 //; apply: order_type_exists.
Qed.


Lemma OT_prod_assoc1 r g r' g':
  worder r -> substrate r = domain g  -> order_type_fam g ->
  worder r' -> substrate r' = domain g' ->  worder_fam g' ->
  r = order_sum r' g' ->
  (forall i, inc i (domain g') ->  finite_set (substrate (Vg g' i))) ->
  let order_prod_assoc_aux :=
    fun l =>
    OT_prod (Vg g' l) (Lg (substrate (Vg g' l)) (fun i => Vg g (J i l))) in
  OT_prod r g = OT_prod  r' (Lg (domain g') order_prod_assoc_aux).
Proof.
move=>  wor sr alB wor' sr' alw oal  alfs osa.
rewrite /OT_prod. 
have oa': orsum_ax r' g'.  
  by split;fprops; move => t ta; move: (proj1 (alw _ ta)).
apply: order_type_unique.
set g'' := (Lg (domain g) (fun z => order_type_of (Vg g z))).
have oa: orprod_ax r g''.
  rewrite /g'';red; aw;split => //; hnf;aw; move=> i idg; rewrite LgV//.
  apply: (OT_prop3 (OT_prop2 (alB _ idg))).
move: (orprod_assoc_iso oa oa' oal wor' alw) => /=.
set aux' := fun l =>
    order_prod (Vg g' l) (Lg (substrate (Vg g' l)) (fun i => Vg g'' (J i l))).
set f:= Lf _ _ _.
move => oi1; move: (oi1) => [o1 o2 _ _].
apply: (@orderIT (order_prod r' (Lg (domain g') aux')));
    first by exists f.
apply: orprod_invariant2 =>//; aww. 
rewrite sr';move=> i isr;  rewrite LgV//; rewrite /osa /OT_prod;aw.
rewrite ! LgV //; aw.
set s:= order_prod _ _.
have -> : (aux' i = s).
  rewrite /aux' /s; apply: f_equal.
  apply: Lg_exten => //;move=> j js.
  have pd: inc (J j i) (domain g). 
    by rewrite - sr oal (orsum_sr oa');  by apply: disjoint_union_pi1.
  rewrite /g''; aw; rewrite ! LgV//.
have os: order s. 
rewrite /s; apply: orprod_or; saw; first fprops.
  hnf; aw;move=> j js; rewrite !LgV//.
  have jdg: inc (J j i) (domain g).
    rewrite - sr oal  (orsum_sr oa');  by apply: disjoint_union_pi1.
  apply: (OT_prop3 (OT_prop2 (alB _ jdg))).
by rewrite OT_prop4 //; apply: order_type_exists.
Qed.

Lemma OT_sum_assoc3 a b c:
  order_type a -> order_type b -> order_type c ->
  a +t (b +t c) = (a +t b) +t c.
Proof. 
move => oa ob oc. 
have xoa: order (order_type_of a) by apply: OT_prop3; apply: OT_prop2.
have xob: order (order_type_of b) by apply: OT_prop3; apply: OT_prop2.
have xoc: order (order_type_of c) by apply: OT_prop3; apply: OT_prop2.
rewrite/OT_sum2; apply: order_type_unique.
have pa: order (order_sum2 (order_type_of b) (order_type_of c)).
  by apply: orsum2_or.
have pb: order (order_sum2 (order_type_of a) (order_type_of b)).
  by apply: orsum2_or.
rewrite OT_prop4 // OT_prop4 //.
apply: (@orderIT 
    (order_sum2 (order_type_of a) (order_sum2 (order_type_of b) (order_type_of c)))).
  apply: orsum_invariant4; [by apply: orderIR | by apply: OT_prop0 ].
apply: (@orderIT 
  (order_sum2 (order_sum2 (order_type_of a) (order_type_of b))(order_type_of c))).
apply: osum_assoc2; fprops.
apply: orsum_invariant4; [ by apply: order_type_exists | by apply: orderIR].
Qed.

Lemma OT_prod_assoc3 a b c:
  order_type a -> order_type b -> order_type c ->
  a *t (b *t c) = (a *t b) *t c. 
Proof. 
move => oa ob oc. 
have xoa: order (order_type_of a) by apply: OT_prop3; apply: OT_prop2.
have xob: order (order_type_of b) by apply: OT_prop3; apply: OT_prop2.
have xoc: order (order_type_of c) by apply: OT_prop3; apply: OT_prop2.
rewrite/OT_prod2; apply: order_type_unique.
have pa: order (order_prod2 (order_type_of b) (order_type_of c)).
  by apply: orprod2_or.
have pb: order (order_prod2 (order_type_of a) (order_type_of b)).
  by apply: orprod2_or.
rewrite OT_prop4 // OT_prop4 //.
apply: (@orderIT 
 (order_prod2 (order_type_of a)  (order_prod2 (order_type_of b) (order_type_of c)))).
  apply: orprod_invariant4; [ by apply: orderIR |by apply: OT_prop0 ].
apply: (@orderIT 
  (order_prod2 (order_prod2 (order_type_of a) (order_type_of b))(order_type_of c))).
apply:  oprod_assoc2; fprops.
apply: orprod_invariant4; [ by apply: order_type_exists | by apply: orderIR].
Qed.

Lemma OT_sum_distributive3 a b c:
  order_type a -> order_type b -> order_type c ->
  c *t (a +t b) = (c *t a) +t (c *t b).
Proof.
move => oa ob oc. 
rewrite /OT_sum2 /OT_prod2; apply:  order_type_unique.
have xoa: order (order_type_of a) by apply: OT_prop3; apply: OT_prop2.
have xob: order (order_type_of b) by apply: OT_prop3; apply: OT_prop2.
have xoc: order (order_type_of c) by apply: OT_prop3; apply: OT_prop2.
have pa: order (order_prod2 (order_type_of c) (order_type_of a)).
  by apply: orprod2_or.
have pb: order (order_prod2 (order_type_of c) (order_type_of b)).
  by apply: orprod2_or.
have pc: order (order_sum2 (order_type_of a) (order_type_of b)).
  by apply: orsum2_or.
rewrite OT_prop4 // OT_prop4 // OT_prop4 //.
apply: (@orderIT 
  (order_prod2 (order_type_of c) (order_sum2 (order_type_of a) (order_type_of b)))).
  apply: orprod_invariant4; [ by apply: orderIR | by apply: OT_prop0].
apply: (@orderIT 
     (order_sum2
        (order_prod2 (order_type_of c) (order_type_of a))
        (order_prod2 (order_type_of c) (order_type_of b)))).
  apply: osum_distributive => //. 
by apply: orsum_invariant4;apply: order_type_exists.
Qed.

Lemma OT_sum_increasing2 r f g: order r ->
  substrate r = domain f -> substrate r = domain g ->
  (forall x, inc x (domain f) -> (Vg f x) <=t (Vg g x)) ->
  (OT_sum r f) <=t (OT_sum r g).
Proof.
move=>  wor sf sg alo. 
have Xa: orsum_ax r (Lg (domain f) (fun z : Set => order_type_of (Vg f z))).
  split => //;hnf; aw; trivial;move=> i isf; rewrite LgV//.
  move: (alo _ isf) => [pa pb _].
  by apply: OT_prop3; apply: OT_prop2.
have Xb: orsum_ax r (Lg (domain g) (fun z : Set => order_type_of (Vg g z))).
  split => //; hnf;aw; trivial;rewrite - sg sf.
  move=> i isf; rewrite LgV //; move: (alo _ isf) => [pa pb _].
  by apply: OT_prop3; apply: OT_prop2.
have pa:order (order_sum r (Lg (domain f) (fun z => order_type_of (Vg f z)))).
  by apply: orsum_or. 
have pb:order (order_sum r (Lg (domain g) (fun z => order_type_of (Vg g z)))).
  by apply: orsum_or.
have pc: order_type (OT_sum r f) by  apply: OT_prop1.
have pd: order_type (OT_sum r g) by  apply: OT_prop1.
apply / OTorder_le_altP;split =>// ; apply: order_le_alt4.
apply /(OTorder_le_compatP pa pb); apply:osum_increasing1 => //.
aw; move=> x xdf; rewrite !LgV//; last by rewrite - sg sf.
move: (alo _ xdf); move /OTorder_le_alt2P=> [ot1 ot2]. 
by move /(OTorder_le_compatP (OT_prop2 ot1) (OT_prop2 ot2)).
Qed.

Lemma OT_prod_increasing2 r f g: worder r ->
  substrate r = domain f -> substrate r = domain g ->
  (forall x, inc x (domain f) -> (Vg f x) <=t (Vg g x)) ->
  (OT_prod r f) <=t (OT_prod r g).
Proof.
move=> wor  sf sg alo. 
have Xa: orprod_ax r (Lg (domain f) (fun z : Set => order_type_of (Vg f z))).
  split => //;hnf ;aw; trivial;move=> i isf; rewrite LgV//. 
  move: (alo _ isf) => [pa pb _].
  by apply: OT_prop3; apply: OT_prop2.
have Xb: orprod_ax r (Lg (domain g) (fun z : Set => order_type_of (Vg g z))).
  split => //; hnf;aw; trivial;rewrite - sg sf.
  move=> i isf; rewrite LgV//;move: (alo _ isf) => [pa pb _].
  by apply: OT_prop3; apply: OT_prop2.
have pa:order (order_prod r (Lg (domain f) (fun z => order_type_of (Vg f z)))).
  by apply: orprod_or. 
have pb:order (order_prod r (Lg (domain g) (fun z => order_type_of (Vg g z)))).
  by apply: orprod_or.
have pc: order_type (OT_prod r f) by  apply: OT_prop1.
have pd: order_type (OT_prod r g) by  apply: OT_prop1.
apply /OTorder_le_altP;split => //; apply: order_le_alt4.
apply /(OTorder_le_compatP pa pb).
apply: oprod_increasing1 => //.
aw; move=> x xdf; rewrite ! LgV//; last by rewrite - sg sf.
move: (alo _ xdf); move /OTorder_le_alt2P=> [ot1 ot2]. 
by move /(OTorder_le_compatP (OT_prop2 ot1)(OT_prop2 ot2)).
Qed.

Lemma OT_sum_increasing4 r f j:  order r ->
  substrate r = domain f ->
  sub j (domain f) -> order_type_fam f ->
  (OT_sum (induced_order r j) (restr f j)) <=t (OT_sum r f).
Proof.
move => or  sr sjf alo.
have sjr: sub j (substrate r) by ue.
have dr: (domain (restr f j)) = j by rewrite restr_d //.
have Xa: orsum_ax r (Lg (domain f) (fun z  => order_type_of (Vg f z))).
  split => //; hnf; aw;trivial;move=> i isf; rewrite LgV//;move: (alo _ isf) => iot.
  by apply: OT_prop3; apply: OT_prop2.
have pa:order (order_sum r (Lg (domain f) (fun z => order_type_of (Vg f z)))).
  by apply: orsum_or.
have pc: order_type (OT_sum r f) by  apply: OT_prop1. 
have dj: j = domain (restr f j) by  rewrite restr_d.
move: (iorder_osr or sjr) => [pa' pb'].
have p2:  orsum_ax (induced_order r j)
     (Lg (domain (restr f j)) (fun z : Set => order_type_of (Vg (restr f j) z))).
  split;fprops;hnf;aw; trivial; move=> i idf; rewrite !LgV//.
  move: (sjr _ idf); rewrite sr => i1; move: (alo _ i1) => iot.
  by apply: OT_prop3; apply: OT_prop2.
have pb: order (order_sum (induced_order r j)
        (Lg (domain (restr f j)) (fun z => order_type_of (Vg (restr f j) z)))). 
  by apply: orsum_or.
have pd: order_type (OT_sum (induced_order r j) (restr f j)).
  by apply: OT_prop1.
apply /OTorder_le_altP; split => //; apply: order_le_alt4.
apply /(OTorder_le_compatP pb pa).
set g:= (Lg (domain f) (fun z : Set => order_type_of (Vg f z))).
have fgg: fgraph g by rewrite /g; fprops.
have sjdg: sub j (domain g) by rewrite /g; aw.
have ->: (Lg (domain (restr f j)) (fun z => order_type_of (Vg (restr f j) z)))
   = restr g j.
  by apply: fgraph_exten;aw;fprops;rewrite /g; move => k kj /= ;rewrite !LgV//; apply: sjf.
apply: osum_increasing3 => //. 
Qed.

Lemma OT_prod_increasing4 r f j:  worder r ->
  substrate r = domain f ->
  sub j (domain f) -> order_type_fam f ->
  (forall x, inc x  ((domain f) -s j) ->
     substrate (Vg f x) <> emptyset) ->
  (OT_prod (induced_order r j) (restr f j)) <=t (OT_prod r f).
Proof.
move => or sr sjf alo alne .
have sjr: sub j (substrate r) by ue.
have dr: (domain (restr f j)) = j by rewrite restr_d //.
have Xa: orprod_ax r (Lg (domain f) (fun z  => order_type_of (Vg f z))).
  split => //; hnf;aw; trivial;move=> i isf; rewrite LgV//;move: (alo _ isf) => iot.
  by apply: OT_prop3; apply: OT_prop2.
have pa:order (order_prod r (Lg (domain f) (fun z => order_type_of (Vg f z)))).
  by apply: orprod_or.
have pc: order_type (OT_prod r f) by  apply: OT_prop1. 
have dj: j = domain (restr f j) by  rewrite restr_d.
have odr: order r by move: or => [ok _].
have p2:  orprod_ax (induced_order r j)
     (Lg (domain (restr f j)) (fun z : Set => order_type_of (Vg (restr f j) z))).
  have woi: worder (induced_order r j) by apply:induced_wor.
  split => //; aw;first by  rewrite iorder_sr.
  hnf;aw => i idf; rewrite !LgV//.
  move: (sjr _ idf); rewrite sr => i1; move: (alo _ i1) => iot.
  by apply: OT_prop3; apply: OT_prop2.
have pb: order (order_prod (induced_order r j)
        (Lg (domain (restr f j)) (fun z => order_type_of (Vg (restr f j) z)))). 
  by apply: orprod_or.
have pd: order_type (OT_prod (induced_order r j) (restr f j)).
  by apply: OT_prop1.
apply/OTorder_le_altP; split => //; apply: order_le_alt4.
apply /(OTorder_le_compatP pb pa).
set g:= (Lg (domain f) (fun z : Set => order_type_of (Vg f z))).
have fgg: fgraph g by rewrite /g; fprops.
have sjdg: sub j (domain g) by rewrite /g; aw; ue.
have ->: (Lg (domain (restr f j)) (fun z=> order_type_of (Vg  (restr f j) z)))
   = restr g j.
  by apply: fgraph_exten; aww;rewrite /g; move => k kj /= ;rewrite !LgV//;apply: sjf.
apply: oprod_increasing3 => //.
move=> x; rewrite /g Lgd => xg.
have xdf: inc x (domain f) by move: xg => /setC_P [].
aw; rewrite LgV//;move: (alne _ xg) => t; dneg bad.
move: (order_type_exists (OT_prop2 (alo _ xdf)))
   => [h [_ _ [[[fh _] _] sh tgh] _]].
apply /set0_P => t' ts.
empty_tac1 (Vf h t'); rewrite - tgh; Wtac.
Qed.

Lemma OT_prod_pr1 a b c:
  order_type a -> order_type b -> worder c -> b \Is c ->
  a *t b = OT_sum c (cst_graph (substrate c) a).
Proof. 
move=>  ota otb woc ibc.
rewrite /OT_prod2 /OT_sum.
have ora: order a by apply: OT_prop2.
have orb: order b by apply: OT_prop2.
move: (proj1 woc) => oc.
apply: order_type_unique.
have ->:  domain (cst_graph (substrate c) a) = substrate c.
  by  rewrite /cst_graph; aw.
apply: (@orderIT  (order_prod2 a b)).
  by apply: orprod_invariant4; apply: OT_prop0.
move: (order_prod_pr ora orb);set aux := order_sum _ _ ; move=> h.
apply: (@orderIT aux) => //.  
move: ibc => [f isf].
rewrite /aux /cst_graph; apply: (orsum_invariant1(f:=f)); aw => //.
move: isf => [_ _ [[[ff _] _] sf tf] _].
rewrite - sf; move=> i id.
move: (Vf_target ff id); rewrite -tf=> vt.
by rewrite ! LgV// ; apply: order_type_exists.
Qed.

Definition OT_opposite x := order_type_of (opp_order x).

Lemma OT_opposite1 a b: a \Is b ->
  (opp_order a) \Is (opp_order b).
Proof.
move=>  [f [o1 o2 bp isf]].
move: (opp_osr o1)(opp_osr o2) => [pa pb][pc pd].
exists f;split => //;fprops; rewrite ? pb ? pd //.
move=> x y asf bsf. 
by split; move /opp_gleP /(isf _ _ bsf asf) /opp_gleP.
Qed.

Lemma  OT_opposite2 x: order x -> opp_order (opp_order x) = x.
Proof.  move =>[pa _ _ _]; apply :(igraph_involutive pa). Qed.


Lemma OT_opposite3 a: order a -> OT_opposite (order_type_of a) = OT_opposite a.
Proof.
move => oa.
by apply: order_type_unique; apply:OT_opposite1; apply:OT_prop0.
Qed.

Lemma OT_double_opposite x: order_type x ->
   OT_opposite (OT_opposite x) = x.
Proof.
move=> otx; rewrite /OT_opposite.
have ox : order x by apply: OT_prop2.
have xp1: x= order_type_of x by move: otx => [y yo yp]; rewrite yp OT_prop4 //.
rewrite {2} xp1; apply: order_type_unique.
rewrite -{2} (OT_opposite2 ox);apply: OT_opposite1.
apply: OT_prop0; apply: (proj1 (opp_osr ox)).
Qed.

Lemma OT_opposite_sum r f: order r ->
  substrate r = domain f -> order_type_fam f ->
  OT_opposite (OT_sum r f) =
  OT_sum (opp_order r) (Lg (substrate r) (fun z => OT_opposite (Vg f z))).
Proof.
move=> or sr alo.
rewrite /OT_opposite /OT_sum Lgd; apply: order_type_unique.
set s1 := order_sum _ _.
have alor : forall x , inc x (domain f) -> order (Vg f x).
  move=> i idf; apply: (OT_prop2 (alo _ idf)).
set s2:= order_sum r (Lg (domain f) (fun z => (Vg f z))).
apply: (@orderIT (opp_order s2)).
  apply: OT_opposite1;apply: (@orderIT  s1). 
    apply: OT_prop0.
    apply: orsum_or;split => //; hnf; aw; trivial => i idf; rewrite LgV//. 
    apply: (OT_prop3 (alor _ idf)).
  rewrite /s1 /s2.
  apply: orsum_invariant2 ; aww. 
  rewrite sr;move=> i isr; rewrite !LgV//; apply: (OT_prop0 (alor _ isr)).
set g := (Lg (domain f) (fun z => (opp_order (Vg f z)))).
move: (opp_osr or) => [pa pb].
have ta: orsum_ax (opp_order r) g.
  rewrite /g;split => //;fprops;aw;first by ue.
  hnf; aw;move=> i idf; rewrite LgV//; exact: (proj1 (opp_osr (alor _ idf))). 
have os2: order s2. 
  by apply: orsum_or; split => //; hnf; aw; trivial; move=> i idf; rewrite LgV//; apply: alor.
have tb:orsum_ax r (Lg (domain f) (fun z => Vg f z)).
  split => //; hnf; aw; trivial.
  move=> i idf; rewrite LgV//; move: (alor _ idf) => aux; fprops.
have osg: order (order_sum (opp_order r) g) by apply: orsum_or.  
have ss:substrate (order_sum (opp_order r) g) = substrate s2.
  rewrite /s2 orsum_sr // orsum_sr //.
  rewrite /sum_of_substrates /fam_of_substrates /g; aw.
  apply: f_equal; apply: Lg_exten => // x xdf; rewrite !LgV //.
  apply (proj2 (opp_osr (alor _ xdf))).
apply: (@orderIT (order_sum (opp_order r) g)).
  move: ( identity_fb (substrate s2)) => hh.
  move: (opp_osr os2) => [oo3 sr2].
  exists (identity (substrate s2)).
  split;fprops; first split;aww.
  hnf;aw;move => x y xsr ysr; rewrite !idV //.
  have qy:inc (Q y) (domain f).
    move: ysr; rewrite /s2 orsum_sr // => h. 
    by move: (du_index_pr1 h) => [h1 _]; move: h1; aw.
  have qx:inc (Q x) (domain f).
    move: xsr; rewrite /s2 orsum_sr // => h. 
    by move: (du_index_pr1 h) => [h1 _]; move: h1; aw.
  have sgs2: sum_of_substrates g = substrate s2.
    by move: ss;  rewrite /s2 orsum_sr // orsum_sr //. 
  have sgs3: (sum_of_substrates (Lg (domain f) (Vg f)))  = substrate s2.
    rewrite /s2  orsum_sr  //.
  split.
    move /opp_gleP => ha; apply /orsum_gleP; rewrite sgs2;split => //.
    move: ha => /orsum_gleP [pa' pb']; case => pc. 
       by left; apply /opp_gltP.
    rewrite /order_sum_r;right; move: pc => [];rewrite LgV//; move => -> pc; split => //.
    by rewrite /g ! LgV//; apply /opp_gleP.
  move /orsum_gleP => [_ _ h]; apply  /opp_gleP; apply /orsum_gleP.
  rewrite sgs3;split => //; case: h; first by  move /opp_gltP => h;left.
  move => [sq]; rewrite /g LgV//;move  /opp_gleP => h.
  right; rewrite !LgV//. split => //; ue.
apply: orsum_invariant2 => //; rewrite /g pb; aw; trivial.
rewrite sr;move=> i isr; rewrite !LgV//.
move: (alor _ isr) => aux.
have aux2: order (opp_order (Vg f i)) by apply: (proj1 (opp_osr (alor _ isr))).
by rewrite OT_prop4 //; apply: order_type_exists.
Qed.

(* deplacer *)
Lemma OT_prop5 r: order_type r -> order_type_of r = r.
Proof.  by move => [p op ->]; rewrite OT_prop4. Qed.

  
Lemma OTsum_set1 r g i:
  order_on r (domain g) -> 
  domain g = singleton i -> order_type (Vg g i) ->
  OT_sum r g = Vg g i.
Proof. 
move=> [or sr] dgi otve.
have idg: inc i (domain g) by rewrite dgi; fprops.
have eqa:= (OT_prop5 otve).
have or1:= (OT_prop2 otve).
rewrite /OT_sum.
set g1 := Lg (domain g) (fun z => Vg g i).
have ->: Lg (domain g) (fun z => order_type_of (Vg g z)) = g1.
  by apply: Lg_exten => k kdg; aw; move:kdg; rewrite dgi => /set1_P ->.
suff:  (order_sum r g1) \Is Vg g i.
  by move => /order_type_unique; rewrite (OT_prop5 otve).
have osa: orsum_ax r g1.
   rewrite /g1. hnf; aw;split => //; hnf; aw => x xdg; rewrite LgV//.
set (E:= substrate (order_sum r g1)); set (F := substrate (Vg g i)).
have He:E = sum_of_substrates g1 by rewrite /E orsum_sr //.
have uE: (forall u, inc u E <-> [/\ pairp u, Q u = i &inc (P u) F]).
  move=> u; rewrite He /g1;  split.
    move=> us; move: (du_index_pr1 us) => [].
    rewrite Lgd; move=> Qu. rewrite LgV//.
    move: Qu; rewrite dgi=> /set1_P -> pa pb; split => //; ue.
  move => [pu Qu Pu]; rewrite - pu Qu; apply: disjointU_pi; aw; trivial.
  rewrite LgV// ; aw; trivial;rewrite LgV//.
have ta: (lf_axiom P E F) by move=> t /uE [_].
exists (Lf P E F).
split; fprops; first (hnf;saw).
  apply: lf_bijective => //. 
    move=> u v  =>/uE [pu Qu Pu] /uE [pv Qv Pv] sp.
    apply: pair_exten =>//; ue.
  move=> y ys; exists (J y i); aw => //; apply /uE; aw;split;fprops.
hnf; aw => a b aE bE;  rewrite ! LfV//.
move: (aE)(bE) => /uE  [pu Qu Pu] /uE [pv Qv Pv].
have aux: inc (Q a) (domain g) by rewrite Qu dgi; fprops.
split.
  move /orsum_gleP => [_ _]; rewrite/order_sum_r Qu Qv; case; case => //.
  rewrite /g1 LgV//.
move => h; apply /orsum_gleP;hnf; rewrite - He /order_sum_r /g1 LgV//.
by split => //; rewrite Qu Qv; right.
Qed.

Lemma OTsum_Mle0 a b: order_type a -> order_type b ->
     a <=t a+t b /\ b <=t a +t b.
Proof.
move => oa ob.
move: cdo_wor => [wor sr].
have ha: substrate canonical_doubleton_order = domain (variantLc a b).
  by rewrite sr; aw.
have hb: sub (singleton C0) (domain (variantLc a b)).
   aw => t /set1_P->; apply: set2_1.
have hc: sub (singleton C1) (domain (variantLc a b)).
   aw => t /set1_P->; apply: set2_2.
have hd: order_type_fam (variantLc a b). 
  by hnf; aw => x xt; try_lvariant xt.
move:(OT_sum_increasing4 (proj1 wor) ha hb hd).
move:(OT_sum_increasing4 (proj1 wor) ha hc hd).
rewrite - OT_sum2_pr.
have ta1: domain (restr (variantLc a b) (singleton C1)) = singleton C1 by aw.
have ta0: domain (restr (variantLc a b) (singleton C0)) = singleton C0 by aw.
have td0: Vg (restr (variantLc a b) (singleton C0)) C0 = a.
  by rewrite LgV//; aww.
have td1: Vg (restr (variantLc a b) (singleton C1)) C1 = b.
  by rewrite LgV //; aww.
rewrite - td0 in oa; rewrite - td1 in ob. 
move: hb hc; rewrite -ha => hb hc.
move: (iorder_osr (proj1 wor) hb); rewrite {1} /order_on - {3} ta0 => tc0.
move: (iorder_osr (proj1 wor) hc); rewrite {1} /order_on - {3} ta1 => tc1.
by rewrite (OTsum_set1 tc1 ta1 ob) (OTsum_set1 tc0 ta0 oa) td0 td1.
Qed.
  

Lemma OTsum_Mle1 a b c d: a <=t b -> c <=t d -> (a+t c) <=t (b+t d).
Proof.
move => le1 le2.
move: cdo_wor => [wor sr].
pose f :=  (variantLc a c).
pose g :=  (variantLc b d).
have ha: substrate  canonical_doubleton_order = domain f by rewrite sr/f; aw.
have hb: substrate  canonical_doubleton_order = domain g by rewrite sr/g; aw.
have hc: (forall x, inc x (domain f) -> Vg f x <=t Vg g x).
  by rewrite /f /g; aw => i idx; try_lvariant idx.
move:(OT_sum_increasing2 (proj1 wor) ha hb hc). 
by rewrite  - OT_sum2_pr  - OT_sum2_pr.
Qed.


Lemma OTsum_Mle2 a  c d: order_type a -> c <=t d -> (a+t c) <=t (a+t d).
Proof. move /OT_order_le_reflexive; apply: OTsum_Mle1. Qed.


Definition singleton_order := singleton (J emptyset emptyset).
Definition singleton_OT := order_type_of singleton_order.
Notation "\1t" := singleton_OT.

Lemma singleton_order_or: order singleton_order. 
Proof. exact: (proj1 (proj1 (set1_wor emptyset))). Qed.

Lemma OT_1_or : order \1t.
Proof. exact: (OT_prop3 singleton_order_or). Qed.

Lemma OT_cardinal_1: cardinal (substrate singleton_order) = \1c.
Proof. by rewrite (proj2 (set1_wor emptyset)) cardinal_set1. Qed.


Lemma OT_1_order_type : order_type \1t.
Proof. exact: OT_prop1 singleton_order_or. Qed.



Lemma singleton_OT_pr: exists x, \1t = singleton (J x x).
Proof.
move: (set1_wor emptyset) => [[or _] sr]. 
move: (OT_prop0 or) => [f []]. 
rewrite sr  -/singleton_order -/ singleton_OT => o1 _ fp fc.
apply: set1_order_is1 => //; apply/ set_of_card_oneP.
by rewrite -(cardinal_set1 emptyset); apply /card_eqP; exists f.
Qed.


Lemma OT_1_least_nz x: order_type x -> x <> emptyset -> \1t <=t x.
Proof.
move:OT_1_order_type => ha hb hc; apply/OTorder_le_altP; split => //.
move:(OT_prop2 ha) (OT_prop2 hb) => oa ob.
set E := substrate x.
case: (emptyset_dichot E);[ by move/empty_substrate_zero | move =>[a aE]].
move: singleton_OT_pr =>[b bp].
move: (set1_wor b); rewrite - bp; move =>[wo1 sr1].
pose f := Lf (fun z => a )(singleton b) E.
have ax: lf_axiom (fun _ => a) (singleton b) E  by move => t. 
exists f.
split => //; first by  rewrite/f;saw; [ by apply:lf_function | done].
hnf;rewrite /f ; aw => u v ud vd; rewrite ! LfV//; split => _; first by order_tac.
by rewrite (set1_eq ud) (set1_eq vd) bp; apply: set1_1.
Qed.
  

Lemma OT_set0: order_type_of emptyset = emptyset.
Proof.
move: set0_wor =>[[qa _] qb]; apply:empty_substrate_zero.
ex_middle bad; move/nonemptyP: bad => [t tE].
move: (OT_prop0 qa) => [f [_ _ [[[ff _] _] sf yf] _]].
by rewrite - sf in tE;move: (Vf_target ff tE); rewrite yf qb => /in_set0.
Qed.

Definition OT_of_nat n := order_type_of (ordinal_o n).


Lemma OT_of_nat_order_type x:  order_type (OT_of_nat x). 
Proof.
by apply: OT_prop1; apply: ordinal_o_or.
Qed.


Lemma OT_nat_0 : OT_of_nat \0o = emptyset.
Proof.
by rewrite /OT_of_nat ordinal_o_set0;apply: OT_set0.
Qed.

Lemma OT_nat_1 : OT_of_nat \1o = \1t.
Proof.
congr (order_type_of _).
set_extens t.
  move=> /Zo_S /setX_P[p /set1_P ha /set1_P hb].
  by apply/set1_P;rewrite - p ha hb.
move => /set1_P ->; apply: Zo_i; last by aw.
by apply: setXp_i; apply: set1_1.
Qed.
  

Lemma OT_nat_card n: natp n -> cardinal (substrate (OT_of_nat n)) = n.
Proof.
move => nN.
move: (order_type_exists  (ordinal_o_or n)) => [f [_ _ /equipotent_bp fp _] ].
by move/card_eqP:fp; rewrite ordinal_o_sr (card_card (CS_nat nN)); move <-.
Qed. 

Lemma OT_finite_ordered r (E := substrate r):
  total_order r -> finite_set E -> 
  order_type_of r = OT_of_nat  (cardinal E).
Proof.
move => ha hb; rewrite (order_type_unique (finite_ordered_interval2 ha hb)).
rewrite -/E.
set n := (cardinal E).
suff: (Nint_co n) = ordinal_o n by move ->.
move: (Nintco_wor n) => [[or1 _] sr1].
apply: (order_exten or1 (ordinal_o_or n)).
have nN: natp n by apply /NatP. 
move => x y; apply: (iff_trans (Nintco_gleP nN x y)); split.
  move => [qa qb]; move: (proj33 qa) => qc.
  move/(NltP nN): (cle_ltT qa qb) =>  xn; move/(NltP nN): qb =>  yn.
  by apply/(ordo_leP).
move/(ordo_leP) =>[qa qb qc].
move/(NltP nN): qb =>  lyn; move/(NltP nN): qa =>  lxn.
split => //; move: (proj31_1 lxn)(proj31_1 lyn) => cx cy //.
Qed.



(** The eta order of Cantor *)



Definition Cantor_eta := order_type_of BQ_int01_order.

Lemma Cantor_eta_prop2 r: eta_like r -> order_type_of r = Cantor_eta.
Proof.
move => ra.
apply: order_type_unique; apply: (Cantor_eta_pr ra eta_likeQp_int01).
Qed.


Lemma Cantor_etaP r: order r ->
  (eta_like r <-> order_type_of r = Cantor_eta).
Proof.
move => or;split; first by apply:Cantor_eta_prop2.
move: eta_likeQp_int01 => [[pa _ pb pc pd] pe].
move => h;move: (OT_prop0 or) (OT_prop0 (proj1 pa)).
rewrite  -/Cantor_eta h => sa sb; move: (orderIT (orderIS sa) sb). 
move => [f [_ _ fp sincf]] {h sa sb}.
have csr: cardinal (substrate r) = aleph0.
    by rewrite - pe; apply /card_eqP; exists f. 
have ccsr:= (aleph0_countable csr).
move: fp => [bf sf tf]; move: (proj1 (proj1 bf)) => ff.
split => //; split => //.
+ split => // x y; rewrite - sf => xsr ysr. 
  move: (Vf_target ff xsr) (Vf_target ff ysr); rewrite tf => xa ya.
  case: (proj2 pa _ _ xa ya) => h.
     by left; move/(sincf x y xsr ysr): h.
     by right; move/(sincf y x ysr xsr): h.
+ move => x; rewrite - sf => xsr;  move: (Vf_target ff xsr); rewrite tf => xa.
  move:(pb (Vf f x) xa) => [z ylx].
  have: inc z (substrate  BQ_int01_order) by order_tac.
  rewrite - tf => zt; move: (bij_surj bf zt) => [y ysf yv]; exists y.
  move:ylx; rewrite yv; move => [ra rb]; split; last by dneg hh; rewrite hh.
  by apply /(sincf y x ysf xsr). 
+ move => x; rewrite - sf => xsr; move: (Vf_target ff xsr); rewrite tf => xa.
  move:(pc (Vf f x) xa) => [z ylx].
  have: inc z (substrate  BQ_int01_order) by order_tac.
  rewrite - tf => zt; move: (bij_surj bf zt) => [y ysf yv]; exists y.
  move:ylx; rewrite yv; move => [ra rb]; split; last by dneg hh; rewrite hh.
  by apply /(sincf x y xsr ysf). 
+ move => x y [lxy nxy]. 
  have: inc x (substrate r) by order_tac.
  have: inc y (substrate r) by order_tac.
  rewrite - sf => ysr xsr.
  move/(sincf x y xsr ysr): lxy => le1.
  have: glt  BQ_int01_order (Vf f x) (Vf f y).
     by split => //; move /(proj2 (proj1 bf) _ _ xsr ysr).
  move /pd => [u [[ua ub] [uc ud]]].
  have: inc u (substrate  BQ_int01_order) by order_tac.
  rewrite - tf => zt; move: (bij_surj bf zt) => [z zsr zv]; exists z.
  rewrite zv in ua ub uc ud. 
  split; split. 
  + by apply /(sincf _ _ xsr zsr).
  + clear ud;dneg hh; ue.
  + by apply /(sincf _ _ zsr ysr).
  + dneg hh; ue.
Qed.

Lemma Cantor_eta_pr1: order_type_of Nat_order <> Cantor_eta. 
Proof.
move:Nat_order_wor => [[or _] sr].
move/(Cantor_etaP or) => [[_ _ h _ _] _].
by rewrite sr in h; move:(h _ NS0) => [y [/Nat_order_leP[_ _ /cle0 h3]]].
Qed.


Lemma OT_eta_1 : order Cantor_eta.
Proof. apply:(OT_prop3 (proj1 BQ_int01_or_osr)). Qed.

Lemma Cantor_eta_pr2: Cantor_eta +t \1t <> Cantor_eta. 
Proof.
move:BQ_int01_or_osr => [or1 sr1].
move: (set1_wor emptyset) => [[or2 _] sr2].
move: (orsum2_osr or1 or2) => [pc pd].
rewrite (OT_sum2_pr2 or1 or2); move /(Cantor_etaP pc).
rewrite -/singleton_order.
move => [[qa qb _ qd _] _].
move: pd; rewrite sr2 sr1; set E := canonical_du2 _ _ => pd.
have xE: inc (J emptyset C1) E by apply:candu2_prb; fprops.
rewrite pd in qd; move: (qd _ xE) => [y [/orsum2_gleP [_ yE lxy]] nexy].
move /candu2P: yE => [ya yb].
move: lxy; aw; case; move => []; fprops => sa sb;case: yb; move => [sc sd] //.
by move/set1_P => /pr2_def h; case nexy; symmetry;apply: pair_exten; fprops; aw.
Qed.



Lemma orsum_total r g:
  orsum_ax r g -> total_order r ->
  (forall i, inc i (domain g) -> total_order (Vg g i)) ->
  total_order (order_sum r g).
Proof. 
move=> oa  [_ tor] alt; rewrite /total_order.
move: (oa) => [or sr alo]; aw; rewrite orsum_sr //.
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



Lemma orsum2_totalorder r r':
  total_order r -> total_order r' -> total_order (order_sum2 r r').
Proof.
move: cdo_wor => [ha hb].
have hc:= (worder_total ha).
have hd := proj1 ha.
move => pa pb; move:(pa)(pb) => [oa _][ob _];  apply: orsum_total => //.
   hnf; split => //; [ by aw | by hnf; aw => x xi; try_lvariant xi].
by hnf;aw => x xi; try_lvariant xi.
Qed.

Lemma Cantor_eta_pr3: \1t +t Cantor_eta <> Cantor_eta. 
Proof.
move:BQ_int01_or_osr => [or1 sr1].
move: (set1_wor emptyset) => [[or2 _] sr2].
move: (orsum2_osr or2 or1) => [pc pd].
rewrite (OT_sum2_pr2 or2 or1); move /(Cantor_etaP pc).
rewrite -/singleton_order.
move => [[_ _  qd _ _] _].
move: pd; rewrite sr2 sr1; set E := canonical_du2 _ _ => pd.
have xE: inc (J emptyset C0) E by apply:candu2_pra; fprops.
rewrite pd in qd; move: (qd _ xE) => [y [/orsum2_gleP [yE _ lxy]] nexy].
move /candu2P: yE => [ya yb].
move: lxy; aw; case; move => []; fprops => sa _ ;case: yb; move => [sc sd] //.
  by move/set1_P => /pr1_def h; case nexy;apply: pair_exten; fprops; aw.
by case: C0_ne_C1; rewrite - sa - sd.
Qed.




Lemma Cantor_eta_pr4: Cantor_eta  +t Cantor_eta = Cantor_eta.
Proof.
move:BQ_int01_or_osr => [or1 sr1].
move: eta_likeQp_int01  => [[pa _ pb pc pd] pe].
move: (orsum2_osr or1 or1) => [pf pg].
set r :=  BQ_int01_order.
set E := substrate (order_sum2 r r).
move: C1_ne_C0 => nT.
move: C0_ne_C1 => nT1.
have cE: cardinal E = aleph0.
  rewrite /E pg-[cardinal _]/(_ +c _) - csum2cr - csum2cl pe.
   apply:aleph0_pr2.
have ccE:= aleph0_countable cE.
rewrite (OT_sum2_pr2 or1 or1); apply /(Cantor_etaP pf); split => //.
split => //.
+ by apply: orsum2_totalorder.
+ rewrite pg;  move => x xsr; move:(xsr) => /candu2P [px] [] [p1x p2x].
    move:(pb _ p1x) => [y [yp yne]]; exists (J y C0); split; last first.
      by rewrite - px => /pr1_def.     
    apply/orsum2_gleP; split => //; last by constructor 1; aw.
    apply/candu2P; split; fprops; aw;left; split => //;order_tac.
  move:(pb _ p1x) => [y [yp yne]]; exists (J y C1); split; last first.
    by rewrite - px => /pr1_def.  
  apply/orsum2_gleP; split => //.
    apply/candu2P; split; fprops; aw; right; split => //;order_tac.
  constructor 2; aw; rewrite p2x;split =>  //.
+ rewrite pg;  move => x xsr; move:(xsr) => /candu2P [px] [] [p1x p2x].
    move:(pc _ p1x) => [y [yp yne]]; exists (J y C0); split; last first.
      by rewrite - px => /pr1_def.     
    apply/orsum2_gleP; split => //; last by constructor 1; aw.
    apply/candu2P; split; fprops; aw;left; split => //;order_tac.
  move:(pc _ p1x) => [y [yp yne]]; exists (J y C1); split; last first.
    by rewrite - px => /pr1_def. 
  apply/orsum2_gleP; split => //.
    apply/candu2P; split; fprops; aw; right; split => //;order_tac.
  constructor 2; aw; rewrite p2x;split =>  //.
+ move => x y [ /orsum2_gleP [xsr ysr lexy] nexy].
   move/candu2P:(xsr)=> [px xsr']; move /candu2P : (ysr) =>[py ysr'].
  case: lexy. 
    move => [x0 y0 lexy].  
    have: glt r (P x) (P y).
      by split => // spy; case: nexy; apply: pair_exten => //; rewrite x0 y0.
    move => /pd [z [[za zb] [zc zd]]]; exists (J z C0); split; split.
    - apply/orsum2_gleP; split => //; first by apply: candu2_pra; order_tac.
      by aw;  constructor 1. 
    - by rewrite - px => /pr1_def.
    - apply/orsum2_gleP; split => //; first by apply: candu2_pra; order_tac.
      by aw;  constructor 1. 
    - by rewrite - py => /pr1_def.
   move => [x0 y0 lexy].  
   have x1 : Q x = C1 by  case: xsr' => [][].
   have y1 : Q y = C1 by  case: ysr' => [][].
   have: glt r (P x) (P y).
      by split => // spy; case: nexy; apply: pair_exten => //; rewrite x1 y1.
    move => /pd [z [[za zb] [zc zd]]]; exists (J z C1); split; split.
    - apply/orsum2_gleP; split => //; first by apply: candu2_prb; order_tac.
      by aw;  constructor 2. 
    - by rewrite - px => /pr1_def.
    - apply/orsum2_gleP; split => //; first by apply: candu2_prb; order_tac.
      by aw;  constructor 2. 
    - by rewrite - py => /pr1_def.
move => [x0 y0].  
have y1 : Q y = C1 by  case: ysr' => [][].
have xsr2 : inc (P x) (substrate r) by case: xsr' => [][].
have ysr2 : inc (P y) (substrate r) by case: ysr' => [][].
move: (pc _ xsr2) => [z [za zb]]; exists (J z C0); split.
   split; last by rewrite -px => /pr1_def. 
   apply /orsum2_gleP; split => //; first by apply: candu2_pra; order_tac.
   constructor 1; aw; split => //.
rewrite - py y1;apply: orsum2_gle_spec => //; order_tac.
Qed.

Lemma Cantor_eta_pr5: Cantor_eta  +t \1t +t Cantor_eta = Cantor_eta.
Proof.
move:BQ_int01_or_osr => [or1 sr1].
move: eta_likeQp_int01  => [[pa _ pb pc pd] pe].
set r :=  BQ_int01_order.
move: singleton_order_or => or2.
move: (orsum2_osr or1 or2) => [or3 sr3].
move: (orsum2_osr or3 or1) => [or4].
set E := substrate _ => sr4. 
have cE: cardinal E = aleph0. 
  rewrite - aleph0_pr2 sr4 -[cardinal _]/(_ +c _) - csum2cr pe - csum2cl sr3.
  congr (_ +c aleph0).
  rewrite -[cardinal _]/(_ +c _) - csum2cr  - csum2cl  OT_cardinal_1 pe.
  by rewrite aleph0_plus1. 
rewrite {1} /OT_sum2 (OT_sum2_pr2 or1 or2).
rewrite - /(OT_sum2 _ _) (OT_sum2_pr2 or3 or1).
move: (set1_wor emptyset) => [wor2 sr2].
move: sr4; rewrite sr3; rewrite sr2;set T := (substrate r) => sr4.
set T1 := (substrate singleton_order).
have oneT: inc \2hq T. 
  have ra:= QSh2; move/ qlt0xP:QpsSh2 => hp.
  have rc: \2hq <q \1q. rewrite - BQdouble_half2; apply:(BQsum_Mps ra QpsSh2 ).
  by rewrite /T sr1; apply/Zo_P. 
move: C0_ne_C1 => nT.
move: C1_ne_C0 => nT1.
apply /(Cantor_etaP or4); split => //; split.
+ apply: orsum2_totalorder => //;  apply: orsum2_totalorder => //.
  exact: (worder_total wor2).
+ exact: (aleph0_countable cE).
+ rewrite -/E sr4; move => x xsr.
  move:(xsr); rewrite - sr2 - sr3 => xsr1.
  move:(xsr) => /candu2P [px []]; case => [p1x p2x].
    have aux2: inc (P x) (canonical_du2 T T1) by rewrite /T1 sr2.  
    move/candu2P: (p1x) => [ppx []]; case => [p3x p4x].
       move: (pb _ p3x) => [y [lxy nxy]]; exists (J (J y C0) C0). 
       split; last by rewrite - px - ppx => /pr1_def /pr1_def.
       have aux: inc (J y C0) (canonical_du2 T T1).
         apply: candu2_pra; rewrite /T;order_tac.
       apply/orsum2_gleP; split.
       - by apply: candu2_pra; rewrite sr3.
       - exact.
       - constructor 1; saw; apply/orsum2_gleP; split => //.
         by constructor 1; split => //; aw.
    exists (J (J \2hq C0) C0); split; last first.
      by rewrite - px - ppx p4x => /pr1_def /pr2_def.
    have aux: inc (J \2hq C0)  (canonical_du2 T T1) by apply: candu2_pra.
    apply/orsum2_gleP; split. 
    - by apply: candu2_pra; rewrite sr3. 
    - exact.
    - constructor 1; saw; apply/orsum2_gleP; split => //.
      by rewrite p4x;constructor 3; aw. 
  exists (J (J emptyset C1) C0). 
  rewrite -px p2x; apply: orsum2_gle_spec => //.
  rewrite sr3 sr2; apply:candu2_prb;fprops.
+ rewrite -/E sr4; move => x xsr.
  move:(xsr); rewrite - sr2 - sr3 => xsr1.
  move:(xsr) => /candu2P [px []]; case => [p1x p2x].
    exists (J \2hq C1); rewrite - px p2x; apply:  orsum2_gle_spec => //.
    by rewrite sr3 sr2.
  move: (pc _ p1x) => [y [lxy nxy]]; exists (J y C1); split; last first.
     by rewrite - px => /pr1_def.
  apply/orsum2_gleP; split => //; first by apply: candu2_prb; order_tac.
  constructor 2; aw; rewrite p2x; split => //.
+ move => x y [/orsum2_gleP [xsr ysr lexy] nexy].
  move /candu2P: (ysr) => [py ysr0].
  move /candu2P: (xsr) => [px xsr0].
  case: lexy.
  - move => [x0 y0 /orsum2_gleP [xsr1 ysr1]].
    move/candu2P:(xsr1) => [ppx qpx].
    move/candu2P:(ysr1) => [ppy qpy].
    case.
    * move => [px0 py0 le2]. 
      have:glt r (P (P x)) (P (P y)).
        by split =>// h; case:nexy;rewrite - px - py - ppx -ppy h px0 py0 x0 y0.
      move/pd => [z [[za zb] [zc zd]]]. 
      have aux0: inc (J z C0) (canonical_du2 T (substrate singleton_order)).
        apply: candu2_pra; rewrite /T; order_tac.
      have aux: inc (J (J z C0) C0)
        (canonical_du2 (substrate (order_sum2 r singleton_order)) T).
        by apply: candu2_pra; rewrite sr3. 
      exists (J (J z C0) C0); split; split.
      + apply/orsum2_gleP;split => //; constructor 1; aw; split => //.
        by apply/orsum2_gleP;split => //; constructor 1; aw.
      + by rewrite - px - ppx => /pr1_def /pr1_def.
      + apply/orsum2_gleP;split => //; constructor 1; aw; split => //.
        by apply/orsum2_gleP;split => //; constructor 1; aw.
      + by rewrite - py - ppy => /pr1_def /pr1_def.
    * move => [px0 py0 le2]. 
      move:qpy; case; move => [ha hb]; first by case: py0.
      move:qpx; case; move => [hc hd]; first by case: py0.
      case: nexy; apply: pair_exten => //; last by rewrite x0 y0.
      apply: pair_exten => //; last by rewrite hb hd.
      by move: ha hc; rewrite sr2 => /set1_P -> /set1_P ->.
    * move => [px0 py1]; case: qpy; move => [yp1 yp2]; first by case: py1.
      case: qpx; move => [xp1 xp2]; last by case:C0_ne_C1; rewrite -px0 - xp2.
      move: (pc _ xp1) => [z [za zb]].
      have aux0: inc (J z C0) (canonical_du2 T (substrate singleton_order)).
        apply: candu2_pra; rewrite /T; order_tac.
      have aux: inc (J (J z C0) C0)
        (canonical_du2 (substrate (order_sum2 r singleton_order)) T).
        by apply: candu2_pra; rewrite sr3. 
      exists (J (J z C0) C0); split; split.
      + apply/(orsum2_gleP); split => //; constructor 1; aw; split => //.
        apply/(orsum2_gleP); saw; constructor 1; split => //.
      + by rewrite - px - ppx => /pr1_def /pr1_def.
      + apply/(orsum2_gleP); split => //; constructor 1; saw.
        by apply/(orsum2_gleP); saw; constructor 3.
      + by rewrite - py - ppy => /pr1_def /pr2_def /nesym.
  - move => [x1 y1 le1].
    case: ysr0;move => [_ y0]; first by case y1. 
    case: xsr0;move => [_ x0]; first by case x1. 
    have: glt r (P x) (P y).
      by split => // exy; case: nexy; apply:pair_exten => //; rewrite x0 y0.
    move /pd => [z [[za zb] [zc zd]]]; exists (J z C1); split; split.
    * apply/orsum2_gleP; split => //; first by apply:candu2_prb; order_tac.
      by constructor 2; aw.
    * by rewrite - px => /pr1_def.
    * apply/orsum2_gleP; split => //; first by apply:candu2_prb; order_tac.
      by constructor 2; aw.
    + by rewrite - py => /pr1_def.
  - move => [x0 y1].
    case: ysr0 => [] [sa y0]; first by case: y1.
    case: xsr0=> [] [sb x1];last by case: nT; rewrite - x0 - x1.
    rewrite - px x0.
    move:(pb _ sa) => [z [za zb]]. 
    have zr: inc z (substrate r) by order_tac.
    exists (J z C1); split; first by apply: orsum2_gle_spec.
    split; last by rewrite - py => /pr1_def.
    apply/orsum2_gleP; split => //; first by apply: candu2_prb.
    constructor 2; aw; split => //.
Qed.


Lemma Cantor_eta_pr6: Cantor_eta  *t Cantor_eta = Cantor_eta.
Proof.
move:BQ_int01_or_osr => [or1 sr1].
move: eta_likeQp_int01  => [[pa _ pb pc pd] pe].
set r :=  BQ_int01_order.
have H:= (orprod2_gleP or1 or1).
move: (orprod2_osr or1 or1) => [pf pg].
set E := substrate (order_prod2 r r).
set T := (substrate r).
have cE: cardinal E = aleph0.
   have eq : T *c T = cardinal (product2 T T) by [].
   by rewrite /E pg -/T - eq - cprod2cr - cprod2cl pe aleph0_pr3.
have ccE:= aleph0_countable cE.
rewrite (OT_prod2_pr2 or1 or1); apply /(Cantor_etaP pf); split => //.
split => //.
+ by apply: orprod2_totalorder.
+ rewrite pg; move => x xsr;move:(xsr) => /setX2_P [fgx dx x0 x1].
    move:(pb _ x0) => [y yp]; exists (variantLc y (Vg x C1)); split.
      apply /H; split => //; last by right; aw.
      apply /setX2_P; split => //; aww; order_tac.
    by move => hg; case: (proj2 yp); rewrite - hg; aw.
+ rewrite pg; move => x xsr;move:(xsr) => /setX2_P [fgx dx x0 x1].
    move:(pc _ x0) => [y yp]; exists (variantLc y (Vg x C1)); split.
      apply /H; split => //; last by right; aw.
      apply /setX2_P; split => //; aww; order_tac.
    by move => hg; case: (proj2 yp);rewrite  hg; aw.
+ move => x y [/(orprod2_gleP or1 or1) [xsr ysr lxy] nxy].
  move:(xsr) => /setX2_P [fgx dx x0 x1].
  move:(ysr) => /setX2_P [fgy dy y0 y1].
  case lxy.
    move => [sc0 lec1].
    have: glt r (Vg x C1) (Vg y C1).
      split => //; dneg h1; apply: fgraph_exten => //; first by rewrite dx.
      by rewrite dx;move => u udx; try_lvariant udx.
    move /pd => [z [[za zb][za' zb']]]; set z1 := (variantLc (Vg x C0) z).
    have zz:inc z1 (product2 T T).
    apply /setX2_P; rewrite /z1 /T;split => //; aww;order_tac.
    have zc: Vg z1 C1 = z by rewrite /z1; aw.
    have zd: Vg z1 C0 = Vg x C0 by rewrite /z1; aw.
    exists z1; split; split.
    + by apply /H; split => //; left; rewrite zc zd.
    + by move => h;case: zb; rewrite - zc h.
    + by apply /H; split => //; left; rewrite zc zd. 
    + by move => h;case: zb'; rewrite - zc h.
  move/pd => [z [za zb]]; set z1 := (variantLc z (Vg x C1)).
  have zz:inc z1 (product2 T T).
    apply /setX2_P; rewrite /z1 /T;split => //; aww; order_tac.
  have zc: Vg z1 C0 = z by rewrite /z1; aw.
  exists z1; split; split.
  + by apply /H; split => //; right; rewrite zc.
  + by move => h;case: (proj2 za); rewrite - zc h.
  + by apply /H; split => //; right; rewrite zc.
  + by move => h;case: (proj2 zb); rewrite - zc h.
Qed.


Lemma Cantor_eta_pr7:  OT_opposite Cantor_eta = Cantor_eta.
Proof.
move:BQ_int01_or_osr => [or1 sr1].
move: eta_likeQp_int01  => [[pa _ pb pc pd] pe].
set r :=  BQ_int01_order.
move: (opp_osr (proj1 pa)) => [sa sb].
have cE: cardinal (substrate (opp_order r)) = aleph0 by ue.
have ccE:= aleph0_countable cE.
rewrite (OT_opposite3 (proj1 pa)); apply /(Cantor_etaP sa); split => //.
split => //.
+ by apply: total_order_opposite.
+ rewrite sb => x /pc [y lxy]; exists y; by apply/opp_gltP.  
+ rewrite sb => x /pb [y lxy]; exists y; by apply/opp_gltP.  
+ by move => x y /opp_gltP /pd [z [za zb]]; exists z; split; apply/opp_gltP.
Qed.

  

Lemma OT_le_not_order (r1 := Cantor_eta) (r2 :=  Cantor_eta +t \1t):
 [/\ r1 <=t r2, r2 <=t r1 & r1 <> r2].
Proof.
have ot1: order_type r1 by exact:(OT_prop1 (proj1 BQ_int01_or_osr)).
have ot2 := OT_1_order_type.
have p1:=(proj1  (OTsum_Mle0 ot1 ot2)).
have p3 := (nesym Cantor_eta_pr2).
split => //; rewrite /r1 - Cantor_eta_pr4; apply /(OTsum_Mle2 ot1).
apply:(OT_1_least_nz ot1) => /esym h.
move: set0_wor =>[[qa _] qb].
move:(Cantor_etaP qa); rewrite OT_set0 => p; move/p: h => /proj2.
by rewrite qb cardinal_set0 => res; apply: aleph0_nz.
Qed.

(* Infinite sums *)

(* ------------------- *)

Definition consec_list r f :=
  [/\ fgraph f, natp (domain  f), sub (range f) (substrate r)   &
      forall i, natp i -> csucc i <c (domain f) ->
        consecutive r (Vg f i) (Vg f (csucc i))].        
Definition consec_list_for  r f x :=
   consec_list r f /\  inc x (range f).
Definition consec_lists_for  r x :=
  Zo (fgraphs Nat (substrate r)) (fun f => consec_list_for r f x).
Definition consec_pow r x :=
   \csup(fun_image (consec_lists_for  r x) domain).


Lemma consec_pow_pr0 r f x:
  inc f (consec_lists_for  r x) <-> (consec_list_for r f x). 
Proof.
split; first by move/Zo_hi.
move => h; apply:Zo_i => //.
move:h =>[[ha hb hc hd] _]; apply/fgraphsP; split => //.
by move: (NS_inc_nat hb).                           
Qed.
           
Lemma consec_pow_pr1 r x f:
  inc f (consec_lists_for  r x) -> natp (domain f).
Proof.
by move => /Zo_hi /proj1 [].
Qed.


Lemma consec_pow_pr2 r f: order r -> consec_list r f ->
  (domain f) =c (range f).
Proof.
move => or [ha hb _ hc].
pose g := Lf (Vg f)  (domain f) (range f).
have <- : source g = domain f by rewrite /g;aw.
have <- : target g = range f by rewrite /g;aw.
have ax: lf_axiom (Vg f) (domain f) (range f).
  by move => x xdf; apply/(range_gP ha); ex_tac.
have rx y:inc y (range f) -> exists2 x, inc x (domain f) & y = Vg f x.
   by move/(range_gP ha).
have fm i j: i <c j -> j <c (domain f) -> glt r (Vg f i) (Vg f j).
  move => qa qb; move: (NS_lt_nat qb hb) => jN; move: j jN qa qb.
  apply: Nat_induction; first by  move/clt0.
  move => j jN Hrec lij ljd; move: (proj1 (hc j jN ljd)) => lt1.
  move/(cltSleP jN): lij; case/cle_eqVlt => cij; first by rewrite cij.
  exact (lt_lt_trans or (Hrec cij (cle_ltT (cleS jN) ljd)) lt1).
apply: card_bijection; apply: lf_bijective => // u v udx vdx df.
move/(NltP hb): udx => us; move/(NltP hb): vdx => vs.
case: (NleT_ell (NS_lt_nat us hb)(NS_lt_nat vs hb)) => // ll.
  by case:(proj2(fm _ _ ll vs)).
by case:(proj2(fm _ _ ll us)).
Qed.

Lemma consec_pow_pr3 r f: order r -> consec_list r f ->
   (domain f) <=cc (substrate r).
Proof.
move => ha hb; rewrite (consec_pow_pr2 ha hb).
move:(hb) =>[qa qb qc qd].
apply: sub_smaller => t /(range_gP qa) [x xdf ->]; apply: qc.
apply/(range_gP qa); ex_tac.
Qed.

Lemma consec_pow_pr4 n i : natp n -> i <c n ->
  consec_list_for (Nint_co n) (identity_g n) i.
Proof.
move => nN /(NltP nN)lin.
have ha:= (identity_fgraph n).
have hb:= (identity_d n).
split; last first.
 by apply/(range_gP ha); rewrite hb; ex_tac; rewrite identity_ev.
move: (Nintco_wor n) =>[[or _] sr].
split; rewrite ?hb => //.
  by rewrite sr (NintE nN) identity_r.
move => j jN ljn.
move: (cltS jN) => [qa qb].
have jn: inc j n. apply/(NltP nN); apply: (cle_ltT qa ljn).
have sjn: inc (csucc j) n by apply/(NltP nN).
split.
  rewrite (identity_ev jn) (identity_ev sjn).
  split; [ by apply /(Nintco_gleP nN) | exact ].
rewrite sr (NintE nN) => z zn [qc qd].
case: qc; case: qd; rewrite (identity_ev jn) (identity_ev sjn).
move=> /(Nintco_gleP nN) [ eqa _] eqb /(Nintco_gleP nN) [eqc _]; case. 
by apply: cleA => //;move/(cltSleP jN): (conj eqa eqb).
Qed.

Lemma consec_pow_pr5 n i : natp n -> i <c n ->
  consec_pow (Nint_co n) i = n.
Proof.
move => ha hb.
move: (consec_pow_pr4 ha hb) => H.
rewrite /consec_pow; set T := fun_image _ _.
move: (Nintco_wor n) =>[[or _] sr].
have hc: inc (identity_g n)  (consec_lists_for (Nint_co n) i).
  by apply/ consec_pow_pr0.
have hd t: inc t T -> t <=c n.
  move=> /funI_P [u /consec_pow_pr0 /proj1 ua ->].
  move: (consec_pow_pr3 or ua); rewrite sr (NintE ha).
  rewrite (card_card (CS_nat (proj42 ua))).
  by rewrite (card_card (CS_nat ha)).
apply: (cleA (card_ub_sup (CS_nat ha) hd)).
apply: card_sup_ub; first by move => t /hd/proj31.
by apply/funI_P; ex_tac; rewrite identity_d.
Qed.
  
  
Lemma consec_pow_pr6 r r' f g x
  (g' := Lg (domain g) (fun z => Vf f (Vg g z))):
  order_isomorphism f r r' ->
  consec_list_for r g x ->
  consec_list_for r' g'  (Vf f x). 
Proof.
move => iso [qa qb].
move:(order_isomorphism_sincr iso) => fsi.
move: iso => [or or' [fp sf tf] fm].
have ra:  fgraph g' by rewrite /g'; fprops.
have rb: domain g' = domain g by rewrite /g'; aw.
move: qa => [sa sb sc sd].
split; last first.
  move/(range_gP sa): qb =>[y ya ->].
  apply/(range_gP ra); rewrite rb; ex_tac; rewrite /g' LgV//.
have ff: function f by fct_tac.
have sc1 i: inc i (domain g) -> inc (Vg g i) (substrate r).
   move => h; apply: sc;apply/(range_gP sa); ex_tac.
split; [ done | ue | | ].
  move => t/(range_gP ra); rewrite rb; move => [yy ya ->].
  by rewrite /g' LgV//; Wtac; rewrite sf; apply: sc1. 
rewrite rb.
move => i iN lt; rewrite /g'.
have qa: inc (csucc i) (domain g) by  apply /NltP.
have qc: inc i (domain g). apply /(NltP sb); exact: (cle_ltT (cleS iN) lt).
move: (sd i iN lt) =>[rc rd].
rewrite !LgV//;split; first by apply: fsi.
move => z zs [z1 z2].
have ztf: inc z (target f) by ue.
move: (proj2 (proj2 fp) z ztf) => [t ta tb].
move: z1 z2; rewrite tb ;move =>[z1 z2][z3 z4].
have x2s: inc (Vg g (csucc i)) (source f) by rewrite sf; apply: sc1. 
have x1s: inc (Vg g i) (source f) by rewrite sf; apply: sc1; apply: qc.
have tsr: inc t (substrate r) by ue.
case (rd t tsr); split; split.
- by move/(fm (Vg g i)  t x1s ta): z1.
- by move => h; case: z2; rewrite h.
- by  move/(fm t (Vg g (csucc i)) ta x2s): z3.
- by move => h; case: z4; rewrite h.
Qed.


Lemma consec_pow_pr7 r r' f x:
  order_isomorphism f r r' -> inc x (substrate r) ->
  consec_pow r x = consec_pow r' (Vf f x).
Proof.
move => ha hb.
rewrite/consec_pow.
set T := consec_lists_for _ _. 
set T' := consec_lists_for _ _. 
congr union; set_extens k => /funI_P[t tT ->];apply /funI_P.
  move/consec_pow_pr0: tT => h.
  move: (consec_pow_pr6 ha h); set g := Lg _ _  => h'.
  by exists g; [ by apply /consec_pow_pr0  | rewrite /g; aw ].
move:(inverse_order_is ha) => hc.
move/consec_pow_pr0: tT => h.
move: (consec_pow_pr6 hc h); set g := Lg _ _. 
move: ha => [_ _ [bf sf _] _].
have xsf: inc x (source f) by ue.
rewrite (inverse_V2 bf xsf) => h'a.
by exists g; [ by apply /consec_pow_pr0  | rewrite /g; aw ].
Qed.


Lemma consec_pow_pr8 r x (E := substrate r) : total_order r -> finite_set E -> 
  inc x E ->  consec_pow r x  = cardinal E.
Proof.
move => ha hb hc.
move: (finite_ordered_interval1 ha hb) => [f /proj1].
move/card_finite_setP:hb.
rewrite -/E; set n := cardinal _ => nN is1.
rewrite (consec_pow_pr7 is1 hc) (consec_pow_pr5 nN) //.
apply/(NltP nN); rewrite - (NintE nN) -(proj2 (Nintco_wor n)).
move:(is1) => [_ _ [[[ff _] _] sf <-] _]; Wtac; ue.
Qed.


Lemma consec_pow_pr9 r (E := substrate r) : order r ->  finite_set E -> 
  (exists2 x, inc x E &  consec_pow r x  = cardinal E) ->
  total_order r.
Proof.
move => or fse [x xE ].
rewrite /consec_pow; set T := fun_image _ _  => h.
move/card_finite_setP: (fse); set n := cardinal E => nN.
have hd t: inc t T -> t <=c n.
  move=> /funI_P [u /consec_pow_pr0 /proj1 ua ->].
  move: (consec_pow_pr3 or ua).
  by rewrite (card_card (CS_nat (proj42 ua))).
case:(all_exists_dichot1 (fun z => z <c n) T) => hyp.
   case: (equal_or_not  n \0c) => ez.
     move: (card_nonempty ez) => Ez.
     by split => //u v; rewrite -/E Ez => /in_set0.
   move: (cpred_pr nN ez); set p:= cpred n; move => [pN pv].
   have he t: inc t T -> t <=c p.
     by move => tT; apply/(cltSleP pN); rewrite - pv; apply: hyp.
   move: (card_ub_sup (CS_nat pN) he); rewrite h -/n => /cleNgt; case.
   by move: (cltS pN); rewrite pv.
move: hyp => [m ma mb].
have: inc n T.
  case: (equal_or_not m n); first  by move <-. 
  by move => h1;case: mb; split => //; apply: hd.
move/funI_P =>[f /consec_pow_pr0/proj1 qa qb].
move: (qa) =>[ha hb hc he]; rewrite - qb in he.
have fm i j: i <c j -> j <c n -> glt r (Vg f i) (Vg f j).
  move => lij jd; move: (NS_lt_nat jd nN) => jN; move: j jN lij jd.
  apply: Nat_induction; first by  move/clt0.
  move => j jN Hrec lij ljd; move: (proj1 (he j jN ljd)) => lt1.
  move/(cltSleP jN): lij; case/cle_eqVlt => cij; first by rewrite cij.
  exact (lt_lt_trans or (Hrec cij (cle_ltT (cleS jN) ljd)) lt1).
have ww: range f =c E.
  by rewrite - (consec_pow_pr2 or qa) - qb  /n double_cardinal.
move:(strict_sub_smaller_contra fse hc ww) => rf.
split => // u v ; rewrite - /E - rf; move => uu; move: uu (uu).
move => /(range_gP ha) [i idf ->] uu /(range_gP ha) [j jdf ->].
move: idf jdf; rewrite - qb; move/(NltP nN) => lin; move/(NltP nN) => ljn.
case: (cleT_ell (proj31_1 lin)(proj31_1 ljn)) => cp.
- by rewrite - cp; left; order_tac; apply: hc.
- left; exact: (proj1 (fm i j cp ljn)).
- right; exact: (proj1 (fm j i cp lin)).
Qed.
  
Definition sier_inf_sum sigma :=
  OT_sum Nat_order
      (Lg Nat (fun z => (OT_of_nat (csucc (Vf sigma z))) *t Cantor_eta)). 

Definition sier_inf_sum_aux sigma z :=
  (order_prod2  (ordinal_o (csucc (Vf sigma z))) BQ_order).

Lemma  sier_inf_sum_prop sigma: 
  sier_inf_sum sigma =
  order_type_of (order_sum Nat_order (Lg Nat (sier_inf_sum_aux sigma))).
Proof.
move: Nat_order_wor => [[or1 _] sr1].
rewrite /sier_inf_sum.
set f := Lg Nat _.
have  -> : f  =
 Lg (substrate Nat_order) 
    (fun i => order_type_of (Vg (Lg Nat (sier_inf_sum_aux sigma))  i)).
  rewrite sr1; apply: Lg_exten => n nn.
   rewrite LgV// /sier_inf_sum_aux.
  rewrite - (Cantor_eta_prop2 eta_likeQ).
  by rewrite  (OT_prod2_pr2 (ordinal_o_or _) BQor_or).
have  aux: order_fam (Lg Nat (sier_inf_sum_aux sigma)).
  hnf; aw => t tN; rewrite LgV//; apply: (orprod2_or  _ BQor_or).
   apply: ordinal_o_or.
by rewrite  (OT_sum_invariant3 or1); aw.
Qed.  


Definition IFS_sub_pow_gen r x :=
  fun_image (Zo (substrate r) (fun z => gle r z x)) (consec_pow r).

Lemma sub_pow_pr0 r r' f  x:
  order_isomorphism f r r' -> inc x (substrate r) ->
  IFS_sub_pow_gen r x = IFS_sub_pow_gen r' (Vf f x). 
Proof.
move => fis xsr.
rewrite /IFS_sub_pow_gen.
set A  := Zo _ _; set B  := Zo _ _.
move: (fis) => [or1 or2 [bf sf tf] fm].
have ff: function f by fct_tac.
set_extens t.
  move=> /funI_P [z /Zo_P[zsr zle]  ->].
  rewrite (consec_pow_pr7 fis zsr). 
  move: zsr xsr; rewrite - sf => zs xs.
  move/(fm z x zs xs): zle => fzle.
  apply/funI_P; exists (Vf f z) => //.
  apply:Zo_i => //; order_tac.
move => /funI_P [z /Zo_P [za zb] ->].
rewrite - tf in za.
move: (proj2 (proj2 bf) _ za) =>[y ya yb].
move: zb; rewrite yb => le1.
rewrite sf in ya; rewrite - (consec_pow_pr7 fis ya).
apply/funI_P; exists y => //; apply:(Zo_i ya).
apply/fm => //; ue.
Qed.



Section InfSumStudy.
Variables (sigma: Set).
Hypothesis sp: inc sigma (permutations Nat).
Definition IFS_good_pair z := (Q z) <=c Vf sigma (P z). 
Definition IFSE :=
  Zo ((Nat\times Nat) \times BQ) (fun z => IFS_good_pair (P z)).
Definition IFS_order_rel x y:=
  [\/ P (P x) <c P (P y),
    P (P x) = P (P y) /\ Q x <q Q y |
    [/\ P (P x) = P (P y),  Q x = Q y &  Q (P x) <c Q (P y)]].
Definition IFS_order_rel1 x y:= x = y \/ IFS_order_rel x y.
Definition IFS_order := graph_on IFS_order_rel1  IFSE.


Lemma IFE_osr : order_on IFS_order IFSE.
Proof.
have Ha a: inc a  IFSE -> IFS_order_rel1 a a by  move => _; left.
move: (graph_on_sr Ha); rewrite  -/IFS_order => se.
split => //.
apply:order_from_rel; split.
- move => b a c qa qb.
  case: (qa); [ by move -> | move => qa' ].
  case: qb; [by move <- | case => qb; case: qa' => qc].
  - right; constructor 1; apply: (clt_ltT qc qb).
  - by right; constructor 1; rewrite (proj1 qc).
  - by right; constructor 1; rewrite (proj31 qc).
  - by right; constructor 1; rewrite - (proj1 qb).
  - right; constructor 2; move: qc qb => [-> ra] [-> rb]; split => //.
    by apply: (qlt_ltT ra rb).
  - by right; constructor 2; move: qc qb => [-> -> rb] [-> rc].
  - by  right; constructor 1; rewrite - (proj31 qb).
  - by right; constructor 2; move: qc qb => [-> ra] [->  <- rc].
  - right; constructor 3; move: qc qb => [-> -> ra] [->  <- rc].
    by split => //; apply: (clt_ltT ra rc).
- move => a b.
  case => // qa; case => // qb.
  case: qa; case: qb => qa qb.
  - by move:(cleNgt (proj1 qa) qb).
  - case: (proj2 qb); exact: (esym (proj1 qa)).
  - case: (proj2 qb); exact: (esym (proj31 qa)).
  - case: (proj2 qa); exact: (esym (proj1 qb)).
  - case:(qleNgt (proj1 (proj2 qa)) (proj2 qb)).
  - case: (proj2 (proj2 qb)); exact: (esym (proj32 qa)).
  - case: (proj2 qa); exact: (esym (proj31 qb)).
  - case: (proj2 (proj2 qa)); exact: (esym (proj32 qb)).
  - case: (cleNgt (proj1 (proj33 qa)) (proj33 qb)).
by move => a b _; split; left.
Qed.


Lemma IFE_gltP  x y: glt IFS_order x y <-> 
  [/\ inc x IFSE, inc y IFSE & IFS_order_rel x y].
Proof.
split.
  by move => [/graph_on_P1 [xe ye ha] hb]; case: ha.
move => [ha hb hc]; split.
  by apply/graph_on_P1; split => //; right.
move => xy; case: hc; rewrite xy.
- by move => /proj2; case.
- by move => [_ /proj2].
- by move => [_ _ /proj2].
Qed.

  
Lemma IFE_gleP  x y: gle IFS_order x y <->
  [/\ inc x IFSE, inc y IFSE &
   [\/ P (P x) <c P (P y),
    P (P x) = P (P y) /\ Q x <q Q y |
    [/\ P (P x) = P (P y),  Q x = Q y &  Q (P x) <=c Q (P y)]]].
Proof.
split.
  move => /graph_on_P1 [xe ye h]; split => //.
  case: h.
    move ->; constructor 3; split => //; apply: cleR.
    by move/Zo_S: ye => /setX_P [_ /setX_P [_ _ /CS_nat rc] _].
  case. 
    by constructor 1.
    by constructor 2.
   by move =>[ra rb /proj1 rc]; constructor 3.
move =>[xe ye h]; apply/graph_on_P1; split => //.
case: (equal_or_not x y ) => eab; [ by left | right].
case: h.
- by constructor 1.
- by constructor 2.
- move => [sa sb sc]; constructor 3; split => //; split => // eq.
  move/Zo_S: xe => /setX_P [ra /setX_P [rb rc rd] re]. 
  move/Zo_S: ye => /setX_P [ra' /setX_P [rb' rc' rd'] re']. 
  by case: eab; apply: pair_exten => //; apply: pair_exten.
Qed.

Lemma IFE_tor : total_order IFS_order.
Proof.
move: IFE_osr => [or sr ]; split => //.
rewrite sr =>  x y xE yE.
move/Zo_S: (xE) => /setX_P [ra /setX_P [rb rc rd] re]. 
move/Zo_S: (yE) => /setX_P [ra' /setX_P [rb' rc' rd'] re'].
case: (NleT_ell rc rc').
  move => eq1; case: (qleT_ell re re').
     move => eq2; case: (NleT_ee rd rd') => ll.
     by left; apply/IFE_gleP; split => //; constructor 3.
     by right; apply/IFE_gleP; split => //; constructor 3.
  by left; apply/IFE_gleP; split => //; constructor 2.
  by right; apply/IFE_gleP; split => //; constructor 2.
by left;apply/IFE_gleP; split => //; constructor 1.
by right ;apply/IFE_gleP; split => //; constructor 1.
Qed.

Lemma OT_of_E: order_type_of IFS_order  = sier_inf_sum sigma.
Proof.
rewrite sier_inf_sum_prop.
apply: order_type_unique.
move: IFE_osr => [or1 sr1].
move: Nat_order_wor => [[or2 _] sr2].
have or5 := BQor_or.
set g1 := Lg Nat (sier_inf_sum_aux sigma).
have  aux: order_fam (Lg Nat (sier_inf_sum_aux sigma)).
  hnf; aw => t tN; rewrite LgV//; apply: (orprod2_or  _ BQor_or).
   apply: ordinal_o_or.
have ax: orsum_ax Nat_order g1.
  rewrite /g1; saw; hnf;aw => y yN; rewrite LgB//.
move:(orsum_osr ax) =>[or3 sr3].
set F := sum_of_substrates g1. 
pose h x := J (variantLc (Q x) (Q (P x)) )  (P (P x)).
have axs n: natp n ->  natp (Vf sigma n).
  move /permutationsP: sp => [[[ff _] _] sf tf] sn.
  rewrite /natp; Wtac; ue.  
have vs x: inc x IFSE ->
  inc (variantLc (Q x) (Q (P x)))
   (substrate (sier_inf_sum_aux sigma (P (P x)))).
  move/Zo_P => [/setX_P [ra /setX_P [rb rc rd] re] rf]. 
  have Ha: order (ordinal_o (csucc (Vf sigma (P (P x))))).
    by apply: ordinal_o_or. 
  rewrite /sier_inf_sum_aux.  
  rewrite (orprod2_sr Ha BQor_or) BQor_sr ordinal_o_sr.
  apply/setX2_P; aw; split => //; fprops.
  by apply/(NleP (axs _ rc)).
have ax2 x: inc x IFSE -> inc (h x) F. 
  move => xx; move: (vs _ xx) => ra.
  move/Zo_P: xx => [/setX_P [_ /setX_P [_ rc rd] re] _]. 
  by apply: disjoint_union_pi1; rewrite /g1; aw; bw.
have hbp:bijection_prop (Lf h IFSE F) IFSE (sum_of_substrates g1).
  saw; apply : lf_bijective.
  - done.
  - move => x y.
    move/Zo_P => [/setX_P [ra /setX_P [rb rc rd] re] rf]. 
    move/Zo_P => [/setX_P [sa /setX_P [sb sc sd] se] sf]. 
    move/pr12_def => [eq1 eq2].
    move: (f_equal (Vg ^~ C0) eq1) (f_equal (Vg ^~ C1) eq1); aw => eq3 eq4.
    by apply: pair_exten => //; apply: pair_exten.
  - move => y /du_index_pr1 [ea eb ec].
    have oo : order (ordinal_o (csucc (Vf sigma (Q y)))) by apply: ordinal_o_or.
    move: ea; rewrite /g1; aw => ea.
    move: eb; rewrite /g1/sier_inf_sum_aux; rewrite LgV// orprod2_sr //.
    rewrite BQor_sr ordinal_o_sr; move/setX2_P =>[qa qb qc  qd].
    move: (axs _ ea) => sn.
    move/(NleP sn): qd => le1.
    move: (NS_le_nat le1 sn) => rn.
    exists (J (J (Q y) (Vg (P y) C1)) (Vg (P y) C0)).
      apply: Zo_i.
        by apply: setXp_i => //; apply: setXp_i.
      by rewrite /IFS_good_pair; aw.
    rewrite /h; aw; rewrite -{1} ec; congr J.
    apply: fgraph_exten; aww.
    by rewrite qb  => t; case /set2_P => ->; aw. 
exists (Lf h IFSE F); split => //.
  by rewrite sr1 sr3.
hnf; aw => x y xE yE; rewrite ! LfV//.
apply: (iff_trans (IFE_gleP x y)).
apply: iff_trans  (iff_sym (orsum_gleP Nat_order g1 (h x) (h y))).
have ha: inc (h x) (sum_of_substrates g1) by apply: ax2.
have hb: inc (h y) (sum_of_substrates g1) by apply: ax2.
move/Zo_P:(xE) => [/setX_P [ra /setX_P [rb rc rd] re] rf].
move/Zo_P:(yE) => [/setX_P [sa /setX_P [sb sc sd] se] sf].
have  or4: order (ordinal_o (csucc (Vf sigma (P (P x))))).
  by apply: ordinal_o_or.
have or6: order (ordinal_o (csucc (Vf sigma (P (P y))))).
   by apply: ordinal_o_or.
move: (vs _ xE) (vs _ yE); rewrite /sier_inf_sum_aux.
rewrite (orprod2_sr or4 or5) (orprod2_sr or6 or5) => Vx  Vy.
split; move => [_ _ hc]; split => //.
  hnf; rewrite /h; aw; case: hc.
  - move =>[la lb]; left; split => //; apply /Nat_order_leP.
    split => //.
  - move =>[la lb]; right; split => //.
    rewrite /g1/sier_inf_sum_aux LgV//.
    apply /(orprod2_gleP or4 or5); aw.
    split; [ done |  by rewrite la |  by right; apply /BQlt_P].
  - move =>[la lb lc]; right; split => //.
    rewrite /g1/sier_inf_sum_aux LgV//.
    apply /(orprod2_gleP or4 or5); aw.
    split => //; first by rewrite la.
    left; split => //; apply/ordo_leP.
    move: (axs _ sc) => xx.
    move/(NleP xx) : (cleT lc sf) => rr2.
    move/(NleP xx) : sf => rr1.
    rewrite la; split => //; exact: (proj33 lc).
case: hc.
  move => [/Nat_order_leP [_ _ ]]; rewrite /h; aw => ma mb.
  by  constructor 1.
rewrite /h; aw.
move => [a]; rewrite /g1/sier_inf_sum_aux LgV//.
move /(orprod2_gleP or4 or5); move =>[ _ _]; aw; case.
  move =>[lb /ordo_leP [lc ld le]].
  constructor 3; split => //.
  move: (axs _ rc) => sn.
  move/(NleP sn):lc => /proj31 ca.
  move/(NleP sn):ld => /proj31 cb.
  by  split.
by move/BQlt_P => lc; constructor 2.
Qed.
  
  

Lemma IFE_consecP x y :
  inc x IFSE -> inc y IFSE ->
  ((consecutive IFS_order x y) <->
  [/\ P (P x) = P (P y), Q x = Q y & csucc (Q (P x)) = Q (P y)]).
Proof.
move =>xE yE.
move/Zo_P: (xE) => [/setX_P [ra /setX_P [rb rc rd] re] rf]. 
move/Zo_P: (yE) => [/setX_P [ra' /setX_P [rb' rc' rd'] re'] rf'].
split.
  set a := (P (P x)); set b := (Q (P x)); set c := Q x.
  move => [/IFE_gltP qa qb].
  case: (proj33 qa).
  + move => lt0.   
    move: (qlt_succ re) => la.
    move: (proj32_1 la) => ccq.
    set z := J (J a b) (c +q \1q).
    have zE: inc z IFSE.
      apply/Zo_P; split; first by apply: setXp_i => //; apply: setXp_i.
      by rewrite /z; aw; rewrite  rb.
    have zs: inc z (substrate IFS_order) by rewrite (proj2 (IFE_osr)).
    have lt3: glt IFS_order x z.
      by apply/IFE_gltP; split => //; constructor 2; rewrite /z;split; aw.
    have lt4: glt IFS_order z y.
      by apply/IFE_gltP; split => //; constructor 1; rewrite /z; aw.
    by case: (qb z zs).
   + move => [eq1 lt1].
     move: (BQmiddle_comp  lt1) => [lt2 lt3].
     move: (proj31_1 lt3) => cc.
     set z := J (J a b) (BQmiddle (Q x) (Q y)).
     have zE: inc z IFSE.
      apply/Zo_P; split; first by apply: setXp_i => //; apply: setXp_i.
      by rewrite /z; aw; rewrite  rb.
    have zs: inc z (substrate IFS_order) by rewrite (proj2 (IFE_osr)).
    have lt4: glt IFS_order x z.
      apply/IFE_gltP; split => //; constructor 2; rewrite /z;saw.
    have lt5: glt IFS_order z y.
      apply/IFE_gltP; split => //; constructor 2; rewrite /z;saw.
    by case: (qb z zs).
   + move => [eq1 eq2 lt1]; split => //.
     move /(cleSltP rd): (lt1). case/cle_eqVlt => // lt2.
     set z := J (J a (csucc b)) c.
     move:(NS_succ rd) => cc.
     have zE: inc z IFSE.
      apply/Zo_P; split; first by apply: setXp_i => //; apply: setXp_i.
      rewrite /IFS_good_pair; rewrite /z; aw.
      by move: (proj1 (clt_leT lt2 rf')); rewrite - eq1. 
    have zs: inc z (substrate IFS_order) by rewrite (proj2 (IFE_osr)).
    have lt4: glt IFS_order x z.
      apply/IFE_gltP; split => //; constructor 3; rewrite /z;saw.
      by apply: cltS.
    have lt5: glt IFS_order z y.
      apply/IFE_gltP; split => //; constructor 3; rewrite /z;saw.
    by case: (qb z zs).   
move => [ha hb hc]; split.
  apply /IFE_gltP; split => //; constructor 3; split => //.
  by rewrite - hc; apply: cltS.
move => z; rewrite (proj2 (IFE_osr)) => zE [za zb].
move/IFE_gltP: za => /proj33 zc; move/IFE_gltP: zb => /proj33 zd.
case: zc; case: zd.
- by rewrite - ha => /proj1 aa/cltNge; case.
- by move => [-> _]; rewrite ha; case.
- by move => [-> _] _; rewrite ha; case.
- by rewrite ha; move => [_ qa][qb _]; case:  qa.
- by rewrite hb; move => [_ qa][_] /proj1/ qleNgt; case.
- by rewrite hb; move => [_ -> _] [_ /proj2]; case.
- by rewrite ha; move => /proj2 bb /proj31 eq; case:bb.
- by rewrite hb; move => [_ /proj2 bb] /proj32 eq; case: bb.
- by rewrite - hc; move  => /proj33 /(cltSleP rd) la /proj33 /cltNge; case.
Qed.

Definition IFS_pow x := (csucc (Vf sigma (P (P x)))).
Definition IFS_chain x :=
  Lg (IFS_pow x) (fun i => J (J (P (P x)) i) (Q x)).

Lemma IFE_consec_chain x : inc x IFSE ->
  consec_list_for IFS_order (IFS_chain x) x.
Proof.
move => xE.
set m := csucc (Vf sigma (P (P x))).
move/Zo_P: (xE) => [/setX_P [ra /setX_P [rb rc rd] re] rf]. 
have fgf: fgraph (IFS_chain x). by rewrite/IFS_chain; fprops.
have df: (domain (IFS_chain x)) =  m by rewrite /IFS_chain; aw.
move/permutationsP: sp =>[bs ss ts]; move: (proj1 (proj1 bs)) => fs.
have Sn1: natp (Vf sigma (P (P x))) by  rewrite /natp; Wtac.
have Sn: natp m by  apply: NS_succ.
split; last first.
  have hu: inc (Q (P x)) m by apply/NleP. 
  apply/(range_gP fgf); rewrite df; exists (Q (P x)) => //.
  by rewrite/IFS_chain LgV// rb ra.
have sr := (proj2 (IFE_osr)).
have H i: i <c m -> inc (Vg (IFS_chain x) i) IFSE.
  move => lt1.
  move: (NS_lt_nat lt1 Sn) => iN.
  move/(NltP  Sn): (lt1) => yb.
  rewrite /IFS_chain LgV//; apply/Zo_P; split.
    by apply: setXp_i => //; apply: setXp_i.
  by rewrite/IFS_good_pair; aw; apply/NleP.
split.
- done.
- by rewrite /IFS_chain; aw.
- move => t /(range_gP fgf) [y ya ->];  rewrite df in ya.
  by rewrite sr; move/(NltP  Sn): (ya) => /H  yb.
move => i iN; rewrite df => lt1.
move: (H _ lt1) => siE.
have  lt0 := (cle_ltT (cleS iN) lt1).
move: (H _ lt0) => iE.
have lt2: inc (csucc i) m by apply NltP.
have lt3: inc i m by apply NltP.
by  apply/(IFE_consecP iE siE); rewrite /IFS_chain ! LgV//; aw.
Qed.


Lemma IFE_consec_chain1 f: 
  consec_list IFS_order  f ->
  exists2 x, inc x IFSE &
   forall i, inc i (domain f)-> Vg f i = J (J (P (P x)) (Q (P x) +c i)) (Q x).
Proof.
move => [qa qb qc qd].
case: (equal_or_not (domain f) \0c) => nz.
  move/permutationsP: sp =>[bs ss ts]; move: (proj1 (proj1 bs)) => fs.
  have iot: inc \1c (target sigma) by rewrite ts; apply: NS1.
  move: (inverse_V bs  iot); set u := (Vf (inverse_fun _) _) => fu.
  exists (J (J u \0c) \0q); last by  rewrite nz => t /in_set0.
  have qs0 := QS0; have ns0 := NS0.
  have uN: inc u Nat by  rewrite - ss; exact: (inverse_Vis bs iot).
  apply/Zo_P; split.
    by apply: setXp_i => //; apply: setXp_i.
  rewrite /IFS_good_pair; aw; rewrite fu; apply: cle_01.
have ze: inc \0c (domain f).
  by apply/(NltP qb); apply: card_ne0_pos => //; apply: CS_nat.
have sr := (proj2 (IFE_osr)).
set x := Vg f \0c.
have xr: inc x (range f) by  apply/(range_gP qa); ex_tac.
have xsE: inc x IFSE by  rewrite - sr; apply: qc.
move /Zo_P: (xsE) => [/setX_P [px /setX_P [ppx ppn qpn] qpq] gpx].
ex_tac.
move => i idf; move:(NS_inc_nat qb idf) => iN.
move: i iN idf; apply: Nat_induction.
  by rewrite (csum0r (CS_nat qpn)) ppx px.
move => n nN Hrec snd. 
have fsnE: inc (Vg f (csucc n))  IFSE.
  rewrite - sr; apply: qc; apply/(range_gP qa); ex_tac.
move/(NltP qb): snd => lt1.
move:(cle_ltT (cleS nN) lt1) => lt2.
move/(NltP qb): lt2 => nd.
have fnE: inc (Vg f n)  IFSE.
  rewrite - sr; apply: qc; apply/(range_gP qa); ex_tac.
move: (qd n nN lt1).
move/(IFE_consecP fnE fsnE); rewrite (Hrec nd); aw; move => [ea eb ec].
move /Zo_P: (fsnE) => [/setX_P [pv /setX_P [ppv _ _] _] _].
by rewrite - pv - ppv - ec - ea - eb (csum_nS _ nN).
Qed.

Lemma IFE_consec_chain2 x : inc x IFSE ->
  exists2 f, inc f (consec_lists_for IFS_order x) &
         domain f = IFS_pow x.
Proof.
move => xE.
move: (IFE_consec_chain xE) => hyp.
exists (IFS_chain x); first  by apply/consec_pow_pr0.
by rewrite /IFS_chain; aw.
Qed.

Lemma IFE_consec_chain3 f x : inc x IFSE ->
  inc f (consec_lists_for IFS_order x)  ->
  domain f <=c IFS_pow x.
Proof.
move => xE /consec_pow_pr0 [hf1 xrf].
move: (IFE_consec_chain1 hf1) =>[y yE fp].
move: hf1 =>[qa qb qc qd].
move/(range_gP qa):xrf =>[n ndf  ->]; rewrite  (fp _ ndf); aw.
move /Zo_P:yE => [/setX_P [px /setX_P [ppx ppn qpn] qpq]  gy].
case: (equal_or_not (domain f) \0c).
  by move ->; apply: cle0x; apply:CS_succ.
move => dp.
move: (cpred_pr qb  dp); set s := cpred _; move =>[sa sb].
have sdf: inc s (domain f) by rewrite sb; apply: Nsucc_i.
have fe: inc (Vg f s) IFSE.
  rewrite - (proj2 (IFE_osr)); apply: qc; apply/(range_gP qa); ex_tac.
move/Zo_P:fe => [/setX_P [pxs /setX_P [pps ppns qpns] qpqs]].
rewrite /IFS_good_pair; rewrite (fp _ sdf); aw => eqa.
move: (cleT (csum_Mle0 (Q (P y)) (CS_nat sa)) eqa).
by rewrite /IFS_pow; aw; move/cleSS; rewrite sb.
Qed.

Lemma IFE_consec_chain4 x : inc x IFSE ->
  consec_pow IFS_order x = IFS_pow x.
Proof.
move => xE.
have lt1: IFS_pow x <=c consec_pow IFS_order x.
  apply: card_sup_ub.
   by move => t /funI_P [a /consec_pow_pr0 /proj1/proj42/CS_nat aa ->].
   by apply/funI_P; move: (IFE_consec_chain2 xE) =>[f qa qb]; ex_tac.
apply: (cleA _ lt1).
apply: (card_ub_sup (proj31 lt1)).
move => i /funI_P [f ff ->].
by apply:IFE_consec_chain3.
Qed.

Definition IFS_sub_pow x :=
  fun_image (Zo IFSE (fun z => gle IFS_order z x)) (consec_pow IFS_order).

Lemma sub_pow_pr1 x:
   IFS_sub_pow x = IFS_sub_pow_gen IFS_order x.
Proof. 
by rewrite/ IFS_sub_pow  /IFS_sub_pow_gen (proj2 IFE_osr).
Qed.

  
Lemma IFS_sub_pow_prop0 x : inc x IFSE ->
   IFS_sub_pow x = fun_image (csucc (P (P x))) (fun z => csucc (Vf sigma z)). 
Proof.
move => xE.
move/Zo_P:(xE) => [/setX_P [px /setX_P [ppx ppn qpn] qpq] gp].
set_extens t.
  move/funI_P => [z /Zo_P[zE lzx] -> ].
  rewrite (IFE_consec_chain4 zE); apply/funI_P.
  have h: P (P x) <=c P (P x) by apply: (cleR (CS_nat ppn)).
  have la: P (P z) <=c P (P x). 
    move/IFE_gleP: lzx  => /proj33;case.
    - by case.
    - by move => [ -> _].
    - by move => [ -> _ _].
  by exists (P (P z)) => //; apply/(NleP ppn).
move/funI_P =>[m /(NleP ppn) mle -> ]; apply/funI_P.
case /cle_eqVlt: mle => mle.
  rewrite mle;  exists x.
   move: IFE_osr =>[or sr].
     by apply:Zo_i => //; order_tac; rewrite sr.
  by rewrite (IFE_consec_chain4 xE).
set z := J (J m \0c) \0q.
have mN: natp m by  apply: (NS_lt_nat mle ppn).
have zE: inc z IFSE.
  apply: Zo_i.
    by move: NS0 QS0 => ra rb;  apply: setXp_i => //; apply:setXp_i.
  rewrite /IFS_good_pair /z; aw; apply: cle0n.
  move/permutationsP: sp => [ [[ff _] _] ss ts]; rewrite /natp; Wtac; ue.
have zz: glt IFS_order z x.
  by apply/IFE_gltP; split => //;constructor 1; rewrite /z; aw.
exists z.
  apply: (Zo_i zE); exact: (proj1 zz).
by rewrite (IFE_consec_chain4 zE); rewrite /IFS_pow/z; aw.
Qed.


Lemma IFS_sub_pow_prop1 x : inc x IFSE ->
  cardinal (IFS_sub_pow x) =  csucc (P (P x)).
Proof.
move => xE; rewrite  (IFS_sub_pow_prop0 xE). 
move/Zo_P:(xE) => [/setX_P [px /setX_P [ppx ppn qpn] qpq] gp].
rewrite cardinal_fun_image ?(card_card (CS_succ _)) //.
move => a b /(NleP ppn) la /(NleP ppn) lb.
move/permutationsP: sp => [ [[ff fi] _] ss ts].
have aN: inc a (source sigma) by rewrite ss; apply:(NS_le_nat la ppn).
have bN: inc b (source sigma) by rewrite ss; apply:(NS_le_nat lb ppn).
move: (Vf_target ff aN) (Vf_target ff bN); rewrite ts.
by move=> /CS_nat ca /CS_nat cb; move/(csucc_inj  ca cb); apply: fi.
Qed.


Lemma IFS_sub_pow_prop2 n : natp n -> 
  exists2 x, inc x IFSE  &  cardinal (IFS_sub_pow x) =  csucc n.
Proof.
move => nN.
set z := J (J n \0c) \0q.
have zE: inc z IFSE.
  apply: Zo_i.
    by move: NS0 QS0 => ra rb;  apply: setXp_i => //; apply:setXp_i.
  rewrite /IFS_good_pair /z; aw; apply: cle0n.
  by move/permutationsP: sp => [ [[ff _] _] ss ts]; rewrite /natp; Wtac; ue.
by ex_tac; rewrite (IFS_sub_pow_prop1 zE) /z; aw.
Qed.

Lemma IFS_sub_pow_prop3 x (y := (IFS_sub_pow x)):
  inc x IFSE -> cardinal y = \1c -> union y = csucc (Vf sigma \0c).
Proof.
move => xE. 
move/Zo_P:(xE) => [/setX_P [px /setX_P [ppx ppn qpn] qpq] gp].
rewrite   (IFS_sub_pow_prop1 xE) - succ_zero.
move/(csucc_inj (CS_nat ppn) CS0) => pp.
by rewrite /y (IFS_sub_pow_prop0 xE) pp succ_zero funI_set1 setU_1.
Qed.
  

Lemma IFS_sub_pow_prop4 n a b (qa := IFS_sub_pow a) (qb := IFS_sub_pow b):
  natp n -> inc a IFSE ->  inc b IFSE -> 
  cardinal qa = csucc n -> cardinal qb = csucc (csucc n) ->
  union (qb -s qa)  = csucc (Vf sigma (csucc n)).
Proof.
move => nN aE bE; move: (NS_succ nN) => sN.
move/Zo_P:(aE) => [/setX_P [pa /setX_P [ppa ppna qpna] qpqa] gpa].
move/Zo_P:(bE) => [/setX_P [pb /setX_P [ppb ppnb qpnb] qpqb] gpb].
rewrite (IFS_sub_pow_prop1 aE) (IFS_sub_pow_prop1 bE).
move/(csucc_inj (CS_nat ppna) (CS_nat nN)) => ra.
move/(csucc_inj (CS_nat ppnb) (CS_succ n)) => rb.
rewrite / qa / qb (IFS_sub_pow_prop0 aE) (IFS_sub_pow_prop0 bE). 
rewrite ra rb (succ_of_nat sN) funI_setU1;
set U := fun_image _  _; set k := csucc _.
suff: (U +s1 k -s U) = singleton k by  move ->; rewrite setU_1.
apply: set1_pr; last by move => t /setC_P [/setU1_P]; case => //.
apply /setC_P; split; [ fprops | move/funI_P => [t /(NltP sN) ta tb]].
move/permutationsP: sp => [ [[ff fi] _] ss ts].
have aN: inc (csucc n) (source sigma) by rewrite ss.
have bN: inc t (source sigma) by rewrite ss; apply:(NS_lt_nat ta sN).
move: (Vf_target ff aN) (Vf_target ff bN); rewrite ts.
move=> /CS_nat ca /CS_nat cb; move/(csucc_inj  ca cb): tb.
by move/(fi _ _ aN bN) => hh; case: (proj2 ta).
Qed.

End InfSumStudy.


Lemma IFS_suminjective: { inc (permutations Nat) &,injective sier_inf_sum}.
Proof.
move => s1 s2 hs1 hs2 sv.
move: (IFE_osr s1) => [or1 sr1].
move: (IFE_osr s2) => [or2 sr2].
move: (order_type_exists or1).
move: (order_type_exists or2).
rewrite  (OT_of_E hs2) (OT_of_E hs1) sv => is2 is1.
move: (orderIT is1 (orderIS is2)) => [f isf] {sv is1 is2}.
move/permutationsP:(hs1) =>[[[fs1 ijs1] [_ sjs1]] ss1 ts1].
move/permutationsP:(hs2) =>[[[fs2 ijs2] [_ sjs2]] ss2 ts2].
apply:function_exten => //; try ue.
rewrite ss1 => n nN.
have qa: cardinalp (Vf s1 n) by apply: CS_nat; rewrite /natp; Wtac.
have qb: cardinalp (Vf s2 n) by apply: CS_nat; rewrite /natp; Wtac.
apply (csucc_inj qa qb); clear qa qb.
move:(isf) => [_ _ [bf sf tf] fm].
have ff: function f by fct_tac.
case: (equal_or_not n \0c).
  move ->.
  move: (IFS_sub_pow_prop2 hs1 NS0) =>[x1 x1e1 cx10].
  rewrite succ_zero in cx10.
  rewrite - (IFS_sub_pow_prop3 hs1 x1e1 cx10).
  rewrite - sr1 in x1e1.
  move: (sub_pow_pr0  isf x1e1).
  rewrite - sub_pow_pr1 - sub_pow_pr1 => eq2.
  have cc: cardinal (IFS_sub_pow s2 (Vf f x1)) = \1c.
    by rewrite - eq2 cx10.
  have x2s2: inc (Vf f x1)  (IFSE s2) by  rewrite - sr2 - tf; Wtac.
  by rewrite eq2 (IFS_sub_pow_prop3 hs2 x2s2 cc).
move => nz; move: (cpred_pr nN nz)=> [pN pv].
rewrite pv; set p := cpred n; rewrite -/p in pN.
move: (IFS_sub_pow_prop2 hs1 pN) =>[x1 x1e1 cx10].
move: (IFS_sub_pow_prop2 hs1 (NS_succ pN)) =>[x2 x2e1 cx20].
rewrite -  (IFS_sub_pow_prop4 hs1 pN x1e1 x2e1 cx10 cx20).
rewrite - sr1 in x1e1 x2e1.
have y1s2: inc (Vf f x1)  (IFSE s2) by  rewrite - sr2 - tf; Wtac.
have y2s2: inc (Vf f x2)  (IFSE s2) by  rewrite - sr2 - tf; Wtac.
move: (sub_pow_pr0  isf x1e1)  (sub_pow_pr0  isf x2e1).
rewrite - ! sub_pow_pr1 => eqa eqb.
have cc1: cardinal (IFS_sub_pow s2 (Vf f x1)) = (csucc p) by ue.
have cc2: cardinal (IFS_sub_pow s2 (Vf f x2)) = (csucc (csucc p)) by  ue.
rewrite eqa eqb.
by rewrite  (IFS_sub_pow_prop4 hs2 pN y1s2 y2s2 cc1 cc2).
Qed.

(* old
   
move/(ocle2P (CS_pow a b) qa): (cle_ltT qb (proj1 (Exercise6_33a''))) => h.
move:(cle_ltT qb (proj32 (cnext_pr1 (proj32 hb)))) => la.
move/(ocle2P (proj32_1 la) qa): (la) => ra.
split => //.
  move => t /(oltP qa) [pa _]; exact: (ole_ltT pa h).
have o3: ordinalp c by exact (proj1 (proj1 Exercise6_33c)).
move: h Exercise6_33b => [[_ _ s1] _] [[_ _ s2] _].
apply: (sub_trans s1 s2).
Qed.

 
*)
End OrderType.
