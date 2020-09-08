(** * Theory of Sets EIII-2 Well ordered sets 
Copyright INRIA (2009-2013 2018) Apics, Marelle Team (Jose Grimm).  *)

(* $Id: sset6.v,v 1.6 2018/09/04 07:58:00 grimm Exp $ *)


Set Warnings "-notation-overridden".
From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat. 
Set Warnings "notation-overridden".
Require Export sset5.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Worder.

(** ** EIII-2-1 Segments of a well-ordered set *)

(** Well ordering *)

Definition worder r :=
  order r /\ forall x, sub x (substrate r) -> nonempty x ->
    has_least (induced_order r x). 

Definition worder_r (r: relation) :=
  order_r r /\ forall x, {inc x, reflexive_r r} -> nonempty x ->
    has_least (graph_on r x). 

Definition worder_on G E := worder G /\ substrate G = E.

Lemma worder_or r: worder r -> order r.
Proof. exact: proj1. Qed.

Hint Resolve worder_or: fprops.

Lemma wordering_pr r x: 
  worder_r r -> {inc x, reflexive_r r} ->  
  worder_on (graph_on r x) x.
Proof.
move=> [or wo] ar.
have sg := (graph_on_sr ar).
have gor := (order_from_rel x or).
split=>//; split=>//. 
rewrite sg => s sx nes.
have rs: {inc s, reflexive_r r} by move=> a /sx/ar.
have sgs: substrate (graph_on r s) = s by rewrite graph_on_sr.
move: (wo _ rs nes)=> [a []]; rewrite sgs => ais lea.
have ss:sub s (substrate (graph_on r x)) by rewrite sg.
exists a; split; first by rewrite iorder_sr.
rewrite (iorder_sr gor ss) => y ys; aw.
move: (lea _ ys) => /graph_on_P1 [pa pb pc]; apply/iorder_gle0P => //.
by apply/graph_on_P1;split => //; apply: sx.
Qed.

Lemma worder_prop r x: worder r -> sub x (substrate r) -> nonempty x ->
  exists2 a, inc a x & (forall b, inc b x -> gle r a b).
Proof.
move => [or wor] xsr nex; move:(wor _ xsr nex) => [a []]; rewrite iorder_sr //.
by move=> ax ap; ex_tac => b /ap /iorder_gle1.
Qed.



Lemma worder_prop_eff r x (a := the_least_induced r x):
  worder r -> sub x (substrate r) -> nonempty x ->
  inc a x /\ (forall b, inc b x -> gle r a b).
Proof.
move => [or wor] xsr nex; move:(wor _ xsr nex) => hl.
move:(iorder_osr or xsr) => [oi si].
case: (the_least_pr oi hl); rewrite si => sa sb; split => //.
by move => b /sb  /iorder_gle1.
Qed.

Lemma worder_prop_rev r: order r ->
  (forall x, sub x (substrate r) -> nonempty x ->
    exists2 a, inc a x & (forall b, inc b x -> gle r a b)) ->
  worder r.
Proof.
move => h1 h2; split => // x xsr nex; move: (h2 x xsr nex) => [a ax ap].
exists a; hnf; rewrite iorder_sr //;split => // b bx.
by apply/iorder_gle0P => //; apply: ap.
Qed.

Lemma worder_prop2 r (p:property): worder r ->
  (forall x, inc x (substrate r) -> p x) \/
  (exists x, [/\  inc x (substrate r), ~p x & forall y, glt r y x -> p y]).
Proof.
move => wor; set A := Zo (substrate r) (fun x => ~p x).
case: (emptyset_dichot A) => aE.
  by left; move => x xst; ex_middle bad;empty_tac1 x;  apply: Zo_i.
right.
have sar: sub A (substrate r) by apply: Zo_S.
move: (worder_prop wor sar aE) =>[x /Zo_P[csr xa] xp]; exists x.
split => // => y lxy; ex_middle bad.
have /xp la: inc y A by apply: Zo_i => //; apply: (arg1_sr (proj1 lxy)).
case: (not_le_gt (proj1 wor) la lxy).
Qed.  
   

Lemma worder_invariance r r':
  r \Is r' -> worder r -> worder r'.
Proof. 
move=> [f [or or' [bf sf tf] sif]] wor.
apply:(worder_prop_rev or') => // x xsr [y yx].
set A := Vfs (inverse_fun f) x. 
have bif := (inverse_bij_fb bf).
have fi:= (proj1 (proj1 bif)).
have sxt: (sub x (target f)) by rewrite tf.
have sxs: (sub x (source (inverse_fun f))) by aw. 
have sx :source f = (target (inverse_fun f)) by aw.
have Asx: sub A (substrate r). 
   rewrite - sf sx; apply: sub_trans (dirim_S sxs) (Imf_Starget fi).
have neA: (nonempty A).  
  exists (Vf (inverse_fun f) y); apply /(Vf_image_P fi sxs); ex_tac.
move: (worder_prop  wor Asx neA) => [z zA zle].
move: (zA) => /(Vf_image_P fi sxs) [u ux Wu].
ex_tac; move =>// v vx. 
have utx: inc u (target f) by apply: sxt.
have uW :=inverse_V bf utx. 
have vt: inc v (target f) by apply: sxt.
set v':= Vf (inverse_fun f) v.
have vA: inc v' A by apply /(Vf_image_P fi sxs); ex_tac.
rewrite - (inverse_V bf vt) - uW - sif.
- by rewrite -Wu; move:(zle _ vA).
- rewrite sx; fprops.
- rewrite sx; fprops.
Qed.

(** The empty set is well-ordered *)


Lemma set0_osr: order_on emptyset emptyset.
Proof.
split; first by rewrite - setI_0; apply: setIrel_or => t /in_set0.
by rewrite /substrate domain_set0 range_set0 setU2_id.
Qed.

Lemma set0_wor: worder_on emptyset emptyset.
Proof.
move:set0_osr => [oe se].
split=> //; split => //; rewrite se; move => x xs [y yx].
case: (in_set0 (xs _ yx)).
Qed.

Lemma empty_substrate_zero x: substrate x = emptyset -> x = emptyset.
Proof.  by move /setU2_eq0P => [/domain_set0_P ]. Qed.

(** Singletons are well-ordered, and isomorphic  *)

Lemma set1_wor x:  worder_on (singleton (J x x)) (singleton x).
Proof.
set G := (singleton (J x x)).
have Ei: diagonal (singleton x) = G. 
  apply: set1_pr; first by apply/diagonal_pi_P;fprops.
  by move => z /diagonal_i_P [pa /set1_P]; rewrite - {4} pa => -> <-.
have [pa pb] := diagonal_osr (singleton x).
have oE: (order G) by rewrite -Ei.
have sE: (substrate G = singleton x) by rewrite - Ei pb.
split =>//; apply: (worder_prop_rev oE) => y yE [z zy]; ex_tac => t ty.
rewrite sE in yE.
by rewrite (set1_eq (yE _ zy)) (set1_eq (yE _ ty)); apply/set1_P.
Qed.

Lemma set1_order_is x y:
  (singleton (J x x))  \Is (singleton (J y y)).
Proof. 
have [[o1 _] s1] := (set1_wor x).
have [[o2 _] s2] := (set1_wor y).
have ta: lf_axiom (fun _ => y) (singleton x) (singleton y) by move=> t;fprops.
exists (Lf (fun _ => y) (singleton x) (singleton y)).
split => //.
 rewrite s1 s2; split; aw => //.
  apply lf_bijective => //. 
    by move=> u v /set1_P -> /set1_P ->.
  move=> t /set1_P ->; exists x;fprops.
hnf; rewrite lf_source => a b pa pb; rewrite !LfV // (set1_eq pa) (set1_eq pb).
by split; move => _; apply:set1_1. 
Qed.

Lemma set1_order_is0 r x: 
  order r -> substrate r = singleton x ->  r = singleton (J x x).
Proof. 
move=> or sxsu.
apply: set1_pr; first by order_tac;rewrite sxsu; fprops.
move=> v vx; move: (pr1_sr vx) (pr2_sr vx);rewrite sxsu.
move => /set1_P {2} <- /set1_P <-.  
by rewrite ((order_sgraph or) _ vx).
Qed.

Lemma set1_order_is1 r: 
  order r -> singletonp (substrate r) ->
  exists x, r = singleton (J x x).
Proof. by move=> or [x xa]; exists x; apply:set1_order_is0. Qed.
       
Lemma set1_order_is2 r r': 
  order r -> order r' -> 
  singletonp (substrate r) -> singletonp (substrate r') ->
  r \Is r'.
Proof.
move=> ox oy ssx ssy.
move: (set1_order_is1 ox ssx)=> [u ->].
move: (set1_order_is1 oy ssy)=> [v ->].
apply: set1_order_is.
Qed.

Lemma worder_set1 r e: order_on r (singleton e) -> worder r.
Proof. 
move=> [or sr].
rewrite(set1_order_is0 or sr); exact: (proj1(set1_wor e)).
Qed.


(** We sometimes need an ordered set with two elements; It is well-ordered *)

Definition canonical_doubleton_order :=
  (tripleton (J C0  C0) (J C1 C1) (J C0 C1)).

Lemma cdo_gleP x y:
  gle canonical_doubleton_order x y <->
  [\/ (x = C0 /\ y = C0),  (x = C1 /\ y = C1) | (x = C0 /\ y = C1)].
Proof.
split; first by case/set3_P; move => h;rewrite(pr1_def h)(pr2_def h); in_TP4.
case; move=> [-> ->]; apply /set3_P; in_TP4.
Qed.

Lemma cdo_glt1: glt canonical_doubleton_order C0 C1.
Proof. split; [ apply /cdo_gleP; in_TP4 | fprops]. Qed.

Lemma cdo_wor: worder_on canonical_doubleton_order C2.
Proof.
have cg: sgraph canonical_doubleton_order.
  by move => t /set3_P; case => ->; fprops. 
have subs: substrate canonical_doubleton_order = C2.
  set_extens x.
    case/(substrate_P cg) => [] [y] /cdo_gleP.
       case;case => ->; fprops.
    case;case => _ ->; fprops.
  case /C2_P => ->; apply: (@arg1_sr _ _ C1); apply /cdo_gleP; in_TP4.
have oc: (order canonical_doubleton_order). 
  split => //.
       move => y;rewrite subs; case /C2_P => ->;  apply /cdo_gleP; in_TP4.
    move=> x y z /cdo_gleP pa /cdo_gleP pb; apply /cdo_gleP.
    have aux: z = C0 \/ z = C1 by case: pb;move => [_ ->]; [left |right |right].
    case: (equal_or_not y C0); first by move => ->; case :aux => ->; in_TP4.
    case: pa; move => [-> pa] //.
    move: pa; case: pb;  move => [-> ->]; in_TP4.
  move=> x y /cdo_gleP pa /cdo_gleP.
  by case: pa; move=> [-> ->] //; case; try move => [ aa bb].
split; [ apply:(worder_prop_rev oc); rewrite subs => x xt nex | exact].
case: (inc_or_not C0 x)=> hyp.
  ex_tac => y yx; apply /cdo_gleP; case /C2_P: (xt _  yx) => ->; in_TP4. 
move: nex=> [y yx]; ex_tac.
have p: forall t, inc t x -> t = C1.
  by move=> t tx; case/C2_P: (xt _ tx) => // ta;case: hyp; rewrite - ta.
by move => t tx; apply /cdo_gleP;rewrite (p _ yx)(p _ tx); constructor 2.
Qed.

(** A well ordering is total; bounded sets have a supremum *)

Lemma worder_total r: worder r -> total_order r.
Proof. 
move=> wor; move: (proj1 wor) => or; split=> // x y xs ys.
move:(set2_1 x y)(set2_2 x y);set (u:=doubleton x y) => xu yu.
have ur: sub u (substrate r) by apply: sub_set2. 
have si: substrate (induced_order r u) = u by rewrite iorder_sr.
have neu: nonempty u by ex_tac.
move: (worder_prop wor ur neu)=> [z zu zle].
move: (zle _ xu)(zle _ yu) => p1 p2.
by case /set2_P: zu => <-; [left | right].
Qed.

Lemma worderr_total r x y: worder_r r -> r x x -> r y y ->
    (r x y \/ r y x).
Proof.
move => [p1 p2] rxx ryy.
move:(set2_1 x y)(set2_2 x y);set (u:=doubleton x y) => xu yu.
have p3: {inc u, reflexive_r r} by move => a /set2_P; case => ->.
have p4: nonempty u by ex_tac.
have p5:(substrate (graph_on r u)) = u by apply: graph_on_sr.
move: (p2 _ p3 p4)=> [z []]; rewrite p5 => zu zle.
move: (zle _ xu) => /graph_on_P1 [_ _ zx].
move: (zle _ yu) => /graph_on_P1 [_ _ zy].
by case /set2_P: zu => <-; [left | right].
Qed.

Lemma worder_hassup r A: worder r -> sub A (substrate r) ->
  bounded_above r A -> has_supremum r A.
Proof. 
move=> H As [t tA].
rewrite /has_supremum /least_upper_bound.
set X:= (Zo _ _).
have Xs: sub X (substrate r) by apply: Zo_S. 
have nX: (nonempty X) by exists t; apply: (Zo_i (proj1 tA) tA).
by move: ((proj2 H) _ Xs nX)=> [x leX]; exists x.
Qed.

Lemma induced_wor r A: worder r -> sub A (substrate r) ->
  worder (induced_order r A).
Proof. 
move=> [or wo] As; move: (iorder_osr or As) => [pa pb].
split; [exact | rewrite pb => x sx nex].
rewrite (iorder_trans _ sx). 
by apply: wo=>//; apply: sub_trans As. 
Qed.

Lemma worder_least r: worder r -> nonempty (substrate  r) ->
  has_least r.
Proof. 
move=> [or wo] ne.
move: (wo  _ (@sub_refl (substrate r)) ne)=> [x]. 
by rewrite iorder_substrate //; exists x.
Qed.

(** A set remains well-ordered after adjoining a greatest element *)
  
Lemma worder_adjoin_greatest r a: worder r -> ~ (inc a (substrate r)) ->
  worder (order_with_greatest r a).
Proof. 
move=> wor nas.
have [[on sn] rd [ _ gna]]:= (order_with_greatest_pr (proj1 wor) nas).
apply:(worder_prop_rev on) => x xs nex.
set (y := x \cap (substrate r)).
case: (emptyset_dichot y) => ye.
  have xa: x = singleton a.
    apply: set1_pr1 => //.
    move=> z zx; move: (xs _ zx); rewrite sn; case /setU1_P => // zr.
    by empty_tac1 z; apply:setI2_i.
  have ax: inc a x by rewrite xa; fprops.
  by ex_tac; rewrite xa => t /set1_P ->; order_tac; apply: xs.
have sys:sub y (substrate r) by apply: subsetI2r.
move: (worder_prop wor sys ye)=> [z zy lez].
have zx:= (setI2_1 zy).
exists z => // t tx.
move: (xs _ tx); rewrite sn; case /setU1_P => p.
  have ty: inc t y by apply: setI2_i.
  by move: (lez _ ty) => pa; apply:setU2_1.
by rewrite p; apply: gna; apply: xs.
Qed.

(** Every set can be well-ordered; 
We assume here [inc (rep a) a] for any non-empty subset of [E] *)

Definition Zermelo_chain E F := 
  let p :=  fun a => a -s1 (rep a) in
   [/\ sub F (\Po E), inc E F,
    (forall A, inc A F -> inc (p A) F) 
    & (forall A, sub A F -> nonempty A -> inc (intersection A) F)].

Definition worder_of E :=
  let om :=  intersection (Zo (\Po (\Po E)) (Zermelo_chain E)) in
  let d:= fun x => intersection (Zo om (sub x)) in
  let R := fun x => d (singleton x) in
  graph_on (fun x y => (sub (R y) (R x))) E.


Definition segment_r r x:= interval_cu r x.
Definition Zermelo_like r:= worder r /\ 
  forall x, inc x (substrate r) -> rep (segment_r r x) = x.

Lemma segment_rP r x y: inc y (segment_r r x) <-> gle r x y.
Proof.
split; first by move /Zo_P => [].
move => h; apply: Zo_i => //; order_tac.
Qed.


Lemma Zermelo_ter E (r := worder_of E):
   worder_on r E /\ Zermelo_like r.
Proof.
rewrite /r /worder_of; clear r.
pose p a:=  a -s1 (rep a).
have sp: forall a, sub (p a) a by move=> t; apply:sub_setC.
set chain := (Zermelo_chain E).
set om := intersection (Zo (\Po (\Po E)) chain).
set res := graph_on _ _.
have cp: chain (\Po E). 
  split; fprops; first by apply /setP_P. 
    move=> A /setP_P AE;apply/setP_P /(sub_trans (sp A) AE). 
  move=> A AP [x xA]; move: (AP _ xA) => /setP_P xE; apply/setP_P.
  move=> t ti; exact: (xE _ (setI_hi ti xA)).
have co :chain om.
  have aux: nonempty (Zo (\Po (\Po E)) chain).
    by exists (\Po E); apply: Zo_i; aw; trivial;apply: setP_Ti.
  split. 
  + by apply:setI_s1; apply: Zo_i=> //; apply: setP_Ti.
  + by apply: (setI_i aux) =>y /Zo_hi [_].
  + move=> A Ai; apply:(setI_i aux) => y yi.
    move/Zo_hi: (yi) => / proj43;apply;apply: (setI_hi Ai yi). 
  + move=> A sAi neA;  apply: (setI_i aux) => y yi.
    by move/Zo_hi: (yi) => /proj44; apply => // t /sAi /setI_hi; apply.
move: (co)=> [sop Eo po io].
have cio: forall x, chain x -> sub om x.
  by move=> x [ha hb hc hd]; apply: setI_s1; apply: Zo_i =>//;apply /setP_P.
pose m a:= forall x, inc x om -> sub x a \/ sub a x.
have am: om = Zo om m. 
  apply: extensionality; last by apply: Zo_S.
  apply: (cio); split => //.
  + by apply: sub_trans sop; apply: Zo_S.
  + by apply: Zo_i=>//; move=> x xom; left;move: (sop  _ xom); move/setP_P.
  + move=> A /Zo_P [Aom mA]; apply: Zo_i; first by apply: (po _ Aom).
    suff aux: sub om (Zo om (fun x=> sub x (p A) \/ sub A x)).
      move=> x xom; case: (mA _ xom) => hyp.
        move: (aux _ xom) => /Zo_hi; case =>xpB; first by left.
        rewrite (extensionality xpB hyp); right; apply: sp.
      right;  apply: (sub_trans (sp A) hyp).
    apply: cio; split.
    - by apply: (@sub_trans om); first by apply: Zo_S. 
    - by apply: Zo_i=>//; right; move: (sop _ Aom);move/setP_P.
    - move => B /Zo_P [Bom ors]; apply: Zo_i; first by apply: (po _ Bom).
      case: ors => orsi; first by left; apply: sub_trans orsi; apply: sp.
      case: (mA _ (po _ Bom)) => aux; last by right.
      case: (inc_or_not (rep B) A)=> aux2.
        rewrite (extensionality orsi _); first by left.
        move=> t tB; case: (equal_or_not t (rep B)); first by move=> ->. 
        by move=> trB; apply: aux; apply/setC1_P; split.
      right; move=> t tA;apply/setC1_P;split; [ by apply: orsi| dneg trB; ue].
    - move=> B sB neB; apply: Zo_i.
        apply: io =>//;  apply: (sub_trans sB) ; apply: Zo_S. 
      case: (p_or_not_p (exists x, inc x B /\ sub x (p A))) => H.
        move: H=> [x [xB xp]]; left; move=> t ti; apply:(xp _ (setI_hi ti xB)).
      right; move=> t tA;  apply: setI_i=>//. 
      move=> y yB; move: (sB _ yB) => /Zo_P [yom ]; case; last by apply.
      by move => sy; case: H; exists y.
  + move=> A sAZ neA; apply: Zo_i.
      apply: io =>//; apply: (sub_trans sAZ); apply: Zo_S.
    move=> x xom.
    case: (p_or_not_p (exists2 y, inc y A & sub y x)) => H.
      move: H=> [y yA yx]; right; move => t ti;apply: (yx _ (setI_hi ti yA)).
    left; move=> t tx; apply: setI_i=>//. 
    move=> y yA; move: (sAZ _ yA)=> /Zo_P  [yom my]. 
    case: (my _ xom);[ by apply| move=> yx; case: H;ex_tac; apply: Zo_S].
have st: forall a b, inc a om -> inc b om -> sub a b \/ sub b a.
  move=> a b; rewrite {2} am; move => aom  /Zo_P [bom ba]; apply: (ba _ aom).
pose d p := intersection (Zo om (sub p)).
have dpo: forall X, sub X E -> inc (d X) om. 
  by move=> X XE; rewrite /d; apply: io;[ apply:Zo_S | exists E;apply: Zo_i].
have pdp: forall X, sub X E -> sub X (d X).
  rewrite /d=> X XE t tX; apply: setI_i; first by exists E; apply: Zo_i.  
  by move => y /Zo_hi; apply.
have dpq: forall X Y, inc Y om -> sub X Y -> sub X E -> sub (d X) Y.
  by rewrite /d=> X Y Yom XY XE; apply: setI_s1; apply: Zo_i.
have rdq: forall X, sub X E -> nonempty X -> inc (rep (d X)) X. 
  move=> X XE neX; case: (inc_or_not (rep (d X)) X)=>// ni.
  have ned: nonempty (d X) by exists (rep X); apply: pdp => //; apply: rep_i.
  move: (conj (pdp _ XE) ni) => /subsetC1_P aux.
  case:(setC1_1 ((dpq _ _ (po _ (dpo _ XE)) aux XE)  _ (rep_i ned))).
have qdp: forall X Y, inc Y om -> sub X Y -> inc (rep Y) X -> Y = d X.
  move => X Y Yom sXY YX.
  have sXE: sub X E by apply: (sub_trans sXY); apply /setP_P; apply: sop.
  apply: extensionality  (dpq _ _ Yom sXY sXE). 
  case: (st _ _  (dpo _ sXE) (po _ Yom)) => ch.
    by case /setC1_P: (ch _  ( (pdp _ sXE) _ YX)) => _.
  rewrite - (setC1_K (sXY _ YX)); apply:(setU1_sub ch ((pdp _ sXE) _ YX)).
pose R x := d (singleton x).
have Rp: forall x, inc x E -> 
    [/\ inc (R x) om, inc x (R x) & rep (R x) = x]. 
  move => x xE.
  have p1: sub (singleton x) E by apply: set1_sub. 
  split; [ by apply: dpo | exact:(pdp _ p1 _ (set1_1 x)) | ].
  exact:(set1_eq (rdq _ p1 (set1_ne x))).
have Ri:forall x y, inc x E -> inc y E -> R x = R y -> x = y.
  move=> x y xE yE; move: (Rp _ xE)(Rp _ yE). 
  by move=> [_ _ p1][_ _ p2] p3; rewrite -p3 in p2; rewrite -p1 -p2.
have Rrq: forall X, inc X om -> nonempty X -> R (rep X) = X. 
  move=> X Xom neX; symmetry; apply: qdp =>//; last by fprops.
  by move=> t /set1_P ->;  apply: rep_i.
have sRR: forall x y, inc x E -> inc y E -> inc x (R y) -> (sub (R x) (R y)).
  move=> x y xE yE xRy.
  move: (Rp _ xE)(Rp _ yE) => [Rom xRx rR] [Rom' yRy rR'].
  case: (st _ _ Rom Rom') =>// hyp.
  move: (sub_set2 xRy yRy) => p1; move: (sub_trans p1 hyp) => p2.
  have p3: (inc (rep (R x)) (doubleton x y)) by rewrite rR; fprops.
  have p4: (inc (rep (R y)) (doubleton x y)) by rewrite rR'; fprops.
  by rewrite (qdp _ _ Rom p2 p3) (qdp _ _ Rom' p1 p4).
have [or sr]:order_on res E.
  split; last by apply: graph_on_sr => a _.
  apply: order_from_rel1.
  + by move=> x y z /= xy yz; apply: sub_trans yz xy. 
  + by move=> u v uE vE vu uv; apply: Ri=>//; apply: extensionality.
  + by move => u ue.
have wor:worder res.
  apply:(worder_prop_rev or)=> x; rewrite sr => xsr nex.
  move:(rdq x xsr nex) => rdx.
  ex_tac=> a ax; apply/graph_on_P1; split => //; try apply: xsr => //.
  move: ((pdp _ xsr) _ ax)=> adx;  apply: sRR; fprops.
  have ne: (nonempty (d x)) by exists a.
  by rewrite  (Rrq _ (dpo _ xsr) ne). 
split=>//;split=>//; rewrite sr -/res => x xE.
suff: (segment_r res x) = R x by move => ->; exact:(proj33 (Rp _ xE)).
set_extens t.
  move /segment_rP /(graph_on_P0 (fun x y=> sub (R y) (R x)) E x t).
  move => [_ tE ]; apply; exact (proj32 (Rp _ tE)).
move => tR; move: ((setP_hi (sop _ (proj31 (Rp _ xE)))) _ tR) => tE.
by apply/segment_rP; apply/graph_on_P1; split => //; apply: sRR.
Qed.

(** Two stricly increasing functions with the same range are equal if the source is well-ordered *)

Lemma strict_increasing_extens f g r r':
  strict_increasing_fun f r r'-> strict_increasing_fun g r r' -> worder r ->
  Imf f = Imf g -> f = g.
Proof.
move=> sif sig wo.
have to: total_order r by apply: worder_total.
have sm: (strict_monotone_fun f r r') by left.
have smg: (strict_monotone_fun g r r') by left.
have injf:= (total_order_monotone_injective to sm).
have injg:= (total_order_monotone_injective to smg).
move:sif sig=> [or or' [ff sr sr'] si] [_ _ [fg srg sr'g] sig] rr {sm smg}.
case:(worder_prop2 (fun x=> Vf f x = Vf g x) wo) => H.
  apply: function_exten=>//; try ue. 
move: H =>[x [xsr xb sc]].
have xsf: inc x (source f) by ue.
have xsg: inc x (source g) by ue.
have: inc (Vf f x) (Imf g) by rewrite -rr; Wtac.
move/(Imf_P fg) => [y ysg WW].
move:(ysg); rewrite srg - sr=> ysf.
have: inc (Vf g x) (Imf f) by rewrite rr; Wtac.
move/(Imf_P ff) => [z zsf WWw].
move:(zsf); rewrite sr - srg=> zsg.
have ysr: inc y (substrate r) by rewrite srg in ysg.
have zsr: inc z (substrate r) by rewrite sr in zsf.
have p1: glt r' (Vf g x) (Vf f x).
  have a0: y <> x by move => h; case: xb; rewrite WW h.
  rewrite WW; case: (total_order_pr1 to ysr xsr) => // h;last by apply: sig.
  by move: (sc _ h); rewrite - WW => eq1; case:a0; apply: (proj2 injf).
have p2: glt r' (Vf f x) (Vf g x).
  have a0: x <> z by  move => h; case: xb; rewrite  WWw h.
  rewrite WWw; case: (total_order_pr1 to xsr zsr) => h //; first by apply: si.
  by move: (sc _ h); rewrite - WWw => eq1; case:a0; apply: (proj2 injg).
order_tac.
Qed.


Lemma iso_unique r r' f f': 
  worder r -> order_isomorphism f r r' ->  order_isomorphism f' r r' ->
  f = f'.
Proof.
move => wor ha hb.
have ha':= (order_isomorphism_increasing ha).
have hb':= (order_isomorphism_increasing hb).
have hd: Imf f = Imf f'.
  move: ha => [_ _ [[_ /surjective_pr0 ->] _ ->] _]. 
  by move: hb => [_ _ [[_ /surjective_pr0 ->] _ ->] _]. 
apply(strict_increasing_extens ha' hb' wor hd).
Qed.


Lemma iso_unique_bis r r' f f': 
  worder r' -> order_isomorphism f r r' ->  order_isomorphism f' r r' ->
  f = f'.
Proof.
move => wor ha hb.
have iso: r' \Is r by exists (inverse_fun f); apply:(inverse_order_is ha).
exact: (iso_unique (worder_invariance iso wor) ha hb).
Qed.

(** A segment is a set such that if if contains [x], 
it contains all elements less than [x]. Left-unbounded intervals are segments. *)

Definition segmentp r s :=
  sub s (substrate r) /\ forall x y, inc x s -> gle r y x -> inc y s.
Definition segment r s := interval_uo r s.
Definition segmentc r s := interval_uc r s.

Lemma lt_in_segment r s x y:
  segmentp r s ->  inc x s -> glt r y x -> inc y s.
Proof. move=> [ss sp] xs [le ne]; apply: sp xs le. Qed.

Lemma inc_segment r x y:
  inc y (segment r x) -> glt r y x.
Proof. by move /Zo_hi. Qed.

Lemma not_in_segment  r x: ~ inc x (segment r x).
Proof. by move=> /inc_segment/proj2. Qed.

Lemma sub_segment r x: sub (segment r x) (substrate r).
Proof. by move=> t /Zo_S. Qed.

Lemma sub_segment1 r s: segmentp r s -> sub s (substrate r).
Proof. by move=> [ss sp] t ts; apply: ss. Qed.

Lemma sub_segment2 r x y:  sub (segment (induced_order r x) y) x.
Proof. by move=> t /Zo_hi [/setI2_2 /setXp_P [] ]. Qed.

Lemma segment_inc r x y: glt r y x -> inc y (segment r x). 
Proof. move=> xy;apply /Zo_i =>//;order_tac. Qed.

Lemma segmentP r x y: inc y (segment r x) <-> glt r y x.
Proof. by split; [ apply: inc_segment | apply: segment_inc].  Qed.

Lemma lt_in_segment2 r x s y:
  segmentp r s -> inc x s -> inc y (segment r x) -> inc y s.
Proof.  move => [_ h] xs /segmentP [le _]; apply:(h _ _ xs le). Qed.

Lemma segmentcP r x y: inc y (segmentc r x) <-> gle r y x.
Proof. 
split; [ by move/Zo_P => [] | move =>h;apply: Zo_i =>//; order_tac ].
Qed.

Lemma inc_bound_segmentc r x: order r -> inc x (substrate r) ->
  inc x (segmentc r x).
Proof. by move=> or xs;apply/segmentcP =>//; order_tac. Qed.

Lemma sub_segmentc r x: sub (segmentc r x) (substrate r).
Proof. by move=> t /Zo_S. Qed.

Hint Resolve inc_bound_segmentc: fprops.

Lemma segmentc_pr r x: order r -> inc x (substrate r) ->
  (segment r x) +s1 x = segmentc r x.
Proof.
move=> or xsr;set_extens y.
  case /setU1_P; first by move/segmentP => [pa _]; apply/segmentcP.
  by move => -> ; apply inc_bound_segmentc.
move/segmentcP => h; case: (equal_or_not y x)=> h1.
  by apply/setU1_P; right.
by apply/setU1_P; left; apply/segmentP; split.
Qed.

(** Examples of segments. Empty set, whole substrate, union, intersection, subsegments*)

Lemma set0_segment r: segmentp r emptyset.
Proof. by split; [ fprops | move=> x y /in_set0 ]. Qed.

Lemma substrate_segment r: segmentp r (substrate r).
Proof. split => // x y xst xy; order_tac. Qed.

Lemma segment_segment r x: order r ->  segmentp r (segment r x).
Proof. 
move=> or;split; first by apply: Zo_S. 
move=> a b /Zo_P [asr ax] ba; apply: Zo_i; order_tac. 
Qed. 

Lemma segmentc_segment r x: order r -> segmentp r (segmentc r x).
Proof.
move=> or; split; first by apply: Zo_S. 
move=> a b /Zo_P [asr ax] ba; apply: Zo_i; order_tac.
Qed. 

Lemma subsegment_segment r s s': order r -> 
  segmentp r s -> segmentp (induced_order r s) s' -> segmentp r s'.
Proof. 
move=> or srs sis. 
move: (sub_segment1 srs)=>ssr. 
hnf; move: sis; rewrite /segmentp iorder_sr//.
move=> [s's hyp]; split; first by apply: sub_trans s's ssr.
move=> x y xs' yx; move: (s's _ xs')=> xs; move: srs=> [_ h].
apply: (hyp _ _ xs'); apply /iorder_gle0P => //; apply: h xs yx.
Qed.

Lemma setI_segment r s: 
   (alls s (segmentp r)) -> segmentp r (intersection s).
Proof.
move=>  als; split; first by apply: setI_sub2 => x /als/proj1.
move=> x y xi yx; case: (emptyset_dichot s) => nes.
   by move: xi; rewrite nes setI_0 => /in_set0.
apply: (setI_i nes) => z zs; move: (als _ zs) => [_ p]. 
apply : p (setI_hi xi zs) yx.
Qed.

Lemma setUf_segment r j s:
  (alls j (fun x => segmentp r (s x))) -> segmentp r (unionf j  s).
Proof. 
move=> als; split.
  move=> t tu;move: (setUf_hi tu)=> [y yj ts].
  by move:(als _ yj) => [ss _]; apply: ss.
move=> x y xu xy;move: (setUf_hi xu)=>  [z zj ts].
move:(als _ zj) => [_ ss]; move: (ss _ _ ts xy) =>h; union_tac.
Qed. 

Lemma setU_segment r s: (alls s (segmentp r)) -> segmentp r (union s).
Proof. by move=>  als; rewrite setU_prop; apply: setUf_segment. Qed.

(** Any segment is [ segment r x] or the whole set *)


Theorem well_ordered_segment r s: worder r -> segmentp r s ->
  s = substrate r \/ (exists2 x, inc x (substrate r)& s = segment r x).
Proof.
move=> wor sr.
case: (equal_or_not s (substrate r));[by left | move=> snr; right].
set y:= (substrate r) -s s.  
have ney: nonempty y by move: sr=> [sr _] ; apply: setC_ne. 
have tor := (worder_total wor); have or := proj1 tor.
have sys: (sub y (substrate r)) by apply: sub_setC.
move: (worder_prop wor sys ney)=> [x xy xle].
have xis: inc x (substrate r) by apply: sys. 
ex_tac;set_extens z => zs.
  apply/segmentP.
  have zsr: inc z (substrate r) by apply: (sub_segment1 sr). 
  case: (total_order_pr2 tor zsr xis) => //.
  by case /setC_P: xy => [_  bad]  /(proj2 sr _ _ zs).
ex_middle zis.
have zy: (inc z y) by apply/setC_P; split => // ;apply: (sub_segment zs).
move: (xle _ zy) (inc_segment zs)=> p1 p2; order_tac.
Qed.

Lemma segment_alt r x a: least r a ->
  segment r x = interval_co r a x.
Proof. 
move => [ais lea]; set_extens t; move /Zo_P => [pa pb]; apply/Zo_P;fprops.
by move: pb =>  [_].
Qed.

Lemma segment_alt1 r s: worder r -> segmentp r s ->
  s = substrate r \/ (exists x, exists a, s = interval_co  r a x).
Proof. 
move => wo iss.
case: (emptyset_dichot (substrate r)) => sre.
  by left; move: iss=> []; rewrite sre => /sub_set0.
case: (well_ordered_segment wo iss); first by left.
move: (worder_least wo sre) => [a lea] [x xsr p]. 
by right; exists x, a; rewrite - segment_alt. 
Qed.

Lemma segment_monotone r x y: order r -> gle r x y ->
  sub (segment r x) (segment r y).
Proof. 
move=> or xy t ts; move: (inc_segment ts) => h. 
apply: segment_inc; order_tac.
Qed.

Lemma segment_dichot_sub r x y:
  worder r -> segmentp r x -> segmentp r y ->
  (sub x y \/ sub y x).
Proof. 
move=> wo sx sy.
case: (well_ordered_segment wo sx).
  by move=> ->; right; apply: sub_segment1. 
case: (well_ordered_segment wo sy).
  by move=> ->; left; apply: sub_segment1. 
move=>[b br ->] [a ar ->].
by case: (proj2 (worder_total wo) _ _ ar br) => le;
    [left | right]; apply: (segment_monotone (proj1 wo)).
Qed.

Lemma le_in_segment r x y z: order r -> inc x (substrate r) ->
  inc y (segment r x) -> gle r z y -> inc z (segment r x).
Proof. 
move=> or xsr ysr zy; apply: segment_inc.
move: (inc_segment ysr)=> aux; order_tac.
Qed. 
  
Lemma coarse_segment_monotone r x y: order r -> gle r x y ->
  sub (coarse (segment r x)) (coarse (segment r y)).
Proof. 
by move=> or xy;move: (segment_monotone or xy) =>sm; apply: setX_Slr.
Qed.

Lemma segment_induced_a r s x:
  segmentp r s -> inc x s -> 
  segment (induced_order r s) x = segment r x.
Proof.
move=> srs xs; set_extens t=>  ys.
  move: (inc_segment ys)=> iys; move: (iorder_gle2 iys)=> tx. 
  by apply: segment_inc. 
apply: segment_inc.
move: (inc_segment ys)=> [tx nxy]; split => //; apply /iorder_gle0P=> //.
exact (proj2 srs _ _ xs tx).
Qed.

Lemma segment_induced r a b: order r ->  glt r b a ->
  segment (induced_order r (segment r a)) b = segment r b.
Proof.
move=> or /segmentP ab.
exact: (segment_induced_a  (segment_segment _ or) ab). 
Qed.

Lemma segment_induced1 r a b: order r ->  glt r b a ->
  segment (induced_order r (segmentc r a)) b = segment r b.
Proof.
move=> or /proj1/segmentcP ba. 
exact: (segment_induced_a  (segmentc_segment _ or) ba).
Qed. 

(** The union of all segments of [E], distinct from [E], 
is [E] when it has no gratest element, [E] minus its greatest element otherwise.
  Assumes the set totally ordered *)

Definition segmentss r:= 
  fun_image (substrate r) (segment r).

Lemma union_segments r (E := substrate r)(A := union (segmentss r)):
   total_order r ->
   ( (forall x, ~ (greatest r x)) -> A = E)
   /\ (forall x, greatest r x -> A = E -s1 x).
Proof.
move=> tor.
have Ap: forall x, inc x A <-> exists y, glt r x y.
  move=> x;split.
    move/setU_P => [y xy /funI_P [z zE sy]]. 
    exists z; apply: inc_segment;ue.
  move=> [y xy]; apply/setU_P;exists (segment r y).
    by apply: segment_inc=>//; order_tac.
   apply/funI_P; exists y => //; rewrite /E; order_tac.
have AE: sub A E by move=> t /Ap [y xy]; rewrite /E;order_tac. 
split.
  move=> p; apply: extensionality=>// t tE. 
  apply /Ap; ex_middle bad; case: (p t); split =>//.
  move=> y ysr; case: (total_order_pr2 tor tE ysr)=>//. 
  by move=> ty; case: bad; exists y.
move=> x [xs gr]; set_extens y => ys.
  apply/setC_P;split; first by apply: AE.
  move=> /set1_P xy; move: ys => /Ap [z yz].
  have zc: inc z (substrate r) by order_tac. 
  move: (gr _  zc) => aux. 
  rewrite xy in yz; move:tor=> [or _];order_tac.
move /setC_P: ys =>  [yE] /set1_P yx.
by apply/Ap; exists x; split=>//; apply: gr.
Qed. 

(** The mapping that associates to each [x] the segment with endpoint [x] is a 
bijection from [E] to the set of segments of [E], different from [E]. 
It is an order isomorphism (target ordered by inclusion), for any well-ordering.
The set of all segments is thus well-ordered *)

Definition segments r:= 
  (segmentss r) +s1 (substrate r).
Definition segments_iso r:= 
  Lf (segment r) (substrate r) (segmentss r).

Lemma inc_segmentsP r: worder r -> forall x,
  (segmentp r x <-> inc x (segments r)).
Proof.
move => wor x; split=> hyp.  
  case: (well_ordered_segment wor hyp).
    by move => ->; apply /setU1_P; right.
  move=> [y ysr ->]; apply /setU1_P; left; apply/funI_P; ex_tac.
move:wor=> [or  wor].
case /setU1_P: hyp.
  by move/funI_P => [z zr ->];  apply: segment_segment. 
by move=> ->; apply: substrate_segment.
Qed.

Lemma segment_insetof r x: worder r -> inc (segment r x) (segments r).
Proof.
move=> wo; apply/(inc_segmentsP wo).
apply: segment_segment; fprops. 
Qed. 

Lemma segmentc_insetof r x: worder r -> inc (segmentc r x) (segments r).
Proof.
move=> wo ; apply/(inc_segmentsP wo).
apply: segmentc_segment; fprops. 
Qed.

Lemma sub_segments r x: worder r ->
  inc x (segments r) -> sub x (substrate r).
Proof. move=> wor /(inc_segmentsP wor) ;apply: sub_segment1. Qed.

Lemma segment_monotone1 r x y: total_order r ->
  inc x (substrate r) ->  inc y (substrate r) ->  
  sub (segment r x)(segment r y) -> gle r x y.
Proof.
move=> tor xsr ysr sxy.
case: (total_order_pr2 tor ysr xsr)=>//.
by move/segmentP=> yis; move: (sxy _ yis) => /segmentP [].
Qed.

Lemma segment_injective r : total_order r ->
  {inc (substrate r) &,  injective (segment r) }.
Proof.
move=> tor x y xsr ysr sxy.
have p1: (sub (segment r x)(segment r y)) by rewrite sxy.
have p2: (sub (segment r y)(segment r x)) by rewrite sxy.
have p3:= (segment_monotone1 tor xsr ysr p1).
have p4:= (segment_monotone1 tor ysr xsr p2).
move: tor=> [or _]; order_tac.
Qed.

Theorem segments_iso_is r: worder r ->
  order_isomorphism (segments_iso r) r (sub_order (segmentss r)).
Proof.
move=> wor;move: (wor)=> [or worp].
have ta: lf_axiom (segment r) (substrate r) (segmentss r).
  by move => t ts; apply /funI_P; ex_tac.
move: (sub_osr (segmentss r)) => [pa pb].
hnf; rewrite /segments_iso;split => //.  
  split;aw => //; apply: lf_bijective=> //.
  + move=> u v; apply: (segment_injective (worder_total wor)).
  + move=> y /funI_P [z za ->];ex_tac.
hnf; aw;move=> x y xsr ysr; rewrite !LfV //; split.
  move=> hyp; apply/sub_gleP;split => //; fprops.
  by apply: segment_monotone. 
move /sub_gleP=> [_ _ ss].
exact: (segment_monotone1 (worder_total wor) xsr ysr ss).
Qed.


Theorem segments_worder r: worder r ->
  worder (sub_order (segments r)).
Proof. 
move=> wor; move: (wor)=> [or _];move: (worder_total wor)=> tor.  
have [oi sr] := (sub_osr (segments r)).
apply:(worder_prop_rev oi); rewrite sr => x xsr nex.
set y := x \cap (segmentss r).
case: (emptyset_dichot y) => hy.
  have xv: x = singleton (substrate r).
    apply: set1_pr1=>// z zx.
    case /setU1_P: (xsr _ zx) => //.
    by move=> aux; empty_tac1 z; apply: setI2_i.
  have srx: inc (substrate r) x by rewrite xv; fprops.
  by ex_tac; rewrite xv; move=> z /set1_P ->; order_tac;rewrite sr; apply:xsr.
have ysr: sub y (segmentss r) by move => t ty; apply: (setI2_2 ty).
have segp a: inc a y -> exists2 u, inc u (substrate r) & a = segment r u.
   by move=> /ysr /funI_P.
pose cf a := select(fun u => a = segment r u) (substrate r).
have cfp: forall a, inc a y -> 
     (inc (cf a) (substrate r) /\ a = segment r (cf a)).
   move=> a ay; move: (segp _ ay) => [u us uv].
   have  <- //: u = cf a.
   apply: (select_uniq _ us uv); move => c b csr sc bsr  sb.
   by apply: (segment_injective (worder_total wor) csr bsr); rewrite - sb - sc.
set (z:= fun_image y cf). 
have nez: nonempty z by apply: funI_setne.
have zsr: sub z (substrate r).
   by move => t /funI_P [u uy ->]; move: (cfp _ uy)=> [res _].
move: (worder_prop wor zsr nez) => [a asr lea].
have sax: (inc (segment r a) x).
  move: asr => /funI_P [u uy ->].
  move: (cfp _ uy)=> [h <-];  apply: (setI2_1 uy).
ex_tac;move=> b bx; apply/sub_gleP; split; fprops.
case /setU1_P: (xsr _ bx); [ move => h | by move=>->; apply: sub_segment ].
have biy: (inc b y) by apply: setI2_i.
have cbz: (inc (cf b) z) by apply /funI_P; ex_tac.
move: (lea _ cbz).
by move: (cfp _ biy)=> [p1 {2} ->]; apply: segment_monotone.
Qed.

(** Assume that [G] is a family such that (a) each [G(i)] is a well-ordering 
on [E(i)]; (b) if [E(i)] is a subset of [E(j)], then  [G(j)] agrees with [G(i)] on  [E(i)], and (c) for any [i] and [j] there is [k] such that [E(k)] is a 
subset of [E(i)] and [E(j)]. Instead of (c) we may assume (d) that one  
[E(i)] of [E(j)] is a segment of the order.

Then the union of [G] is a well-ordering; moreover
segments of the union are segments of [G(i)]. *)


Definition worder_fam g := allf g worder.
Definition order_extends r r' := r = induced_order r' (substrate r).
Definition monotone_order_fam g :=
  forall a b, inc a (domain g) -> inc b (domain g) ->
    sub (substrate (Vg g a)) (substrate (Vg g b)) ->
    order_extends (Vg g a) (Vg g b).

Definition common_extension_order g h:=
  [/\ order h, substrate h = unionf (domain g) (fun a => substrate (Vg g a)) 
  & (forall a, inc a (domain g) -> order_extends (Vg g a) h)].

Definition common_extension_order_axiom g :=
  [/\ order_fam g,
  (forall a b, inc a (domain g) -> inc b (domain g )-> exists c, 
    [/\ inc c (domain g), sub (substrate (Vg g a)) (substrate (Vg g c))
      & sub (substrate (Vg g b)) (substrate (Vg g c))])
  & monotone_order_fam g].
Definition common_worder_axiom g:=
  [/\  worder_fam g,
  (forall a b, inc a (domain g) -> inc b (domain g) -> 
    segmentp (Vg g a) (substrate (Vg g b))
    \/ segmentp (Vg g b) (substrate (Vg g a)))
  & monotone_order_fam g].

(** We first show that we have an ordering that extends [G(i)] *)

Lemma order_merge1 g:
  common_extension_order_axiom g -> common_extension_order g (unionb g).
Proof.
set G := (unionb g); move=> [alo eVVg pVV].
have gu: sgraph G. 
  by move=> t /setUb_hi [x /alo xdg /(order_sgraph xdg)].
set (E:=unionf (domain g) (fun a => substrate (Vg g a))). 
have ur: forall y,inc y E ->  related G y y. 
  rewrite /E=> y yE; move: (setUf_hi yE)=> [x xdg xp].  
  by apply: (setUb_i xdg); apply:(proj42 (alo _ xdg)).
have su: substrate G = E. 
  set_extens x; last by move=> xE; move: (ur _ xE)=> h; substr_tac.
  rewrite /E;case /(substrate_P gu) => [] [y Ju];
      move: (setUf_hi Ju)=>  [z zdg zp]; union_tac;
     move: (alo _ zdg)=> h; substr_tac.
have cov: forall x y, inc x G -> inc y G -> 
    exists u, [/\ inc u (domain g), inc x (Vg g u)& inc y (Vg g u)].
  move=> x y xu yu.
  move: (setUf_hi xu) (setUf_hi yu)=>  [a adg ap][b bdg bp].  
  move: (eVVg _ _ adg bdg)=> [c [cdg sac sbc]].
  move:(pVV _ _ adg cdg sac)(pVV _ _ bdg cdg sbc)=> Vag Vbg.
  move: ap bp; rewrite Vag Vbg /induced_order; aw.
  by move /setI2_P => [p1 _] /setI2_P [p2 _]; exists c.
have oG: order G.
  split => //.
      by hnf; rewrite su.
    rewrite /related => x y z p1 p2.
    move: (cov _ _ p1 p2)=> [c [cdg p1c p2c]].
    move: (alo _ cdg) => or; rewrite /G /related; union_tac; order_tac.
  rewrite /related => x y  p1 p2.
  move: (cov _ _ p1 p2)=> [c [cdg p1c p2c]].
  move: (alo _ cdg)=> or; order_tac.
split=>// a adg;set_extens x => xs.
  apply/setI2_P; split; first by rewrite /G;  union_tac.
  by apply:(sub_graph_coarse_substrate (proj41 (alo _ adg))).
move: (setUb_hi (setI2_1 xs))=> [z zdg zpr].
move: (eVVg _ _ adg zdg)=> [t [tdg sa sz]].
rewrite (pVV _ _ adg tdg sa);  apply/setI2_P;split;last by apply: (setI2_2 xs).
by move: zpr; rewrite(pVV _ _ zdg tdg sz); move/setI2_P => [].
Qed.

(** There is at most one extension *)

Lemma order_merge2 g: common_extension_order_axiom g -> 
  uniqueness (common_extension_order g). 
Proof. 
move => [alo eVVg pVV] h1 h2 c1 c2.
suff: (forall h1 h2, common_extension_order g h1 ->
  common_extension_order g h2 -> sub h1 h2).
  by move=> aux; apply: extensionality; apply: aux.
move => r r' [or sr vr][or' sr' vr'].
move=> x xr.
have ppx:= (proj41 or _ xr).
move:(pr1_sr xr)(pr2_sr xr); rewrite  sr => pxs pys.
move: (setUf_hi pxs) (setUf_hi pys)=> [u udg psu][v vdg qsv].
move:(eVVg _ _ udg vdg)=> [w [wdg wu wv]].
have: (inc x (Vg g w)). 
   rewrite  (vr _ wdg); apply /setI2_i => //;apply/setX_P;split;fprops.
by rewrite  (vr' _ wdg) ; move /setI2_P => [].
Qed.

(** Property (d) implies (c); in this case, the unique extension is the union *)

Lemma order_merge3 g:
  common_worder_axiom g -> common_extension_order_axiom g.
Proof.
move=> [alwo pa pb];split => //.
  by move => w xdg; move: (alwo _ xdg) => [ok _].
move => a b adg bdg;case: (pa _ _ adg bdg); rewrite /segmentp;
  move => [ss _]; [  exists a | exists b]; split=> //.
Qed.

Lemma order_merge4 g: 
  common_worder_axiom g -> common_extension_order g (unionb g).
Proof. by move=> ga; apply: order_merge1; apply: order_merge3. Qed.

Lemma order_merge5 g: common_worder_axiom g -> 
  uniqueness (common_extension_order g). 
Proof. 
move=> ca h1 h2 a1 a2;apply: (order_merge2 (order_merge3 ca) a1 a2). 
Qed.

(** This is the main result *)

Theorem worder_merge g  (G := unionb g):
  common_worder_axiom g -> 
 [/\  (common_extension_order g G),
   worder G,
   (forall a x, inc a (domain g) -> segmentp (Vg g a) x 
     -> segmentp G x),
   (forall a x, inc a (domain g) ->  inc x (substrate (Vg g a)) ->
     segment (Vg g a) x = segment G x)
   & (forall x, segmentp G x ->
     x = substrate G \/ exists2 a, inc a (domain g) & segmentp (Vg g a) x)].
Proof. 
move=> co.
move: (order_merge4 co)=>coe.
move: coe=> [oh sh Vag].   
move: co => [pb pc pd].
have p1: (forall a, inc a (domain g) -> sub (substrate (Vg g a)) (substrate G)).
  by move=> a adg; rewrite sh; move=> t ts; apply: (setUf_i  adg).
have p0 a x y: inc x (substrate (Vg g a)) -> gle G y x -> inc y (substrate G)
   -> inc a (domain g) -> inc y (substrate (Vg g a)).
  move => xs yx ys adg.
  move: (setUf_hi yx) => [u udg Jv].
  case: (pc  _ _ adg udg) => h; first by apply:(proj1 h); substr_tac.
  exact: (proj2 h _ _ xs Jv).
have p2: (forall a, inc a (domain g) -> segmentp G (substrate(Vg g a))).
  move=> a adg;split; first by apply: p1.
  move=> x y xs yx;exact: (p0 a _ _ xs yx (arg1_sr yx) adg).
have p3:(forall a x, inc a (domain g) -> inc x (substrate (Vg g a)) 
    -> segment (Vg g a) x = segment G x).
  move=> a x adg xs; set_extens y => ys; move: (inc_segment ys) => [yx nyx].
    apply /segmentP; split=>//; apply: setUb_i adg  yx.
  apply/segmentP; split => //;rewrite (Vag _ adg);apply/iorder_gle0P => //.
  exact: (p0 a _ _ xs yx (arg1_sr yx) adg).
have p4: (forall a x, inc a (domain g) -> segmentp (Vg g a) x -> 
    segmentp G x).
  move=> a x adg sa; case: (well_ordered_segment (pb _ adg) sa).
    by move=> ->; apply: p2.
  by move=> [y ysV ->]; rewrite (p3 _ _ adg ysV); apply: segment_segment.
have p5: worder G.
  apply:(worder_prop_rev oh) => x xsr [y yx].
  move: (xsr _ yx)=> ysr; rewrite sh in ysr. 
  move: (setUf_hi ysr) => [a adg ysVa].
  set (x1:= x \cap (substrate (Vg g a))).
  have sx1s: (sub x1 (substrate (Vg g a))) by apply: subsetI2r.
  have nx1: nonempty x1 by exists y; apply: setI2_i.  
  move: (worder_prop (pb _ adg) sx1s nx1)=> [z zs zle].
  have zx: inc z x by apply: (setI2_1 zs).
  have zVa: inc z (substrate (Vg g a))  by apply: (setI2_2 zs).  
  exists z => // t tx.
  move: (xsr _ tx); rewrite sh => tu; move: (setUf_hi tu)=> [b bdg bV]. 
  have aux: inc t (substrate (Vg g a)) -> gle G z t.
    move=> hyp.
    by move:(zle _ (setI2_i tx hyp));rewrite (Vag _ adg) => /iorder_gle1. 
  case: (pc _ _ adg bdg); move => [p p']; first by apply: (aux (p _ bV)).
  move: (p _ zVa)=> zVb.
  case: (total_order_pr2 (worder_total (pb _ bdg)) bV zVb).
    move=> [tz ntz]; apply: (aux (p' _ _ zVa tz)).
  rewrite Vag // => h; exact:(iorder_gle1 h).
split => //.
move=> x seg.
case: (well_ordered_segment p5 seg); [ by left | move=>[y ysr ->]; right ].
rewrite sh in ysr; move: (setUf_hi ysr)=> [a adg ap]; ex_tac.
rewrite -(p3 _  _ adg ap); apply: segment_segment (proj1 (pb _ adg)).
Qed.

(** Isomorphos on segments *)


Definition seg_order r x := (induced_order r (segment r x)).

Lemma seg_order_osr r x: order r ->
  order_on (seg_order r x)  (segment r x).
Proof. move => or; exact: (iorder_osr or (@sub_segment r x)). Qed.

Lemma seg_order_wor r x: worder r ->
  worder (seg_order r x).
Proof. move => or; exact: (induced_wor or (@sub_segment r x)). Qed.

Lemma seg_order_wosr r x: worder r ->
  worder_on (seg_order r x) (segment r x).
Proof. 
move => wor;split; first exact:(seg_order_wor x wor).
exact: (proj2 (seg_order_osr x (proj1 wor))).
Qed.



Lemma seg_order_trans r a b: order r -> glt r a  b ->
  seg_order (seg_order r b) a = seg_order r a.
Proof.
move => or ltab; move: (segment_monotone or (proj1 ltab)) => ss.
by rewrite /seg_order (segment_induced or ltab) iorder_trans.
Qed.

Lemma isomorphism_to_morphism f r r' x
  (F := (Lf (Vf f) (substrate r) (substrate r'))):
  order r -> order r' ->
  sub x (substrate r') ->
  order_isomorphism f r (induced_order r' x) ->
  (order_morphism F r r'  /\ Imf F = x).
Proof.
move=> oa ob  sxa [ou ov' [bf sz tz] siz].
rewrite iorder_sr // in tz.
have fh: function f by fct_tac.
have ta1: lf_axiom (Vf f) (substrate r) (substrate r').
  move=> t tu; apply: sxa; Wtac.
have fF: function F by apply: lf_function.
have rg: Imf F = x.
  rewrite - tz; set_extens t. 
    move/(Imf_P fF); rewrite /F; aw; move => [a asf ->]; rewrite LfV//; Wtac.
  move/(proj2 (proj2 bf)) => [u us ->].
  by rewrite sz in us;apply/(Imf_P fF); rewrite /F; aw;  ex_tac; rewrite LfV.
split =>//; split => //; first by rewrite /F;split;aw.
rewrite /F;hnf; aw;move  => x1 x2 x1s x2s; rewrite !LfV//.
rewrite - sz in x1s x2s; apply: (iff_trans (siz _ _ x1s x2s)).
split; first by move/iorder_gle1. 
move => hh; apply/iorder_gle0P => //; rewrite - tz; Wtac.
Qed.

Definition iso_seg_mor r1 r2 f :=
   segmentp r2 (Imf f) /\ order_morphism f r1 r2.

Definition iso_seg_iso r1 r2 f :=
 segmentp r2 (target f) /\ order_isomorphism f r1 (induced_order r2 (target f)).


Lemma iso_seg_mor_prop r1 r2 f:
  order r1 -> order r2 -> iso_seg_mor r1 r2 f ->
  iso_seg_iso r1 r2 (restriction_to_image f).
Proof.
move => or1 or2 [ha hb].
move:(proj1 ha) => hc; hnf.
move:(order_morphism_fi hb) => fi.
move: (restriction_to_image_fb fi) => bb.
have tr: target (restriction_to_image f) = Imf f.
  by rewrite /restriction_to_image/restriction2; aw.
have sr: source (restriction_to_image f) = source f.
  by rewrite /restriction_to_image/restriction2; aw.
move:(iorder_osr or2 hc) =>[qa qb].
move: hb =>[_ _ [ff sf tf] isf].
rewrite tr; split => //; split => //.
  by hnf; rewrite sr tr sf qb.
have H: restriction2_axioms f (source f) (Imf f).
 by split; fprops; apply: Imf_Starget.
hnf; rewrite sr => x y xsr ysr.
rewrite restriction2_V // restriction2_V //.
apply: (iff_trans (isf x y xsr ysr)); split.
  by move => h;apply/iorder_gle0P => //; apply:Imf_i.
by move/iorder_gle1.
Qed.

Lemma iso_seg_iso_prop r1 r2 f:
  order r1 -> order r2 -> iso_seg_iso r1 r2 f ->
  iso_seg_mor r1 r2(Lf (Vf f) (substrate r1) (substrate r2)).
Proof.
move => or1 or2 [ha hb]; move:(proj1 ha) => hc.
move: (isomorphism_to_morphism or1 or2 hc hb)=> [qa qb]; split => //; ue.
Qed.
                                            
  
Section IsoSeg.

Variables r1 r2: Set.
Hypothesis (wor1: worder r1) (wor2: worder r2).
  
Definition iso_graph  g :=
  [/\ sgraph g, segmentp r1 (domain g), segmentp r2 (range g) &
     forall a b c d, inc (J a b) g -> inc (J c d) g -> 
     (gle r1 a c <-> gle r2 b d)].

Definition iso_graphs  :=
   Zo (\Po ((substrate r1) \times (substrate r2))) iso_graph.


Lemma  iso_graph_inj1 g a b c: inc g iso_graphs ->
   inc (J a c) g -> inc (J b c) g -> a = b.
Proof.
move =>/Zo_P[/setP_P h [pa pb pc pd]] i1 i2.
move:(proj1 wor1) (proj1 wor2) => or1 or2.
move: (h _ i1) (h _ i2) => /setXp_P [asr csr] /setXp_P [bsr _].
have cc:  gle r2 c c by order_tac.
move/(pd a c b c i1 i2): (cc) => l1.
move/(pd b c a c i2 i1): cc => l2.
order_tac.
Qed.

Lemma  iso_graph_inj2 g a b c: inc g iso_graphs ->
   inc (J c a) g -> inc (J c b) g -> a = b.
Proof.
move =>/Zo_P[/setP_P h [pa pb pc pd]] i1 i2.
move:(proj1 wor1) (proj1 wor2) => or1 or2.
move: (h _ i1) (h _ i2) => /setXp_P [csr asr] /setXp_P [_ bsr].
have cc:  gle r1 c c by order_tac.
move/(pd _ _ _ _ i1 i2): (cc) => l1.
move/(pd _ _ _ _ i2 i1): cc => l2.
order_tac.
Qed.
  
Lemma iso_graph_mon1 g a b c: inc g iso_graphs ->
   inc (J a b) g -> glt r2 c b ->
   exists2 d, glt r1 d a & inc (J d c) g.
Proof.
move => gi qa [qb qc].
move: (gi) => /Zo_P[/setP_P h [pa pb pc pd]].
have br: inc b (range g) by apply/funI_P; ex_tac; aw.
move:(proj2 pc _ _ br qb) =>/funI_P [db dg dv].
have ph: inc (J (P db) c) g by  rewrite dv (pa _ dg).
exists (P db) => //; split; first by apply/ (pd _ _ _ _ ph qa).
move => bad. rewrite bad in ph.
case: qc; exact:  (iso_graph_inj2 gi ph qa).
Qed.
 
  
Lemma iso_graph_mon2 g a b c: inc g iso_graphs ->
   inc (J a b) g -> glt r1 c a ->
   exists2 d, glt r2 d b & inc (J c d) g.
Proof.
move => gi qa [qb qc].
move: (gi) => /Zo_P[/setP_P h [pa pb pc pd]].
have br: inc a (domain g) by apply/funI_P; ex_tac; aw.
move:(proj2 pb _ _ br qb) =>/funI_P [db dg dv].
have ph: inc (J c (Q db)) g by  rewrite dv (pa _ dg).
exists (Q db) => //; split; first by apply/ (pd _ _ _ _ ph qa).
move => bad. rewrite bad in ph.
case: qc; exact:(iso_graph_inj1 gi ph qa).
Qed.

Lemma iso_graph_mon4 g1 g2 a b c d:
  inc g1 iso_graphs -> inc g2 iso_graphs ->
  inc (J a b) g1 -> inc (J c d) g2 ->
  (gle r1 a c <-> gle r2 b d).
Proof.
move: g1 g2 a b c d.
move:(proj1 wor1) (proj1 wor2) => or1 or2.
suff H: forall g1 g2 a b c d, inc g1 iso_graphs -> inc g2 iso_graphs ->
  inc (J a b) g1 -> inc (J c d) g2 ->
  gle r1 a c -> glt r2 d b -> False.
  move => g1 g2 a b c d g1i g2i ha hb. 
  move: (g2i) => /Zo_S /setP_P pp.
  move/setXp_P:(pp _ hb) =>[csr dsr].
  move: (g1i) => /Zo_S /setP_P pp1.
  move/setXp_P:(pp1 _ ha) =>[asr bsr].
  split => le1.
     case : (total_order_pr2 (worder_total wor2) dsr bsr) => // gt.
     case: (H _ _ _ _ _ _ g1i g2i ha hb le1 gt).
  case : (total_order_pr2 (worder_total wor1) csr asr) => // gt.
  case: (equal_or_not b d ) => ebd; last first.
    case:(H  g2 g1 c d a b g2i g1i hb ha (proj1 gt) (conj le1 ebd)).
  rewrite - ebd in hb.
  set Z := Zo (substrate r1)
    (fun c1 => exists a1 b1, [/\ inc (J a1 b1) g1,  inc (J c1 b1) g2 &
                                        glt r1 c1 a1]).
  have nez: nonempty Z.
     exists c; apply: Zo_i; [ by order_tac |   by exists a,b].
  have sz: sub Z (substrate r1) by apply: Zo_S.
  apply: False_ind.
  clear a b c d asr bsr csr dsr ha hb le1 gt ebd.
  move: (worder_prop wor1 sz nez) =>[c /Zo_hi [a [b [abg cbg lt1]]] cm].
  move: (iso_graph_mon2 g1i abg lt1) =>[d lt2 cdg].
  move: (iso_graph_mon1 g2i cbg lt2) =>[e lt3 edg].
  have /cm mt2: inc e Z.
    apply: Zo_i. order_tac. exists c, d. split => //.
  order_tac.
move => g1 g2 a b c d g1i g2i abg cdg le1 lt1.
set Z := Zo (substrate r2)
    (fun d1 => exists a1 b1 c1, [/\ inc (J a1 b1) g1, inc (J c1 d1) g2,
     gle r1 a1 c1&  glt r2 d1 b1]).
have neZ: nonempty Z.
   exists d; apply: Zo_i; [ by order_tac |  by exists a,b,c].
have sz: sub Z (substrate r2) by apply: Zo_S.
clear a b c d abg cdg le1 lt1.
move: (worder_prop wor2 sz neZ) =>[d /Zo_hi [a [b [c [abg cdg le1 lt1]]]] cm].
move: (iso_graph_mon1 g1i abg lt1) =>[e hc lt3].
have lt4: glt r1 e c by order_tac.
move:(iso_graph_mon2 g2i cdg lt4) =>[f lt5 hd ].
have /cm fz: inc f Z.
   apply: Zo_i; first by order_tac.
   exists e,d,e; split => //; order_tac.
   by move /setP_P: (Zo_S g2i) => h; move:(h _ hd) => /setXp_P [].
order_tac.
Qed.

Lemma iso_graph_stableU: 
  inc (union (iso_graphs)) (iso_graphs).
Proof.
set U := union (iso_graphs).
have ha x: inc x U -> inc x  ((substrate r1) \times (substrate r2)).
  by  move => /setU_P [y ya /Zo_S/setP_P]; apply.
have hb x: inc x U -> pairp x by move => /ha/setX_P; case.
apply: Zo_i; first by apply /setP_P.  
have q1: sgraph U.
  by move => t/setU_P [y ya /Zo_hi [gy _ _  _]]; apply: gy.
have q4: segmentp r1 (domain U).
  rewrite domain_setU; apply: setU_segment => t/funI_P[ x xi ->].
  by case/Zo_hi: xi.
have q5: segmentp r2 (range U).
  rewrite range_setU; apply: setU_segment => t/funI_P[ x xi ->].
  by case/Zo_hi: xi.
split => //.
move => a b c d /setU_P [x iax gx] /setU_P [y iby  gy].
exact: (iso_graph_mon4 gx gy iax iby).
Qed.

Lemma iso_graph_maxU (U :=  (union (iso_graphs))):
  domain U = substrate r1 \/ range U = substrate r2. 
Proof.
move:(proj1 wor1) (proj1 wor2) => or1 or2.
case: (equal_or_not (domain U) (substrate r1)) => ha; first by left.
case: (equal_or_not (range U) (substrate r2)) => hb; first by right.
move:iso_graph_stableU; rewrite -/U => Ud.
move/Zo_P: (Ud) =>[/setP_P sU [Ua Ub Uc Ue]].
set Xa := substrate r1 -s (domain U).
set Xb := substrate r2 -s (range U).
have Xas: sub Xa (substrate r1) by apply: sub_setC.
have Xbs: sub Xb (substrate r2) by apply: sub_setC.
have neXa: (nonempty Xa) by apply: setC_ne; split => //; case: Ub.
have neXb: (nonempty Xb) by apply: setC_ne; split => //; case: Uc.
move:(worder_prop wor1 Xas neXa) =>[a /setC_P[asr anX] al].
move:(worder_prop wor2 Xbs neXb) =>[b /setC_P[bsr bnX] bl].
set g := U +s1 (J a b).
have jabg: inc (J a b) g by apply: setU1_1.
suff: (inc g iso_graphs).
  move => bad; move: (setU_s1 bad); rewrite -/U => /domain_S sg.
  case: anX; exact: (sg _ (domain_i jabg)).
move: Ub Uc =>[qa qb] [qc qd].
have rre: sub g (substrate r1 \times substrate r2).
  by move  => t /setU1_P; case; [ apply: sU |  move => ->; apply:setXp_i].
  have ra:  sgraph g. move => t/setU1_P; case; [ fprops | move ->; fprops].
have rb:  segmentp r1 (domain g).
  rewrite /g domain_setU1; split; first by apply:setU1_sub.
  move => x y /setU1_P xs xy; case: xs => xdu.
     apply:setU1_r; apply:(qb _ _ xdu xy).
  case: (inc_or_not y (domain U)) => ydU; first by apply: setU1_r.
  have yXa: inc y Xa by apply/setC_P; split => //; order_tac.
  move: (al _ yXa) => lay; rewrite xdu in xy.
  have -> : y = a by order_tac.
  fprops.
have  rc: segmentp r2 (range g).
  rewrite /g range_setU1; split; first by apply:setU1_sub.
  move => x y /setU1_P xs xy; case: xs => xdu.
     apply:setU1_r; apply:(qd _ _ xdu xy).
  case: (inc_or_not y (range U)) => ydU; first by apply: setU1_r.
  have yXa: inc y Xb by apply/setC_P; split => //; order_tac.
  move: (bl _ yXa) => lay; rewrite xdu in xy.
  have -> : y = b by order_tac.
  fprops.
apply:Zo_i; [ by apply/setP_P | split => // u v c d p1g p2g].
case/setU1_P: p1g => Ha; case/setU1_P:p2g => Hb.
+ by apply: Ue.
+ move: (pr12_def Hb) =>[-> ->].
  move:(domain_i Ha)  (range_i Ha) => ud vr.
  move:(qa _ ud) (qc _ vr) => usr vsr.
  split => le1.
    case:(total_order_pr2 (worder_total wor2) bsr vsr) => // ltbv.
    case:bnX; exact:(qd v b  vr (proj1 ltbv)).
  case:(total_order_pr2 (worder_total wor1) asr usr) => // ltbv.
  case:anX; exact:(qb _ _   ud (proj1 ltbv)).
+ move: (pr12_def Ha) =>[-> ->]; split => le1.
    case: anX; exact: (qb _ _ (domain_i Hb) le1).
  case: bnX; exact: (qd _ _ (range_i Hb) le1).
+ move: (pr12_def Hb) =>[-> ->]; move: (pr12_def Ha) =>[-> ->].
  by split => _; order_tac.  
Qed.

Definition iso_seg_fun := let g := union  iso_graphs in 
   triple (domain g) (range g) g.


Lemma iso_graph_prop (f := iso_seg_fun):
  [/\ segmentp r1 (source f), segmentp r2 (target f),
    source f= substrate r1 \/ target f = substrate r2 &
    order_isomorphism f (induced_order r1 (source f))
        (induced_order r2 (target f))].
Proof.
move: iso_graph_stableU iso_graph_maxU.
rewrite /f/iso_seg_fun; aw; set U := union _ => gU alt.
move: (gU) => /Zo_P[/setP_P s1][qa qb qc qd]; split => //.
move: (iorder_osr (proj1 wor1) (proj1 qb)) =>[ora sra].
move: (iorder_osr (proj1 wor2) (proj1 qc)) =>[orb srb].
have ff: function (triple (domain U) (range U) U).
   apply: function_pr => //; split => // u v uU vU sp1.
   move: (qa _ uU) (qa _ vU) => sa sb.
   apply: pair_exten => //.
   by move: uU vU; rewrite -{1} sa - {1} sb - sp1; apply: iso_graph_inj2.
have fv z: inc z U -> Q z = Vg U (P z).
  move => zU.
  apply: select_uniq.
  + move => a b /funI_P [ap apu ->] eqa /funI_P [bp bpu ->] eqb.
    exact:(iso_graph_inj2 gU eqa eqb).
  + apply/funI_P; ex_tac.
  + by rewrite (qa _ zU).
have bf: bijection (triple (domain U) (range U) U).
  split; saw.
    move => u v uU vU //; rewrite /Vf; aw.
    move/funI_P: uU =>[pa pau pav]. 
    move/funI_P: vU =>[pb pbu pbv].
    rewrite pav pbv - (fv _ pau) - (fv _ pbu) => eq1.
    move:(qa _ pau)(qa _ pbu) => p1 p2.
    move: pau pbu; rewrite -{1} p1 -{1} p2 - pav - pbv - eq1 => ia ib.
    exact (iso_graph_inj1 gU ia ib).
  move => y /funI_P [z zU ->].
  exists (P z); first by apply/funI_P; ex_tac.
  by rewrite/Vf; aw; apply: fv.
split => //; first by rewrite sra srb; saw. 
move => u v; aw => ud vd; rewrite /Vf; aw.
move/funI_P:(ud) =>[up upU upv].
move/funI_P:(vd) =>[vp vpU vpv].
rewrite{2} upv - (fv _ upU) {2} vpv - (fv _ vpU).
have ur: inc (Q up) (range U)  by apply/funI_P; exists up.
have vr: inc (Q vp) (range U)  by apply/funI_P; exists vp.
move:(qa _ upU)(qa _ vpU) => p1 p2.
move: (upU)(vpU); rewrite -{1} p1 - {1} p2 => sa sb.
move:(qd (P up) (Q up) (P vp) (Q vp) sa sb); rewrite - upv - vpv => mn.
split.
  by move/iorder_gle1 => /mn le; apply/iorder_gleP.
by move/iorder_gle1 => /mn le; apply/iorder_gleP.
Qed.

End IsoSeg.

Lemma isomorphism_worder_exists_v1 r r' (f := iso_seg_fun r r'):
  worder r -> worder r' ->
  iso_seg_iso r r' f \/ iso_seg_iso r' r (inverse_fun f).
Proof.
move => wo1 wo2.
move:(proj1 wo1) (proj1 wo2) => o1 o2.
move:(iso_graph_prop wo1 wo2) => /=.
move => [ha hb hc hd]; case: hc => hc; [left | right].
  by move: hd; rewrite hc (iorder_substrate o1) => hd.
move: hd; rewrite hc (iorder_substrate o2) => hd.
by saw;  apply: inverse_order_is.
Qed.
  

Lemma isomorphism_worder_exists_v2 r r': worder r -> worder r' ->
  (exists f, iso_seg_mor r r' f) \/ (exists f, iso_seg_mor r' r f).
Proof.
move => wo1 wo2.
move:(proj1 wo1) (proj1 wo2) => o1 o2.
case: (isomorphism_worder_exists_v1 wo1 wo2) => iso.
  by left; move:(iso_seg_iso_prop o1 o2 iso); set g := Lf _ _ _ => h; exists g.
by right;move:(iso_seg_iso_prop o2 o1 iso); set g := Lf _ _ _ => h; exists g.
Qed.


Lemma isomorphism_worder_sub r E (r' := induced_order r E):
  worder r -> sub E (substrate r) ->
  iso_seg_iso r' r (iso_seg_fun r' r).                                   
Proof.
move => wor sr; move: (proj1 wor) => or.
move: (induced_wor wor sr) => wor'.
move: (iorder_sr (proj1 wor) sr) => sr'.
move: (iso_graph_prop wor' wor).
set f := iso_seg_fun _ _;move => [[sa sb] st di].
rewrite sr' in sa.
rewrite (iorder_trans _ sa) => is1; split => //.
case: di => qa; first by  move: is1; rewrite qa sr'. 
move: is1; rewrite qa (iorder_substrate or).
move => ts1; move:(ts1)  =>[or1 _ [[injf [ff srjf]] sf tf] fi].
set X := Zo (source f) (fun x => glt r x (Vf f x)).
case: (emptyset_dichot X) => xe; last first.
  have Xsr: sub X (substrate r) by move => t /Zo_S/sa/sr.
  move: (worder_prop wor Xsr xe) => [a /Zo_P[asr [le1 ne1]] ap].
  move :(arg1_sr le1) => gasr.
  have atf: inc a (target f) by ue.
  move: (srjf  a atf) => [b bsf bv].
  move: le1; rewrite {1} bv.
  move/(fi b a  bsf asr) => /iorder_gleP [ra rb rc].
  have  aux: a <> b by  move => bb; case: ne1; rewrite {2} bb.
  have /ap le2: inc b X.
    apply: (Zo_i bsf); split => //; try ue.
  by move: (not_le_gt or rc (conj le2 aux)).
have eq2: (source f) = E.
  apply: extensionality => // a tE; ex_middle bad.
  move: (sr _ tE) => asr.
  have tsg: inc a (target f) by ue.
  move: (srjf _ tsg) => [b bsf bv].
  have bE: inc b E by apply: sa.
  move:(sr _ bE) => bsr.
  case: (total_order_pr2 (worder_total wor)  bsr asr) => h.
    by empty_tac1 b; apply:(Zo_i  bsf); rewrite - bv.
  have aux: gle (induced_order r E) a b.
    by apply/iorder_gleP.
  exact:(sb b a bsf aux).  
by move: ts1; rewrite /r' eq2.
Qed.


Lemma fsincr_wor_prop  r X f: worder r -> sub X (substrate r) ->
  order_isomorphism f r (induced_order r X) ->
  forall x, inc x (substrate r) -> gle r x (Vf f x).      
Proof.
move => wor ser [_ _ [/proj1/proj1 bf sf tf] ff].
case: (worder_prop2 (fun x => gle r x (Vf f x)) wor) => // - [a [asr fa ap]].
case: fa.
have H t: inc t (source f) -> inc (Vf f t) X.
  rewrite - (iorder_sr (proj1 wor) ser) - tf => xs. Wtac.
have asf: inc a (source f) by ue.
have bX := H _ asf.
case: (total_order_pr2 (worder_total wor) (ser _ bX) asr) => // /ap aux.
move:(ser _ bX);rewrite - sf => bsf; move: (H _ bsf) => vvX.
by apply/(ff a (Vf f a) asf bsf); apply/iorder_gleP. 
Qed.


(** **  EIII-2-2 The principle of transfinite induction *)

(** Let [O(x)] and [C(x)] be  the set of all elements less than (resp. less or 
equal than) [x]. These are segments, and [C(x)] is the union of [O(x)] and the 
singleton [x]. In a well-ordered set every segment [S] is of the form [C(x)] or 
the union of all segments of [S], distinct from [S]. 
Consequence: a set of segments, stable by union, 
and stable by the mapping [O->C] contains all segments.*)

Section TransfinitePrinciple.
Variables r s: Set.
Hypothesis wor: worder r.
Hypothesis u_stable: forall s', sub s' s -> inc (union s') s.
Hypothesis adj_stable:
 (forall x, inc x (substrate r) -> inc (segment r x) s -> inc (segmentc r x) s).

Lemma transfinite_principle1 x: segmentp r x -> inc x s.
Proof.
move=> sx.
have or: order r by case: wor.
move: (segments_worder wor) => woi.
set (cs:=  (segments r) -s s).
case: (emptyset_dichot cs) => necs.
  have nc: (~ inc x cs) by rewrite necs; case; case. 
  move: sx => /(inc_segmentsP wor) sx.
  apply: (nin_setC sx nc).
have scs: sub cs (segments r) by rewrite /cs; apply: sub_setC.
move:(proj2 (sub_osr (segments r))) => sr1.
move: (scs); rewrite - {1} sr1 => src1.
move:(worder_prop woi src1 necs) => [y ycs hyp].
move/setC_P:(ycs) => [yssr nys].
have ysr:(sub y (substrate r)) by apply: sub_segments=>//.
have woi': worder (induced_order r y) by apply: induced_wor. 
case: (p_or_not_p (exists a, greatest_induced r y a)).
  move=> [a []]; rewrite iorder_sr // => [ay pa].
  move: (ysr _ ay)=> asr.
  have ysc: (y = segmentc r a).
    set_extens t => ts; first by move: (iorder_gle1 (pa _ ts)) => /segmentcP.
    move: ts => /segmentcP ta. 
    move: yssr => /(inc_segmentsP wor) [_ aux]; apply: (aux _ _ ay ta).
  case: (p_or_not_p (inc (segment r a) cs))=> h.
      move: (hyp _ h) => /sub_gleP [_ _ ysa].
      case: (not_in_segment (ysa _ ay)).
  have p1: (inc (segment r a)  (segments r)) by apply: segment_insetof. 
  by case: nys; rewrite ysc; apply: adj_stable =>//; apply: (nin_setC p1 h).
move=> nge.
have aux: (forall x, ~ greatest_induced r y x). 
  by move=> b ngeb; case: nge; exists b.
move: (union_segments (worder_total woi'))=> [unm _]. 
move: (unm aux); rewrite iorder_sr // => us; clear aux unm.
case: nys; rewrite -us; apply: u_stable.
move => z /funI_P [u uy zv].
case: (inc_or_not z cs) => zcs. 
  move: (hyp _ zcs) => /sub_gleP [_ _ yz].
  move: uy; rewrite iorder_sr // => uy; move: (yz _ uy).
  by rewrite zv=>/not_in_segment.
have siu: (segmentp (induced_order r y) z). 
  rewrite zv; apply: segment_segment; fprops. 
have zsr: (inc z (segments r)). 
  apply /(inc_segmentsP wor).
  move: yssr => /(inc_segmentsP wor)  yssr.
  apply: (subsegment_segment or yssr siu). 
by apply: (nin_setC zsr zcs).
Qed.

Lemma transfinite_principle2: inc (substrate r) s.
Proof. 
apply: (transfinite_principle1); apply: substrate_segment; fprops.
Qed.

End TransfinitePrinciple.


(** Two proofs of the transfinite principle; either by application of the
 previous lemma or direct proof (in ssete2) *)

Theorem transfinite_principle r (p:property) (E:= substrate r):
  worder r ->  
  (forall x, inc x E -> (forall y, inc y E -> glt r y x -> p y) -> p x) -> 
  forall x, inc x E -> p x.
Proof.
move => wor hyp x xsr.
have or: order r by case: wor.
set (s:= Zo (segments r)(fun z => forall y, inc y z -> p y)).
have alseg: forall x, inc x s -> segmentp r x. 
   by move=> t /Zo_P [] /(inc_segmentsP wor).
have su:forall s', sub s' s -> inc (union s') s.
  move=> s' s's; apply /Zo_P; split.
    apply /(inc_segmentsP wor);apply: setU_segment. 
    by move=> t ts'; apply: alseg; apply: s's.
  move=> y yu; move: (setU_hi yu)=> [v yv vs]. 
  by move: (s's _ vs) => /Zo_hi; apply.
have seg: forall x, inc x (substrate r) -> inc (segment r x) s -> 
      inc (segmentc r x) s.
  move=> y ysr yxs; rewrite /s; apply: Zo_i.
  apply /(inc_segmentsP wor); apply: (segmentc_segment _ or).
  move: yxs => /Zo_P [p1 p2].
  move=> z; rewrite - segmentc_pr //; case /setU1_P; first by apply: p2.
  by move=> ->; apply: hyp =>// t _ /segmentP ty; apply: p2. 
exact: (Zo_hi (transfinite_principle2 wor su seg)).
Qed.


(** Let [r] be a well-ordering, [x] in the substrate, [S(x)] the segment with 
   endpoint [x], and [g] a function, whose source contains [S(x)]. 
   We define [gx] to be the restriction of [g] to [Sx];
   and study some properties. *)


Definition fgraph_to_fun f:= triple (domain f) (range f) f.

Lemma fgraph_to_fun_ev f x: Vf (fgraph_to_fun f) x = Vg f x.
Proof. by rewrite /Vf/fgraph_to_fun; aw. Qed.

Lemma fgraph_to_fun_source f: source (fgraph_to_fun f) = domain f.
Proof. by rewrite /fgraph_to_fun; aw.  Qed.

Lemma fgraph_to_fun_fs f: fgraph f -> surjection (fgraph_to_fun f). 
Proof.
move => fgf.
have ff: function (fgraph_to_fun f) by apply: function_pr.
apply:(surjective_pr5 ff); rewrite /fgraph_to_fun;aw.
by move => y /(range_gP fgf) [x xdf ->]; ex_tac; apply:fdomain_pr1.
Qed.

Lemma fgraph_to_fun_restr f s:
   function f -> sub s (source f) ->
   restriction1 f s =  fgraph_to_fun (restr (graph f) s).
Proof.
move => ha hb; apply:function_exten4.
- by rewrite/restriction1 fgraph_to_fun_source; aw.
- by apply: restriction1_fs.
- apply:fgraph_to_fun_fs; fprops.
- rewrite{1}/restriction1; aw => x xs.
  by rewrite (restriction1_V ha hb xs) fgraph_to_fun_ev LgV.
Qed.

(** A function [f] is defined by transfinite induction by [p] if [f(x)] is 
 [p(fx)], where [fx] is as above. It exists, its graph is unique. 
 The value [f(x)] is in a set [F] if, for all [g] whose source is a segment and
 target is a subset of [F],  [p(g)] is in [F]. We start with some uniqueness 
 properties *)

Definition transfinite_def r (T: fterm) f :=
  [/\ surjection f, source f = substrate r &
  forall x, inc x (substrate r) -> Vf f x = T (restriction1 f (segment r x))].

Definition transfiniteg_def r (T: fterm) f :=
  [/\ fgraph f, domain f = substrate r &
  forall x, inc x (substrate r) -> Vg f x = T (restr f (segment r x))].

Lemma transfinite_def_prop1 r T f:
  transfiniteg_def r T f <->
  transfinite_def r (T \o graph)  (fgraph_to_fun f).
Proof.
split.
  move => [ha hb hc]; split.
  - by apply:fgraph_to_fun_fs.
  - by rewrite fgraph_to_fun_source.
  - move => x xsr; rewrite fgraph_to_fun_ev (hc _ xsr).
    by rewrite /restriction1/fgraph_to_fun/=; aw.
move => [[ff _] hb hc]; split.
- by move: (proj32 ff); rewrite /fgraph_to_fun; aw.
- by rewrite - hb; rewrite /fgraph_to_fun; aw.
- move => x xsr. 
  move: (hc x xsr); rewrite fgraph_to_fun_ev /restriction1/fgraph_to_fun /=.
  by aw.
Qed.


Lemma transfinite_def_prop2 r T f:
  transfinite_def r T f ->
  transfiniteg_def r (T \o fgraph_to_fun)  (graph f).
Proof.
move => [[ff sjf] hb hc]; split.
- exact: (function_fgraph ff).
- by rewrite domain_fg.
- move => x xsr; rewrite -/(Vf _ _) (hc _ xsr)  fgraph_to_fun_restr //.
  by rewrite hb; apply: sub_segment.
Qed.

Lemma transfiniteg_unique r T : worder r -> 
  uniqueness (transfiniteg_def r T).
Proof.
move=> wo f f' [fgf df fv] [fgf' df' fv'].
case:(worder_prop2 (fun t => Vg f t = Vg f' t) wo) => hyp.
  by apply: fgraph_exten => //; [ ue | move => t ts /=]; apply: hyp; ue.
move:hyp => [a [asr h zp]]; case:h.
rewrite (fv _ asr) (fv' _ asr); congr T; apply: restr_exten => t/segmentP lta.
by apply: zp.
Qed.

Lemma transfinite_unique r T : worder r -> 
  uniqueness (transfinite_def r T).
Proof.
move => wor f g fp gp.
move: (transfinite_def_prop2 fp) (transfinite_def_prop2 gp) => fp' gp'.
move:(transfiniteg_unique wor fp' gp') => sgr.
move:(proj31 fp)(proj31 gp) => sf sg; move: (proj1 sf)(proj1 sg) => ff fg.
apply: (function_exten1 ff fg sgr).
by rewrite - (surjective_pr0 sf) - (surjective_pr0 sg) (ImfE ff) (ImfE fg) sgr.
Qed.


(** Existence follows from two extension properties *)


Lemma transfinite_aux2 r T s (tdf: fterm) : worder r ->
  (alls s (segmentp r)) ->
  (forall z, inc z s ->  transfiniteg_def (induced_order r z) T (tdf z)) ->
  let f := (unionf s tdf) in
  transfiniteg_def (induced_order r (union s)) T f.
Proof. 
move=> wo alseg altd.
set f := unionf s tdf.
have or := proj1 wo.
have prop1 y: inc y s -> substrate (induced_order r y) = y.
  move => /alseg h; apply:(iorder_sr or(sub_segment1 h)).
have prop2 y: inc y s -> domain (tdf y) = y.
  by move => ys; rewrite (proj32 (altd _ ys)) (prop1 _ ys).
have sgf: sgraph f by move => t /setUf_P [y /altd [[ha _] _ _] td]; apply: ha.
have df: domain f = union s.
  set_extens t.
    move /(domainP sgf) => [y /setUf_P [z zs /domain_i]].
    rewrite (prop2 _ zs) => tz; union_tac.
  move => /setU_P [y ty ys]; apply/(domainP sgf).
  move: ty; rewrite - (prop2 _ ys) => /(domainP (proj1 (proj31 (altd _ ys)))).    move => [z za]; exists z; apply/setUf_P; ex_tac.
have su: sub (union s) (substrate r). 
  by move=> v /setU_hi [i vi /alseg /proj1]; apply. 
have sr1:= (iorder_sr or su).
have hb0 i j x: inc i s -> inc j s ->  inc x i -> inc x j -> sub i j ->
  Vg (tdf i) x = Vg (tdf j) x.
  move => ins jns xi xj sij.
  suff: (tdf i) = restr (tdf j) i by  move ->; rewrite LgV.
  have seg1 := (alseg _ ins); have seg2 := (alseg _ jns).
  have sjr:=  proj1 seg2.
  have sir:= sub_trans sij sjr. 
  have iv: i = substrate (induced_order r i) by rewrite iorder_sr.
  have woi: worder (induced_order r i) by  apply: induced_wor.
  apply: (transfiniteg_unique woi (altd i ins)).
  split;[apply: restr_fgraph |  by rewrite restr_d | rewrite - iv => t ti].
  have tj := (sij _ ti).
  move:(tj); rewrite - {1}(iorder_sr or sjr) => tsj.
  move:(altd j jns) => [ha hv hc].
  rewrite (restr_ev _ ti) (hc _ tsj).
  rewrite (segment_induced_a seg2 tj).
  rewrite (segment_induced_a  seg1 ti) double_restr //.
  by move => u /(lt_in_segment2 seg1 ti). 
have hb i j x: inc i s -> inc j s -> inc x i -> inc x j -> 
  Vg (tdf i) x = Vg (tdf j) x.
  move=> ins jns x1 x2.
  move: (alseg _ ins) (alseg _ jns) (altd _ ins) (altd _ jns)=> si sj ti tj.
  case: (segment_dichot_sub wo si sj) => sij; first by apply: hb0.
  by symmetry; apply: hb0.
have fgf: fgraph f.
  split => // x y /setUf_P [x' x's x'v] /setUf_P [y' y's y'v] eq.
  rewrite (in_graph_V (proj31 (altd _ x's)) x'v).
  rewrite (in_graph_V (proj31 (altd _ y's)) y'v) - eq (hb _ _ _ x's y's) //.
    by move:(domain_i1 x'v); rewrite prop2.
  by move:(domain_i1 y'v); rewrite eq  prop2.
have fv i x : inc x i -> inc i s ->  Vg f x = Vg (tdf i) x.
  move => xi ins; suff: inc (J x (Vg (tdf i) x)) f by  move/(pr2_V fgf); aw.
  move:(altd _ ins) => [g1 d1 _].
  by apply/setUf_P; ex_tac; apply: (fdomain_pr1 g1); rewrite prop2.
split => //; first  by rewrite sr1 df.
rewrite sr1 => x xu;move: (xu)=>/setU_P [i xi ins]; rewrite (fv _ _ xi ins).
rewrite (proj33 (altd _ ins)) ?(prop1 _ ins) //; congr T.
rewrite  (segment_induced_a (alseg _ ins) xi).
rewrite (segment_induced_a (setU_segment alseg) xu).
apply: restr_exten => t /(lt_in_segment2  (alseg _ ins) xi) ti.
by rewrite (fv _ _ ti ins).
Qed.

Lemma transfinite_aux3 r T x g:
  worder r ->  inc x (substrate r) ->
  transfiniteg_def (induced_order r (segment r x)) T g ->
  transfiniteg_def (induced_order r (segmentc r x)) T 
    (g +s1 J x (T (restr g (segment r x)))).
Proof. 
move=> wo xsr tdo.
have or:= proj1 wo.
have [sug sog Wg] := tdo.
have ssr: sub (segment r x) (substrate r) by apply: sub_segment.
have sio: substrate (induced_order r (segment r x)) = segment r x
  by rewrite iorder_sr.
rewrite sio in sog  Wg.
set tsx:= segmentc r x; set h:= (restr g (segment r x)).
have stsx: sub tsx (substrate r) by apply: sub_segmentc. 
have sioc: substrate (induced_order r tsx) = tsx by rewrite iorder_sr.
have nxsg: ~ (inc x (domain g)) by rewrite  sog; aw; apply: not_in_segment.
have sto := (fgraph_setU1 (T h) sug nxsg).
have tos:(segment r x) +s1 x = tsx by rewrite /tsx segmentc_pr. 
have soto: domain (g +s1 J x (T h)) = tsx by rewrite domain_setU1 sog.
hnf;rewrite sioc; split => // y ytsx.
rewrite (segment_induced_a (segmentc_segment _ or) ytsx).
case: (equal_or_not y x) => yx.
   rewrite /h yx setU1_V_out //; congr T; apply: restr_exten.
   move => t ts /=; rewrite setU1_V_in //; ue.
have ysx: inc y (segment r x) by  move: ytsx; rewrite -tos; case/setU1_P.
have ydg: inc y (domain g) by ue.
rewrite (setU1_V_in _ sug nxsg ydg) (Wg _ ysx); congr T.
rewrite (segment_induced_a  (segment_segment _ or) ysx).
have sg : segmentp r (domain g) by rewrite sog; apply:segment_segment.
apply: restr_exten => t /(lt_in_segment2 sg ydg) tdg.
by rewrite (setU1_V_in _ sug nxsg).
Qed.

Definition transfiniteg_defined r T:= choose (fun f => transfiniteg_def r T f).

Lemma transfinite_exists1 r T:
   worder r -> exists f, (transfiniteg_def r T f).
Proof.
move => wo.
set (s:=Zo (segments r) (fun z => 
  exists f, transfiniteg_def (induced_order r z) T f)).
have or:= proj1 wo.
have als: (alls s (segmentp r)) by move=> x /Zo_S /(inc_segmentsP wo).
have ssu: forall s', sub s' s -> inc (union s') s.
  move=> s' s's.
  have als':(alls s' (segmentp r)) by move=> x xs'; apply: (als _ (s's _ xs')).
  apply: Zo_i; first by apply /(inc_segmentsP wo); apply: setU_segment. 
  pose tdf z:=  transfiniteg_defined (induced_order r z) T.
  exists (unionf s' tdf); apply: (transfinite_aux2 wo als').
  by move=> z zs'; move: (s's _ zs') => /Zo_P [p1 /choose_pr].
have sss x:inc x (substrate r) -> inc (segment r x) s -> inc (segmentc r x) s.
  move=> xst /Zo_hi [f tdf]; apply: Zo_i.
    by apply: segmentc_insetof. 
  exists (f +s1 J x (T (restr f (segment r x)))).
  apply: (transfinite_aux3 wo xst tdf).
by move /Zo_hi: (transfinite_principle2 wo ssu sss);rewrite iorder_substrate.
Qed.

Lemma transfinite_pr1 r T: worder r ->
  transfiniteg_def r T (transfiniteg_defined r T).
Proof. by move=> wo; apply: choose_pr; apply:transfinite_exists1. Qed.


Lemma transfinite_pr2 r x T:
  worder r -> transfiniteg_def r T x -> transfiniteg_defined r T = x.
Proof. 
move=> wo td; exact:(transfiniteg_unique wo (transfinite_pr1 T wo) td).
Qed.

Lemma dirim_restr f s : fgraph f -> sub s (domain f) ->
  range (restr f s) = direct_image f s.
Proof.
move => Ha sd.
have Hb: fgraph (restr f s) by fprops.
have Hc: domain (restr f s) = s by  aw.
set_extens t.
  move=> /(range_gP Hb) [x xs ->]; apply/dirim_P; exists x; try ue.
  by rewrite Hc in xs; move: (sd _ xs) => xd; rewrite LgV//; apply:fdomain_pr1.
move/dirim_P => [x xs /(pr2_V Ha)];aw => ->.
by apply/(range_gP Hb); rewrite Hc; ex_tac; rewrite LgV.
Qed.


Lemma isomorphism_worder_exists r r': worder r -> worder r' ->
  (exists f, iso_seg_mor r r' f) \/ (exists f, iso_seg_mor r' r f).
Proof.
move => wor wor'.
have or' := proj1 wor'.
have or := proj1 wor.
set E' := substrate r'; set E := substrate r.
pose T f := the_least (induced_order r' (E' -s (range f))).
move: (transfinite_pr1 T wor).
set f := transfiniteg_defined r T; move => [fgf df fp].
set A := Zo (substrate r) (fun z => ssub (range (restr f (segment r  z))) E').
have sAE: sub A E by apply: Zo_S. 
pose U x := E' -s range (restr f (segment r x)).
have res0 x y: glt r x y ->  inc (Vg f x) (range (restr f (segment r y))).
   move/segmentP => xy;apply/Lg_range_P; ex_tac.
have res1: forall x,inc x A -> inc (Vg f x) (U x) /\
   (forall y, inc y (U x) -> gle r'(Vg f x) y).
  move => x /Zo_P [xsr ss1]; move:(setC_ne ss1)  => nec.
  have uE': sub (U x) E' by apply:sub_setC.
  move:(iorder_osr or' uE') =>[orU srU].
  move:(the_least_pr orU (proj2 wor' _ uE' nec)).
  rewrite (fp _ xsr) /T -/(U x); set u := the_least _; move  => [].
  by rewrite srU => ha hb; split => // y /hb /iorder_gle1. 
have res2: segmentp r A.
  split; [ done |  move => x y xA le1; apply:Zo_i; first by order_tac ].
  move/Zo_P: xA =>[xsr xap]; apply: ssub_trans2 xap.
  move => t /Lg_range_P [b /segmentP aw ->]; apply: res0; order_tac.
have res3 x: inc x A -> inc (Vg f x) E'.
  by move /res1 /proj1 /setC_P; case.
have res4 x y: inc x A -> glt r y x -> glt r' (Vg f y) (Vg f x).
  move => xA lxy; move:(proj2 res2 x y xA (proj1 lxy)) => yA.
  have hb b:  glt r b x ->  (Vg f b) <> (Vg f x).
    move => lbx eq; move: (proj1 (res1 x xA)); rewrite - eq => /setC_P [_].
    by case; apply: res0.
  move:(res1 y yA) =>[p1 p2]; split; last by apply: hb.
  apply:p2; apply/setC_P; split; first by apply:res3.
  move/Lg_range_P => [b /segmentP bry]; apply/nesym; apply: hb; order_tac.
have res5 x: inc x A -> inc (Vg f x) (range (restr f A)).
   move => xA; apply/Lg_range_P; exists x => //.
have res6: segmentp r' (direct_image f A).
  have sA: sub A (domain f) by rewrite df.
  rewrite -(dirim_restr fgf sA). 
  split; first by move => y/Lg_range_P[b /res3 ok->].
  move => x y /Lg_range_P[b bA -> le1].
  case: (inc_or_not y (range (restr f (segment r b)))).
    move => /Lg_range_P [c /segmentP lcb ->]; apply:res5.
    apply: (proj2 res2 _ _ bA (proj1 lcb)).
  move  => yr.
  have yU : inc y (U b) by apply/setC_P; split => //; rewrite /E'; order_tac.
  have ->: y = (Vg f b) by move: (proj2 (res1 _ bA) y yU) => h; order_tac.
  by apply: res5.
case: (emptyset_dichot ((substrate r) -s A)) => ae.
  move:(extensionality (empty_setC ae) sAE) => EA.
  set g := triple E E' f.
  left; exists g; split; first by rewrite /Imf/g /Vfs; aw; rewrite /E EA.
  apply: (total_order_increasing_morphism (worder_total wor)).
  have fgg: function_prop g (substrate r) (substrate r').
    rewrite /g; saw; apply: function_pr => //. 
    by move => t/(range_gP fgf); rewrite df EA; move => [x /res3 xE ->].
  split => // x y lxy; rewrite /g /Vf; aw; apply:res4 => //.
  rewrite - EA; order_tac.
move: (worder_prop wor (@sub_setC E A) ae) => [b bA bp].
move/setC_P: bA => [bE /Zo_P bnA].
have res7 c:  glt r c b -> inc c A.
   move => lcb; have cE: inc c (substrate r) by order_tac.
   ex_middle bad1; case:(not_le_gt or _ lcb); apply: bp; apply:setC_i; fprops.
have rrb: (range (restr f (segment r b))) =  E'.
  ex_middle bad; case:bnA; split => //; split => //.
  by move => t /Lg_range_P [c /segmentP /res7 lcb ->]; apply: res3.
have res8 y: inc y E' -> exists2 x, inc x A & y = Vg f x.
  rewrite - rrb => /Lg_range_P [c /segmentP /res7 cA ->]; ex_tac.
have finj y: inc y E' ->  singl_val2 (inc^~ A) (fun x => y = Vg f x).
  move => yE' u v uA -> vA sv.
  case: (total_order_pr1(worder_total wor) (sAE _ uA) (sAE _ vA))=> cp.
    by case:(proj2 (res4 v u vA cp)); rewrite sv.
    by case:(proj2 (res4 u v uA cp)); rewrite sv.
    done.
pose fi y := select (fun x => y = Vg f x) A. 
have res9 y: inc y E' -> y = Vg f (fi y) /\  inc (fi y) A.
   move => yE; apply: (select_pr (res8 _ yE) (finj _ yE)). 
pose g := Lf fi E' E.
have ax: lf_axiom  fi E' E by move => t /res9 [_ /sAE].
have sg: source g = E' by rewrite /g;aw.
have fg: function g by apply:lf_function.
have fgp: function_prop g (substrate r') (substrate r) by rewrite/g; saw.
have img: Imf g = A.
  set_extens t. move/(Imf_P fg); rewrite sg; move=> [u uE ->].
    rewrite LfV//; exact: (proj2 (res9 _ uE)).
  move => tA; move: (res3 _ tA) => ftE.
  apply/(Imf_P fg); rewrite sg; ex_tac; rewrite LfV//.
  by apply: (select_uniq (finj _ ftE) tA).
right; exists g; split; first by rewrite img.
apply: (total_order_increasing_morphism (worder_total wor')).
split => // x y lxy.
have xE: inc x (substrate r') by order_tac.
have yE: inc y (substrate r') by order_tac.
rewrite !LfV //; move:(res9 _ xE) (res9 _ yE)  => [ha hb] [hc hd].
case: (total_order_pr1(worder_total wor) (sAE _ hb) (sAE _ hd)) => cp //.
  move: (res4 _ _ hb cp); rewrite - ha - hc => he; order_tac.
by case: (proj2 lxy); rewrite ha hc cp.
Qed.

Definition transfinite_defined r T:=
  fgraph_to_fun (transfiniteg_defined r (fun f => T (fgraph_to_fun f))).

Lemma transfinite_defined_pr r T: worder r ->
  transfinite_def r T  (transfinite_defined r T).
Proof.
move=> wo; rewrite /transfinite_defined.
set T' := (fun f : Set => T (fgraph_to_fun f)).
move/ (transfinite_def_prop1 ):(transfinite_pr1 T' wo).
set f := fgraph_to_fun  _.
move => [ha hb hc]; split => // x xsr; rewrite (hc _ xsr) /T'.
have ss: sub (segment r x) (source f) by rewrite hb; apply: sub_segment.
by rewrite (fgraph_to_fun_restr (proj1 ha) ss) {2}/fgraph_to_fun/=; aw.
Qed.

Lemma transfinite_pr r x T:
   worder r -> transfinite_def r T x -> transfinite_defined r T = x.
Proof.
move => wo td; exact:(transfinite_unique wo (transfinite_defined_pr T wo) td).
Qed.
  
Theorem transfinite_definition r T:
  worder r -> exists! f, (transfinite_def r T f).
Proof. 
move=> wo; apply /unique_existence. 
split; last by move=> x y;apply: (transfinite_unique wo). 
by exists (transfinite_defined r T); apply:transfinite_defined_pr.
Qed.


(** if [p] sends some functions to [E], then the target of function defined by 
transfinite induction is a subset of [E] *)

Theorem transfinite_definition_stable r T F:
  worder r ->
  (forall f, function f -> segmentp r (source f) -> sub (target f) F ->
    inc (T f) F) ->
  sub (target (transfinite_defined r T)) F.
Proof.
move => wor hb t.
have or := proj1 wor.
move:(transfinite_defined_pr T wor); set f := transfinite_defined r T.
move => [[ff sfj] sf frec] /sfj [x xsf ->]; move: x xsf;rewrite sf.
case: (worder_prop2 (fun x => inc (Vf f x) F) wor) => // - [x [xsr xa px]].
move: (frec _ xsr).
have ssa: sub (segment r x) (source f) by rewrite sf; apply:sub_segment.
move:(restriction1_fs ff ssa) => [fg].
move: (hb _ fg); rewrite [in (source _)] /restriction1; aw => p1 p2 => sa.
have aux: sub (target (restriction1 f (segment r x))) F.
  move => y /p2 [u ua ->].
  by rewrite (restriction1_V ff ssa ua); move /segmentP: ua => /px.
by move:  (p1 (segment_segment _ or) aux); rewrite - sa.
Qed.


Definition ordinal_iso r := transfinite_defined r target.
Definition ordinal_isog r := transfiniteg_defined r range.
  
Lemma transdef_tg0 r (f := ordinal_isog r): worder r -> 
  forall x, inc x (substrate r) ->
  Vg f x = direct_image f (segment r x).
Proof.
move => wor x xsr.
move: (transfinite_pr1 range wor) => [pa pb pc].
rewrite (pc _ xsr) dirim_restr //; rewrite pb; apply: sub_segment.
Qed. 

Lemma transdef_tg1 r (f := ordinal_iso r): worder r -> 
  forall x, inc x (substrate r) ->
  Vf f x = Vfs f (segment r x).
Proof.
move => wor x xsr.
move: (transfinite_defined_pr target wor)=> [pa pb pc].  
by rewrite (pc _ xsr)  corresp_t.
Qed. 

Lemma transdef_tg2 r f:
  worder r -> surjection f -> source f = substrate r ->
  (forall x, inc x (substrate r) -> Vf f x = Vfs f (segment r x)) ->
  f = ordinal_iso r.
Proof.
move => wor pa pb pc.
have pd: transfinite_def r target f by split => // x /pc ->; rewrite corresp_t.
by move: (transfinite_pr wor pd).
Qed.

Lemma transdef_tg3 r (f: fterm):
  worder r -> 
  (forall x, inc x (substrate r) -> f x = fun_image (segment r x) f) ->
  forall x, inc x (substrate r) -> f x =  Vf (ordinal_iso r) x.
Proof.
move => wor pa x xX.
have or := proj1 wor.
set C := (fun f0 : Set => target (fgraph_to_fun f0)).
rewrite /ordinal_iso /transfinite_defined -/C fgraph_to_fun_ev.
pose g := Lg (substrate r) f.
have ->: f x = Vg g x by rewrite LgV.
congr Vg; symmetry; apply: (transfinite_pr2 wor).
have fg : fgraph g by rewrite/g;fprops.
rewrite /g; saw  => t tX; rewrite LgV //.
rewrite (pa _ tX) /C corresp_t - Lg_range restr_Lg //; apply: sub_segment.
Qed.


(** **  EIII-2-3  Zermelo's theorem *)

(** Given an ordering, let [Sx] be the segment with endpoint [x],
   considered as an ordered set. Given two orderings, we consider the set of 
   all [x] with [Sx=Sx']. 
   This is a segment, ordered by any of the two induced orders. *)

Definition Zermelo_ax E (p:fterm) s r:=
  [/\ worder r,
  sub (substrate r) E &
  forall x, inc x (substrate r) -> 
   ( inc (segment r x) s) /\ p (segment r x)  = x].

Lemma Zermelo_aux E s p
  (r :=  union (Zo (\Po coarse E)  (Zermelo_ax E p s))):
  sub s (\Po E) ->
  (forall x, inc x s -> inc (p x) (E -s x)) ->
  Zermelo_ax E p s r /\ (~ (inc (substrate r)  s)).
Proof. 
move=> sp pp.
rewrite /r;set (m:= Zo _ _); clear r.
pose co r r' := Zo ((substrate r) \cap (substrate r'))
    (fun x => segment r x = segment r' x /\
        (seg_order r x) = (seg_order r' x)).
have aux0 r r': co r r' = co r' r.
   rewrite /co setI2_C. 
   set_extens t; move/Zo_P => [pa [pb pc]]; apply: Zo_i => //.
have aux1 r r': worder r ->  worder r' -> segmentp r (co r r').
  rewrite /co => wor wor'.
  split; first by move=> t /Zo_S /setI2_P  [].
  move=> x y.  
  case: (equal_or_not y x); first by move=> ->.
  move => nyx /Zo_P  [pa [pb pc]] pd.
  have ltyx:glt r y x by split.
  have sry: inc y (segment r x) by apply /segmentP.
  have sry': inc y (segment r' x) by rewrite - pb.
  have syr: inc y (substrate r) by apply: (sub_segment sry).  
  have syr': inc y (substrate r') by apply: (sub_segment sry').  
  rewrite /seg_order/induced_order - pb in pc.
  have or: order r by fprops.
  have or': order r' by fprops. 
  have sryy': (segment r y = segment r' y).
    set_extens t; move/segmentP => [ty nty]; apply /segmentP;  split=>//;
       suff: (inc (J t y) (r \cap (coarse (segment r x)))).
    - by rewrite pc; case/setI2_P.
    - apply/setI2_i => //; apply/setXp_i => //; apply/segmentP; order_tac.
    - by case /setI2_P.
    - have  aux: glt r' y x by apply/segmentP; rewrite -pb; apply/segmentP.
      rewrite pc pb;apply:setI2_i => //; apply:setXp_i;apply/segmentP =>//.
      order_tac.
  apply: Zo_i; [ fprops | split=>// ].
  rewrite /seg_order/induced_order - sryy'.
  move: (coarse_segment_monotone or pd)=> p1.
  set_extens z; move/setI2_P =>[zr zc];
    suff: (inc z (r \cap (coarse (segment r x)))).
  - by rewrite pc; case/setI2_P => qa qb; apply: setI2_i => //; apply: p1.
  - by apply /setI2_i => //; apply: p1.
  - by move /setI2_P => [qa qb]; apply :setI2_i.
  - by rewrite pc;apply/setI2_i => //; apply: p1.
have aux2 r r': worder r ->  worder r' ->
  sub (induced_order r (co r r')) (induced_order r' (co r r')).
  move=> wor wor'.
  have or: order r' by fprops.
  move=> t /setI2_P [tr] /setX_P [pt Pt Qt].
  apply/setI2_P; split; last by apply /setX_P.
  move: Qt => /Zo_P [] /setI2_P [Qtr Qtr'] [ss io].
  case: (equal_or_not (P t) (Q t)) => eq.
    by rewrite -pt eq;  order_tac.
  rewrite -pt in tr.
  have: inc (P t) (segment r (Q t)) by apply: segment_inc.
  rewrite ss  -{3} pt => aux.
  exact: (proj1 (inc_segment aux)).
pose qp r r' :=  [/\ sub (substrate r) (substrate r'),
     r = induced_order r' (substrate r) & segmentp r' (substrate r)].
have aux3 r r': Zermelo_ax E p s  r -> Zermelo_ax E p s r' -> 
 qp r r' \/ qp r' r.
  move=> [wor srE prx] [wor' srE' pry].
  move: (aux1 _ _ wor' wor)(aux1 _ _ wor wor'). 
  rewrite aux0; set (v:= co r r'). 
  move=> svr' svr.
  have io: (induced_order r v = induced_order r' v).
    apply: extensionality; first by apply: aux2. 
    by rewrite /v aux0; apply: aux2. 
  move: (sub_segment1 svr)(sub_segment1 svr')=>  vsr vsr'.
  case: (equal_or_not v (substrate r)) => evr.
    left; rewrite /qp -evr; split => //. 
    rewrite -io evr;symmetry; apply: iorder_substrate; fprops.
  case: (equal_or_not v (substrate r')) => evr'.
    right; rewrite /qp -evr'; split => //. 
    rewrite io evr';symmetry; apply: iorder_substrate; fprops.
  case: (emptyset_dichot  ((substrate r) -s v)) => cr.
    by case: evr; apply: extensionality=>//; apply: empty_setC. 
  case: (emptyset_dichot  (complement (substrate r') v)) => co'. 
    by case: evr'; apply: extensionality=>//; apply: empty_setC.
  have sc: (sub  ((substrate r) -s v) (substrate r)).
     by apply: sub_setC.
  have sc': (sub  ((substrate r') -s v) (substrate r')).
     by apply: sub_setC.
  move:(worder_total wor) (worder_total wor')=> tor tor'. 
  move:wor=> [or wo]; move: (wo _ sc cr)=> [x []].
    rewrite iorder_sr // => /setC_P [xs xc] px.
  move:wor'=> [or' wo']; move: (wo' _ sc' co')=> [y []].
  rewrite iorder_sr // => /setC_P [ys yc] py.
  have p1: (segment r x = v).  
    set_extens z => zs.
      ex_middle aux.
      move: (inc_segment zs) => zx.
      have zc: inc z ((substrate r) -s v) by apply/setC_P; split=>//; order_tac.
      move: (iorder_gle1  (px _ zc)) => h; order_tac.
    apply /segmentP.
    case: (total_order_pr2 tor (vsr _ zs) xs)=>// xz.
    case: xc; exact: ((proj2 svr) _ _ zs xz).
  have p2: (segment r' y = v).  
    set_extens z => zs.
      ex_middle aux. 
      move: (inc_segment zs) => zx.
      have zc: inc z ((substrate r') -s v) by apply/setC_P;split=>//;order_tac.
      move: (iorder_gle1 (py _ zc)) => h; order_tac.
    apply /segmentP.
    case: (total_order_pr2 tor' (vsr' _ zs) ys)=>// yz.
    case: yc; exact: ((proj2 svr') _ _ zs yz).
  have xy: x = y by rewrite - (proj2(prx _ xs)) -(proj2(pry _ ys)) p1 p2.
  case: xc.
  apply: Zo_i; first by apply :setI2_i => //; ue.  
  by rewrite /seg_order  p1 xy p2. 
have ha x: inc x m -> worder x  by move => /Zo_hi [].
have hb a b: inc a m -> inc b m ->
       segmentp a (substrate b) \/ segmentp b (substrate a).
  move => /Zo_hi za /Zo_hi zb.
  by case: (aux3 _ _ za zb); move => [_ _]; [right | left ].
have hc a b: inc a m -> inc b m ->
   sub (substrate a) (substrate b) -> order_extends a b.
  move => am bm sab; move:(am)(bm) =>/Zo_hi za /Zo_hi zb.
  case: (aux3 _ _ za zb);move=> [sba bi siab]; first exact.
  have ssab: (substrate a = substrate b) by apply: extensionality.
  move:(iorder_substrate (proj1 (ha _ am))) => H.
  by move: bi; rewrite/order_extends - ssab H; move ->.
have hcw a b: inc a m -> inc b m ->
   sub (substrate a) (substrate b) -> sub a b.
  by move => am bm h; rewrite (hc _ _ am bm h) => t /setI2_P [].
have sxm x: inc x m -> sub x (coarse E) by move /Zo_S/setP_P.
have eVVg a b:  inc a m -> inc b m -> exists c,
      [/\ inc c m, sub (substrate a) (substrate c)
        & sub (substrate b) (substrate  c)].
  move => am bm.
  by case: (hb _ _ am bm) => - [sa _]; [  exists a | exists b]; split.
set G := union m.
have gu: sgraph G. 
  move=> t /setU_hi [y ty /sxm yc]; exact:(setX_pair (yc _ ty)).
pose D := Zo E (fun z => exists2 x, inc x m & inc z (substrate x)).
have ur y: inc y D ->  related G y y. 
  move =>/Zo_hi[x xm ysx]; apply/setU_P; ex_tac.
  by move:(proj42 (proj1 (ha _ xm)) y ysx). 
have su: substrate G = D. 
  set_extens x; last by move/ur => rr; substr_tac.
  case /(substrate_P gu) => [] [y Ju]; move: (setU_hi Ju)=>  [z zdg zp].
    move:((sxm _ zp) _ zdg) => /setXp_P [xE _].
    apply: (Zo_i xE); exists z => //; substr_tac.
   move:((sxm _ zp) _ zdg) => /setXp_P [_ yE ].
   apply: (Zo_i yE); exists z => //; substr_tac.
have sGP x:
  inc x (substrate G) <-> exists2 t, inc t m & inc x (substrate t).
  split; first  by rewrite su; move/Zo_hi.
  move => [t tm xsr]. move:(proj42 (proj1 (ha _ tm)) x xsr) => txx.
  have hh: inc (J x x) G by  apply/setU_P; exists t.
  substr_tac.
have cov x y: inc x G -> inc y G -> 
    exists u, [/\ inc u m, inc x u & inc y u].
  move=> /setU_P [a adg ap] /setU_P [b bdg bp].
  case: (hb _ _ ap bp) =>- [asub _].
    by  move:(hcw _ _ bp ap asub) => sba; exists a; split => //; apply: sba.
  by  move:(hcw _ _ ap bp asub) => sba; exists b; split => //; apply: sba.
have oG: order G.
  split.
  + exact.
  + by hnf; rewrite su.
  + move => x y z p1 p2; move: (cov _ _ p1 p2)=> [c [cm p1c p2c]].
    move: (ha _ cm) => [/proj43 or _]; exact:(setU_i (or _ _ _ p1c p2c) cm).
  + move => x y p1 p2; move: (cov _ _ p1 p2)=> [c [cdg p1c p2c]].
    move: (ha _ cdg)=> [or _]; order_tac.
have Vag a: inc a m -> induced_order G (substrate a) = a.
  rewrite /induced_order.
  move => am;set_extens x => xs; last first.
     apply/setI2_P; split; first by rewrite /G;  union_tac.
     by apply:(sub_graph_coarse_substrate (proj41 (proj1 (ha _ am)))).
  move/setI2_P:xs => [/setU_P  [z xz zm] xaa].
  move: (eVVg _ _ am zm)  => [t [tm sa sz]].
  have xt:= ((hcw z t zm tm sz) _ xz).
  by rewrite (hc _ _ am tm sa); apply/setI2_P.
have p1 a: inc a m -> sub (substrate a) (substrate G).
  move => am t tsa; apply/sGP; ex_tac.
have p0 a x y: inc x (substrate a) -> gle G y x -> inc y (substrate G)
   -> inc a m -> inc y (substrate a).
  move => xs/setU_P [u Jv udg] ys am.
  case: (hb  _ _ am udg) => h; first by apply:(proj1 h); substr_tac.
  exact: (proj2 h _ _ xs Jv).
have p2 a: inc a m -> segmentp G (substrate a).
  move=> am;split; first by apply: p1.
  move=> x y xs yx;exact: (p0 a _ _ xs yx (arg1_sr yx) am).
have p3 a x: inc a m -> inc x (substrate a) -> segment a x = segment G x.
  move=> am xs; set_extens y => ys; move: (inc_segment ys) => [yx nyx].
    apply /segmentP; split=>//; apply: setU_i yx am.
  apply/segmentP; split => //;rewrite - (Vag _ am);apply/iorder_gle0P => //.
  exact: (p0 a _ _ xs yx (arg1_sr yx) am).
have p4 a x: inc a m -> segmentp a x ->  segmentp G x.
  move=> am sa; case: (well_ordered_segment (ha _ am) sa).
    by move=> ->; apply: p2.
  by move=> [y ysV ->]; rewrite (p3 _ _ am ysV); apply: segment_segment.
have woG: worder G.
  apply:(worder_prop_rev oG) => x xsr [y yx].
  move /sGP: (xsr _ yx) => [a am ysa].
  set (x1:= x \cap (substrate a)).
  have sx1s: (sub x1 (substrate a)) by apply: subsetI2r.
  have nx1: nonempty x1 by exists y; apply: setI2_i.  
  move: (worder_prop (ha _ am) sx1s nx1)=> [z zs zle].
  have zx: inc z x by apply: (setI2_1 zs).
  have zVa: inc z (substrate a)  by apply: (setI2_2 zs).  
  exists z => // t tx.
  move: (xsr _ tx) => /sGP [b bm bV]. 
  have aux: inc t (substrate a) -> gle G z t.
    move=> hyp.
    by move:(zle _ (setI2_i tx hyp));rewrite - (Vag _ am) => /iorder_gle1.
  case: (hb _ _ am bm); move => [px py]; first by apply: (aux (px _ bV)).
  move: (px _ zVa)=> zVb.
  case: (total_order_pr2 (worder_total (ha _ bm)) bV zVb).
    move=> [tz ntz]; apply: (aux (py _ _ zVa tz)).
  by rewrite - (Vag _ bm) => /iorder_gle1.
have ssGE: sub (substrate G) E by rewrite su; apply/Zo_S.
have ssG x: inc x (substrate G) ->
  inc (segment G x) s /\ p (segment G x) = x.
  move => /sGP [y ym xsy]; move: (ym) => /Zo_hi [_ _ zp2].
  by rewrite - (p3 y x ym xsy); apply: zp2.
have Za: (Zermelo_ax E p s G) by [].
split => // sGs.
case/setC_P:(pp _ sGs); set (a:= p (substrate G)) => [aE nas].
move:(worder_adjoin_greatest woG nas).
move: (order_with_greatest_pr (worder_or woG) nas).
set Ga := order_with_greatest G a; move => [[oGa sGa] Gai [aGA ala]] woGa.
have seGa: segment Ga a = (substrate G).
  set_extens x => xs.
     move:(inc_segment xs)=> [xa xna]. 
     have: inc x (substrate Ga) by order_tac.
     by rewrite sGa => /setU1_P;case.
  have nax: x <> a by dneg axx; rewrite -axx.
  apply /segmentP; split=>//; apply: ala; rewrite sGa; fprops.
have asa x: inc x (substrate Ga) -> x = a \/ segment Ga x = segment G x.
  rewrite  sGa => /setU1_P; case; last by left.
  move=> xsr; right.
  have xsre: inc x (substrate Ga) by rewrite sGa; aw; fprops.
  set_extens y; move /segmentP=> [yx nyx]; apply/segmentP; split => //.
     rewrite Gai; apply/iorder_gleP => //.
      move: (arg1_sr yx); rewrite sGa => /setU1_P; case => // eya.
      move: (ala _ xsre); rewrite -/Ga - eya => xy; case: nyx; order_tac. 
  by move: yx; rewrite Gai; apply: iorder_gle1.
have Zae: (Zermelo_ax E p s (order_with_greatest G a)).
  move: Za=> [q1 q2 q3].
  have H t: inc t (substrate G) ->
      segment (order_with_greatest G a) t = segment G t.
    move => ts; move: (setU1_r (p (substrate G)) ts); rewrite - sGa => /asa.
    by case => // hyp; case: nas; rewrite - hyp.
  split=>//; rewrite sGa => t /setU1_P; case.
  - apply: q2.
  - by move=> ->.
  - by move=> ts; rewrite (H _ ts); apply: q3.
  - by move => ->; rewrite seGa.
have um:inc (order_with_greatest G a) m.
  apply: Zo_i =>//;apply /setP_P.
  apply: sub_trans (setX_Sll (proj32 Zae)).
  apply: sub_graph_coarse_substrate; fprops.
case: nas; apply/sGP; ex_tac; rewrite sv; apply: setU1_1.
Qed.




(** The axiom of choice asserts existence of an element [p(x)] of [E] not 
   in [x], if [x] is not [E]. From this we deduce a well-ordering on [E]  *)


Lemma Zermelo_v1 E (p:= fun x => rep (E -s x)) (s:=(\Po E) -s1 E)
    (r :=  union (Zo (\Po coarse E) (Zermelo_ax E p s))):
   worder_on r E.
Proof. 
have p1: sub s (\Po E) by rewrite /s; apply: sub_setC.
have p2: forall x, inc x s -> inc (p x)  (E -s x).
  move=> x xs; rewrite /p; apply: rep_i. 
  apply: setC_ne. 
  by move: xs => /setC_P [] /setP_P pa /set1_P xe.
have p3: forall x, inc x s -> (inc (p x) (E -s x)).
  by move =>  x xs; move: (p2 _ xs).
move: (Zermelo_aux p1 p3) => [[xor so _] ns].
split => //;ex_middle h; case: ns.
by apply/setC_P; split; [ apply /setP_P | move/set1_P].
Qed.


Theorem Zermelo E: exists r, worder_on r E.
Proof.  by move: (Zermelo_v1 E) => /=; set r := union _ => h; exists r. Qed.


(** **  EIII-2-4 Inductive sets *)

Definition inductive r :=
  forall X, sub X (substrate r) -> total_order (induced_order r X) ->
    exists x, upper_bound r X x.

(** Examples of inductive set *)

Lemma inductive_graphs a b:
  inductive (opp_order (extension_order a b)).
Proof.
move: (extension_osr a b)=> [or sr].
move: (opp_osr or) => [ooi osr] X XX.
move: (XX); rewrite osr sr => Xs toX.
have Ha:forall i, inc i X -> function i.
   by move=> i iX; move: (Xs _ iX)  => /sfunctionsP [].
have Hb:forall i, inc i X -> target i = b. 
  by move=> i iX; move: (Xs _ iX)  => /sfunctionsP [_ ].
move: toX=> [orX]; rewrite iorder_sr // => tor.
set si:= Lg X source.
have Hd: forall i j, inc i (domain si) -> inc j (domain si) -> 
    agrees_on ((Vg si i) \cap (Vg si j)) i j.
  rewrite /si; aw; move=> i j iX jX; rewrite !LgV //.
  split; [by apply: subsetI2l |  by apply: subsetI2r | ].
  move=> t /setI2_P [ti tj].
  case: (tor _ _ iX jX) => h; move: (iorder_gle1 h)=> h'.
     apply: (extension_order_pr h' ti).
  symmetry;  apply: (extension_order_pr h' tj).
have He:forall i, inc i (domain si) -> function_prop i (Vg si i) b.
   rewrite /si; aw; move=> i iX; rewrite LgV //;split; fprops.
move: (extension_covering He Hd) => [[fg sg tg] _ _ agg].
set g:= (common_ext si id b).
have gs: (inc g (sub_functions a b)).
  apply /sfunctionsP;split => // t tsg. 
  rewrite sg in tsg; move: (setUf_hi tsg)=> [v]. 
  rewrite {1}/si; aw => vx; rewrite LgV // => tv.
  by move: (Xs _ vx) =>  /sfunctionsP [_ sv _]; apply: sv.
rewrite /upper_bound osr sr; ex_tac.
move: agg; rewrite /si; aw => agg.
move=> y yX; move: (Xs _  yX)=> ys; move: (agg _ yX)=> ag.
have fy: (function y) by move: ys; fprops.
apply /igraph_pP; apply/extension_order_P1;split => //.
apply/(sub_functionP fy fg).
move: ag; rewrite /agrees_on !LgV //;move=> [p1 p2 p3]; split => //.
by move=> u; symmetry; apply: p3.
Qed.

(** Full and short version of Zorn's lemma *)

Lemma Zorn_aux_eff r (m n: fterm): order  r -> 
  (forall s, sub s (substrate r) -> worder (induced_order r s) ->
      upper_bound r s (m s)) ->
  (forall x, inc x (substrate r) -> glt r x (n x)) ->
  False.
Proof.
move=> or mp np.
set (E:= substrate r). 
set (s:= Zo (\Po E) (fun z => (worder (induced_order r z)))).
have sp: sub s (\Po E) by rewrite /s; apply: Zo_S.
pose p s := n (m s).
have mp1 x: inc x s ->  upper_bound r x (m x).
  by move =>  /Zo_P [/setP_P sa sb]; apply: mp.
have Ha x: inc x s -> inc (p x) E.
  move/mp1 => [/np lt _]; rewrite/E; order_tac.
have Hb x: inc x s ->  upper_bound r x (p x). 
  move/mp1 =>[qa qb]; move:(np _ qa) => [qc _].
  split; [ order_tac |]; move => y /qb => lr; order_tac.
have Hc x: inc x s -> ~ inc (p x) x. 
  move => xs pxx.
  move/mp1: (xs) =>[qa qb];  move:(np _ qa) => [qc qd].
  move:(qb _ pxx) => ba; case qd; order_tac.
have zp x: inc x s -> inc (p x) (E -s x).
  move => zs; apply/setC_P; split; fprops.
move: (Zermelo_aux sp zp); set r' := union _.
move =>[[xor so ww] ns].
move: (iorder_osr or so) => [oi sr1].
have ext: sub r' (induced_order r (substrate r')).
  move=> x xr.
  move:(pr1_sr xr)(pr2_sr xr) => Ps Qs.
  have gr: sgraph r' by fprops.
  move: (gr _ xr) => xp; rewrite -xp; rewrite - xp in xr.
  case: (equal_or_not (P x) (Q x)) => aux. 
    rewrite aux; order_tac; rewrite iorder_sr //.
  have ltPQ: glt r' (P x) (Q x) by split.
  have Pse: (inc (P x) (segment r' (Q x))) by apply/segmentP.
  apply /iorder_gle0P => //.
  move: (ww _ Qs) => [p1 <-].
  by apply: (proj2 (Hb _ p1)).
have r'v: r' = induced_order r (substrate r').
  apply: extensionality => // t tio.
  have p1: order (induced_order r (substrate r')) by fprops.
  have p2: sgraph (induced_order r (substrate r')) by fprops.
  move: (p2 _ tio) => pt. 
  move:(pr1_sr tio)(pr2_sr tio); rewrite sr1 => Ps Qs.
  rewrite -pt in tio  *.
  case: (total_order_pr2 (worder_total xor) Qs Ps) =>//.
  move=> [lePQ nPQ]; move: (ext _ lePQ)=>tio'; case: nPQ;  order_tac. 
rewrite r'v in xor.
by case  ns; apply:Zo_i;first apply/setP_P.
Qed.

Theorem Zorn_aux r: order  r -> 
  (forall s, sub s (substrate r) -> worder (induced_order r s) ->
    (bounded_above r s)) -> 
  exists a, maximal r a.
Proof.
move=> or zaux.
set E := substrate r.
ex_middle bad.
have Ha: forall x, inc x E -> exists y,  glt r x y.
  move => x xR; ex_middle ba1; case: bad; exists x; split => //.
  by move => y le1; symmetry; ex_middle ba2; case: ba1; exists y.
pose next x := choose (fun y => glt r x y). 
have ha: (forall x, inc x (substrate r) -> glt r x (next x)).
  move=> x xE; apply: (choose_pr (Ha _ xE)).
pose p s x :=  upper_bound r s x.
pose max s := choose (p s).
have hb: (forall s, sub s (substrate r) -> worder (induced_order r s) ->
    upper_bound r s (max s)).
  by move => s sa sb;move:(zaux _ sa sb) => xx; apply: choose_pr. 
case: (Zorn_aux_eff or hb ha).
Qed.


Theorem Zorn_lemma r: order  r -> inductive r ->
  exists a, maximal r a.
Proof. 
move=> or isr; apply: Zorn_aux =>//. 
by move=> s ssr wo; hnf;  apply: isr =>//; apply: worder_total.
Qed.


(** Consequences *)

Lemma inductive_max_greater r a: order r ->  inductive r ->
  inc a (substrate r) -> exists2 m, maximal r m & gle r a m.
Proof.
move=> or isr asr. 
set (F:= Zo (substrate r)(gle r a)).
have Fs: sub F (substrate r) by rewrite /F; apply: Zo_S.
move: (iorder_osr or Fs) => [oi sr].
have aF: inc a F by rewrite /F; apply: Zo_i=> //; order_tac.
suff isF: inductive (induced_order r F).
  move:(Zorn_lemma oi isF)=> [b []]; rewrite iorder_sr // => bF bm.
  move: (bF) => /Zo_P [bs ab].
  exists b => //; split =>// x h. 
  apply: bm;  apply/iorder_gle0P => //; apply: Zo_i; order_tac. 
move=> u; rewrite iorder_sr // => uF; rewrite iorder_trans // => toi.
have tos: (sub (u +s1 a) (substrate r)).
  by apply: sub_trans Fs => t;  case /setU1_P ; [ apply: uF|  move=> ->]. 
move: (iorder_osr or tos) => [oit sit].
have toit: total_order (induced_order r (u +s1 a)).  
  split=>//; rewrite sit.
  have susr: sub u (substrate r) by apply: sub_trans Fs.
  move=> x y; case /setU1_P=> hx; case /setU1_P => hy.
  - move: toi => [_]; rewrite iorder_sr // => h.
    move: (h _ _ hx hy); case => xx; [left | right];
    apply/iorder_gle0P; fprops; apply (iorder_gle1  xx).
  - rewrite hy;right; apply/iorder_gle0P; fprops.
    by move: (uF _ hx); move /Zo_P => [].
  - rewrite hx;left; apply/iorder_gle0P; fprops.
    by move: (uF _ hy); move /Zo_P => [].
  - rewrite hx hy; left;apply/iorder_gle0P; fprops.
    by move: aF; move /Zo_P => [].
move: (isr _ tos toit) => [b [bs bub]].
move: (bub _  (setU1_1 u a)) => ab.
have bF: inc b F by rewrite /F; apply: Zo_i. 
exists b; split; first by  rewrite iorder_sr //.
move => y yu.
by move: (bub _  (setU1_r a yu)) => yb; apply/iorder_gle0P => //; apply: uF.
Qed.

Lemma setP_inductive A F: sub A (\Po F) ->
  (forall S, (forall x y, inc x S -> inc y S -> sub x y \/ sub y x) ->
    sub S A ->inc (union S) A) ->
  inductive (sub_order A).
Proof.
move=> sp Sp X XA [oX tX]. 
move: (sub_osr A) => [or1 sr1].
rewrite iorder_sr in tX; fprops; rewrite sr1 in XA.
have p1: inc (union X) A.
  apply: Sp =>// x y xX yX.
  case: (tX _ _ xX yX).
   by move/iorder_gle1 => /sub_gleP [_ _ h]; left.
   by move/iorder_gle1 => /sub_gleP [_ _ h]; right.
exists (union X);split; first by ue.
by move=> y yX; apply /sub_gleP;split => //;fprops; apply: setU_s1.
Qed.

Lemma setP_maximal A F: sub A (\Po F) ->
  (forall So, (forall x y, inc x So -> inc y So -> sub x y \/ sub y x) ->
    sub So A -> inc (union So) A) ->
  exists a, maximal (sub_order A) a.
Proof.
move=> Ap /(setP_inductive Ap).
by move: (sub_osr A) => [oA sr1];apply:  Zorn_lemma.
Qed.

Lemma setP_minimal A F: sub A (\Po F) -> nonempty A ->
  (forall S, (forall x y, inc x S -> inc y S -> sub x y \/ sub y x) ->
    sub S A -> nonempty S -> inc (intersection S) A) ->
  exists a, minimal (sub_order A) a.
Proof. 
move=> Ap [x xA] pA.
move: (sub_osr A) => [oA sr1].
move: (opp_osr oA) => [ooA soA].
have ioA: inductive (opp_order (sub_order A)).
  move => X; rewrite soA sr1 => XA;rewrite /total_order. 
  rewrite iorder_sr // ? soA ? sr1 //.
  move=> [pb pc]; rewrite /upper_bound soA sr1.
  case: (emptyset_dichot X) => neX.
     exists x; rewrite neX;split => // y; case; case.
  have iXA:inc (intersection X) A. 
    apply: pA =>// a b aX bX.
    by move: (pc _ _ aX bX); case => h; move: (iorder_gle1 h) =>
       /igraph_pP /sub_gleP [_ _]; [right | left].
  exists (intersection X); saw. 
  move=> y yX;apply /igraph_pP; apply /sub_gleP;split; fprops.
  by apply: setI_s1.
move: (Zorn_lemma ooA ioA)=> [a ] /(maximal_opp oA) ha. 
by exists a. 
Qed.

(** **  EIII-2-5  Isomorphisms of well-ordered sets *)

(** Uniqueness of morphism between segments of well-ordered sets *)

Lemma increasing_function_segments r r' f g:
  worder r -> worder r' ->
  increasing_fun f r r' -> strict_increasing_fun g r r'->
  segmentp r' (Imf f) ->
  forall x, inc x (source f) -> gle r' (Vf f x) (Vf g x).
Proof.
move=> wor wor'
  [or or' [ff sf tf] incf] [_  _ [fg sg tg] sing] sr x xsf.
set (s :=Zo (source f) (fun x => (glt r' (Vf g x) (Vf f x)))). 
have sfsg: source f = source g by ue.
move: (worder_total wor) => tor. 
move: (worder_total wor') => tor'.
have Wfsr': inc (Vf f x) (substrate r') by rewrite - tf; fprops.
have Wgsr': inc (Vf g x) (substrate r').
    by rewrite sfsg in xsf;rewrite - tg; fprops.
case: (total_order_pr2 tor' Wgsr' Wfsr') =>// Wlt.
have nes: nonempty s by exists x; rewrite /s; apply: Zo_i.
have ssf: sub s (substrate r) by rewrite /s sf; apply: Zo_S.
move:(worder_prop wor ssf nes)=> [y ys yle].
move: ys => /Zo_P [ysf [leWy neWy]].
have Wrg: inc (Vf f y)  (Imf f) by Wtac. 
move: ((proj2 sr) _ _ Wrg leWy).
move/(Imf_P ff) => [z zf vv].
have lt1: glt r' (Vf f z) (Vf f y) by rewrite - vv.
have lt2: glt r z y.  
   have: (glt r z y \/ gle r y z).
     rewrite sf in ysf zf; apply: (total_order_pr2 tor zf ysf). 
  case =>// yz; move: (incf _ _ yz)=> lt4; order_tac. 
have Wzf: inc (Vf f z) (substrate r') by rewrite - tf; fprops. 
have Wzg: inc (Vf g z) (substrate r') 
  by rewrite sfsg in zf;rewrite- tg; fprops. 
case: (total_order_pr2 tor' Wzg Wzf) => h.
  have zs: (inc z s) by apply: Zo_i. 
  case: (not_le_gt or (yle _ zs)  lt2).
move: (sing _ _ lt2); rewrite vv => lt3; order_tac. 
Qed.

Lemma isomorphism_worder_unique r r' x y:
  worder r -> worder r' ->
  segmentp r' (Imf x) -> segmentp r' (Imf y) -> 
  order_morphism x r r' -> order_morphism y r r' ->
  x = y.
Proof.
move=> wor wor' srx sry mx my.
move:(order_morphism_increasing mx) => six.
move:(order_morphism_increasing my) => siy.
move: (strict_increasing_w six)=> sx. 
move: (strict_increasing_w siy)=> sy.
move: mx my=> [_ or' [fx srcx tx] _][_ _ [fy srcy ty] _].
apply: function_exten =>//; try ue. 
move=> a asx.
move: (increasing_function_segments wor wor' sx siy srx asx) => p1.
rewrite srcx - srcy in asx.
move: (increasing_function_segments wor wor' sy six sry asx) => p2.
order_tac.
Qed.



Lemma unique_isomorphism_onto_segment r f: worder r -> 
  segmentp r (Imf f) ->  order_morphism f r r ->
  f = identity (substrate r).
Proof. 
move=> wor seg mor.
have [pa pb]: segmentp r (Imf (identity (substrate r))) /\
    order_morphism (identity (substrate r)) r r. 
  split.
  have [_ si]:(bijection (identity (substrate r))) by apply: identity_fb.
  rewrite (surjective_pr0 si); aw; apply: substrate_segment; fprops.
  apply: identity_morphism; fprops.
exact:(isomorphism_worder_unique wor wor seg pa mor pb).
Qed.

(*¨old 

Lemma segment_not_iso r a: worder r -> inc a (substrate r) ->
  r \Is (seg_order r a) -> False.
Proof.
rewrite -/(seg_order _ _).
move => wor asr [f fis]. 
have or := proj1 wor.
move: (@sub_segment r a) => s1.
move:(iorder_sr (proj1  wor) s1) => sr1.
move:(induced_wor wor s1) => wor2.
move:(isomorphism_to_morphism or or s1 fis).
set g := Lf _ _ _; move =>[qa qb].
have pc: segmentp r (Imf g) by rewrite qb; apply: segment_segment.
move:(unique_isomorphism_onto_segment wor pc qa) => gid.
move:(qa) => [_ _ [fg sfg tg] _].
move: qb asr; rewrite - tg.
move: (proj2(identity_fb  (substrate r))); rewrite - gid => /surjective_pr0.
move => -> ->;  apply: not_in_segment.
Qed.
*)

Lemma segment_not_iso r a: worder r -> inc a (substrate r) ->
  r \Is (seg_order r a) -> False.
Proof.
move => wor ase [f fiso].
move:(fsincr_wor_prop wor (@sub_segment r a) fiso ase) => la.
move: fiso =>[_ _ [/proj1 /proj1 ff sf tf] _].
have: inc (Vf f a) (target f) by  Wtac.
rewrite tf (iorder_sr (proj1 wor) (@sub_segment r a) ) => /segmentP.
exact: (not_le_gt (proj1 wor) la).
Qed.


Lemma iso_unique_segment r x y: worder r ->
   inc x (substrate r) -> inc y (substrate r) ->
   (seg_order r x) \Is (seg_order r y) ->
  x = y.
Proof.
move => wor xsr ysr.
suff H: forall a b,   glt r a b ->
   (seg_order r a) \Is (seg_order r b) -> False.
  move =>h; ex_middle bad.
  case:(proj2(worder_total wor) x y xsr ysr) => le.
    case:(H _ _  (conj le bad) h). 
    case:(H _ _  (conj le (nesym bad)) (orderIS h)).
move => a b ltab {xsr ysr} /orderIS [f h].
have or := proj1 wor.
move: (h) =>  [ora orb [[[ff _] _]  sf tf] fi].
move:(seg_order_wosr a wor)(seg_order_wosr b wor) =>[woa sra][wob srb].
have ias: inc a (source f) by rewrite sf  srb; apply/segmentP.
move:(Vf_target ff ias); rewrite tf sra => /segmentP => lt1.
have lt2: glt (seg_order r b) (Vf f a) a.
  have h1: inc a (segment r b)  by apply/segmentP.
  have h2: inc (Vf f a) (segment r b) by apply/segmentP; order_tac.
  by apply/iorder_gltP.
have ss1: sub (segment r a) (substrate (seg_order r b)).
  rewrite srb; apply: (segment_monotone or (proj1 ltab)).
have sab: inc a (substrate (seg_order r b)) by rewrite srb; apply/segmentP.
move: h.
rewrite {1 2}/seg_order - (iorder_trans r (segment_monotone or (proj1 ltab))).
move => hh.
case:(not_le_gt (proj1 wob)  (fsincr_wor_prop wob ss1 hh  sab) lt2).
Qed.

Theorem isomorphism_worder r r': worder r -> worder r' ->
  (exists! f, iso_seg_mor r r' f) \/ (exists! f, iso_seg_mor r' r f).
Proof.
move=> wor wor'.
case: (isomorphism_worder_exists wor wor') => -[f [sf isf]].
  left;apply /unique_existence;split; first by exists f.
  move=> a b [s1 m1][s2 m2].
  by apply: (isomorphism_worder_unique wor wor'). 
right;apply /unique_existence;split; first by exists f.
move=> a b [s1 m1][s2 m2].
by apply: (isomorphism_worder_unique wor' wor). 
Qed.

(** Consequences *) 


Lemma bij_pair_isomorphism_onto_segment r r' f f':
  worder r -> worder r' -> 
  segmentp r' (Imf f) ->  order_morphism f r r' ->
  segmentp r (Imf f') ->  order_morphism f' r' r ->
  (order_isomorphism f r r' /\ order_isomorphism f' r' r /\ 
    f = inverse_fun f').
Proof. 
move=> wor wor' sr1 om sr2 om'.
move: (om)(om')=>[or or' [ff sf tf] fp]  [_ _ [ff' sf' tf'] fp'].
have gf: sgraph (graph f) by fprops.
have gf': sgraph (graph f') by fprops.
have cff': (f \coP f') by split => //; ue.
have cf'f: (f' \coP f) by split => //; ue.
have mor1 := (compose_order_morphism om' om).
have mor2 := (compose_order_morphism om om').
have fc: function (f' \co f) by fct_tac.
have srg: segmentp r (Imf (f'\co  f)). 
  split. 
    have <-: target  (f' \co f) = substrate r by aw.
    by apply: Imf_Starget.
  move=> x y.
  rewrite (ImfE fc) /compose; aw; rewrite (compg_range _ gf).
  move/dirim_P=> [u urg p2] yx.
  have xrg: (inc x (Imf f')) by rewrite (ImfE ff');ex_tac.
  have usr: inc u (source f') by Wtac.
  move: ((proj2 sr2) _ _  xrg yx) => /(Imf_P ff') [v vsf' vp].
  move: yx; rewrite (Vf_pr ff' p2) vp -fp'// => yr.
  rewrite -(ImfE ff) in urg *.
  move: ((proj2 sr1) _ _  urg yr) => va; apply /dirim_P; ex_tac; Wtac.
have srg': segmentp r' (Imf (f \co f')). 
  have fc': function (f \co f') by fct_tac.
  split. 
    have <-: target  (f \co f') = substrate r' by aw.
    by apply: Imf_Starget.
  move => x y.
  rewrite (ImfE fc') /compose; aw; rewrite (compg_range _ gf').
  move/dirim_P=> [u urg p2] yx.
  have xrg: (inc x (Imf f)) by  rewrite (ImfE ff); ex_tac.
  have usr: inc u (source f) by Wtac.
  move: ((proj2 sr1) _ _  xrg yx) => /(Imf_P ff) [v vsf' vp].
  move: yx; rewrite (Vf_pr ff p2) vp -fp// => yr.
  rewrite -(ImfE ff') in urg *.
  move: ((proj2 sr2) _ _  urg yr) => va; apply /dirim_P; ex_tac; Wtac.
have p1 := (unique_isomorphism_onto_segment wor srg mor2).
have p2 := (unique_isomorphism_onto_segment wor' srg' mor1).
rewrite - sf in p1; rewrite - sf' in p2.
have [p3 p4 p5] := (bijective_from_compose cff' cf'f  p2 p1).
by split.
Qed.


(** Two isomorphic segments of a well-ordered set are equal *)



Lemma segments_iso2 r A B: worder r ->
   inc A  (segments r) -> inc B  (segments r)  ->
   (induced_order r A) \Is (induced_order r B) -> A = B.
Proof.
move => wor.
move =>/(inc_segmentsP wor) sa /(inc_segmentsP wor) sb. 
case: (well_ordered_segment wor sa); case: (well_ordered_segment wor sb).
- by move ->.
- move =>  [x xsr ->] ->.
  by move: (segment_not_iso wor xsr); rewrite (iorder_substrate (proj1 wor)).
- move => -> [x xsr ->]; rewrite (iorder_substrate (proj1 wor)).
  by move => /orderIS h; case: (segment_not_iso wor xsr).
- move => [x xsr ->] [y ysr ->] h; apply: f_equal.
  by apply: (iso_unique_segment wor).  
Qed.


(** We rewrite [isomorphism_worder]: two well-ordered sets is isomorphic, 
or one is isomorphic to a segment of the other *)

Lemma isomorphism_worder2 r r': worder r -> worder r' ->
  [\/ r \Is r',
   (exists2 x, inc x (substrate r) & (seg_order r x) \Is r') |
   (exists2 x, inc x (substrate r') & (seg_order r' x) \Is r)].
Proof.
move => wor wor'.
case: (isomorphism_worder_exists wor wor'); move=> [f [fp1 fp2]];
    move: (order_morphism_fi fp2) => injf;
    move: fp2 => [pa pb [pc pd pe] pf].
  case : (well_ordered_segment wor' fp1) => eq1. 
    constructor 1;exists f; split => //; split => //.
    split =>//; apply: surjective_pr1 => //;apply: extensionality.
      fct_tac.
    rewrite eq1 pe; fprops.
  move: eq1 => [x xsr' rgx].  
  constructor 3; ex_tac; apply: orderIS.
  move: (@sub_segment  r' x) => p1.
  move: (iorder_osr pb p1) => [qa qb].
  exists (restriction1 f (source f)); split => //. 
    hnf;  rewrite qb /restriction1; aw; split => //.
       by apply: restriction1_fb.
    rewrite /seg_order - rgx //. 
  hnf; rewrite {1 2} /restriction1; aw; move=> a b ax bx.
  move: (@sub_refl (source f)) => ssf.
  rewrite (restriction1_V pc ssf ax) (restriction1_V pc ssf bx); split.
    move/(pf _ _ ax bx) => e1; apply/iorder_gle0P =>//; Wtac. 
  by move/iorder_gle1 => /(pf _ _ ax bx).
case : (well_ordered_segment wor fp1) => eq1.
  constructor 1;apply: orderIS; exists f; split => //.
     split => //;split =>//; apply: surjective_pr1 => //;apply: extensionality.
      fct_tac.
    rewrite eq1 pe; fprops.
move: eq1 => [x xsr rgx].
constructor 2;ex_tac; apply: orderIS.
move: (@sub_segment  r x) => p1.
move: (iorder_osr pb p1) => [qa qb].
exists (restriction1 f (source f)); split => //.
  rewrite qb /restriction1; saw; first by apply: restriction1_fb => //.
hnf; rewrite /restriction1; aw; move=> a b ax bx.
move: (@sub_refl (source f)) => ssf.
rewrite (restriction1_V pc ssf ax) (restriction1_V pc ssf bx); split.
  move/(pf _ _ ax bx) => e1; apply/iorder_gle0P =>//; rewrite -rgx; Wtac.
by move/iorder_gle1 => /(pf _ _ ax bx).
Qed.


Lemma isomorphism_worder3 r r': worder r -> worder r' ->
  (exists f, segmentp r' (Imf f) /\ order_morphism f r r')
  \/ (exists2 x, inc x (substrate r) & (seg_order r x) \Is r'). 
Proof.
move => wor wor'.
case: (isomorphism_worder_exists wor wor'); first by left.
move=> [f [fa fb]].
move: (order_morphism_fi fb) => injf.
move: fb => [or' or [ff pd pe] pf].
case : (well_ordered_segment wor fa) => eq1.
  left; exists (inverse_fun f).
  have bf: bijection f.
    by split => //; apply: (surjective_pr1 ff); rewrite pe.
  have fif:= (bijective_inv_f bf).
  have sfi: source f = target (inverse_fun f) by aw.
  have tfi: target f = source (inverse_fun f) by aw.
  rewrite (surjective_pr0 (proj2 (inverse_bij_fb bf))) - sfi pd.
  split; first by apply: substrate_segment.
  split => //; [ by  saw |  move => x y; aw => xtf ytf ].
  rewrite - {1} (inverse_V bf xtf) - {1} (inverse_V bf ytf).
  apply: iff_sym;apply:  pf; rewrite sfi; Wtac; aw.
move: eq1 => [x xsr rgx]; right;ex_tac; apply: orderIS.
move: (@sub_segment  r x) => p1.
move: (iorder_osr or p1) => [qa qb].
exists (restriction1 f (source f)); split => //.
  rewrite qb /restriction1; saw;first by apply: restriction1_fb => //.
  rewrite /restriction1; aw.
hnf;aw;move=> a b ax bx.
move: (@sub_refl (source f)) => ssf.
rewrite (restriction1_V ff ssf ax) (restriction1_V ff ssf bx); split.
  move/(pf _ _ ax bx) => e1; apply/iorder_gle0P =>//; rewrite -rgx; Wtac.
by move/iorder_gle1 => /(pf _ _ ax bx).
Qed.

(** **  EIII-2-6  Lexicographic Products *)

(** Given a family of orders [g] and an ordering [r] on the index, we compare 
   two elements [x] and [x'] of the product by comparing [x(i)] and [x'(i)] 
   where [i] is the least index where the quantities differ *)

Definition order_prod_r r g :=
  fun x x' => 
    forall j, least (induced_order r (Zo (domain g)
      (fun i =>  Vg x i <> Vg x' i))) j -> glt (Vg g j) (Vg x j)(Vg x' j).

Definition orprod_ax r g:=
  [/\ worder r, substrate r = domain g & order_fam g].

Definition order_prod r g := 
  graph_on (order_prod_r r g)(prod_of_substrates g).


(** Alternate formulation without [least_element] *)

Lemma orprod_gle1P r g:
  orprod_ax r g -> forall x x',
  (related (order_prod r g) x x' <-> 
  [/\ inc x (prod_of_substrates g),  inc x' (prod_of_substrates g) &
    forall j, least (induced_order r (Zo (domain g)
      (fun i =>  Vg x i <> Vg x' i))) j -> glt (Vg g j) (Vg x j)(Vg x' j)]).
Proof. move=> ax x x';apply/graph_on_P1. Qed.

Lemma orprod_gleP r g :  orprod_ax r g -> forall x x',
  (gle (order_prod r g) x x' <-> 
  [/\ inc x (prod_of_substrates g), inc x' (prod_of_substrates g) &
    (x= x' \/ exists j, [/\ inc j (substrate r),
      glt (Vg g j) (Vg x j) (Vg x' j) &
      forall i, glt r i j -> Vg x i = Vg x' i])]).
Proof. 
move=> la x x'.
move: (la) => [wor sr alo]; move: (proj1 wor) => or.
have He: domain (fam_of_substrates g) = domain g. 
  by rewrite /fam_of_substrates; aw.
have Hf: fgraph(fam_of_substrates g) by rewrite /fam_of_substrates; fprops.
split. 
  move/(orprod_gle1P la) => [xp x'p aux]; split => //.
  set (s := (Zo (domain g) (fun i => Vg x i <> Vg x' i))) in aux.
  have ssr: sub s (substrate r) by rewrite sr; apply: Zo_S.
  case: (emptyset_dichot s)=> nse. 
    left; apply: (setXb_exten xp x'p). 
    move=> i idf; ex_middle h; empty_tac1 i. 
    by rewrite /s; apply: Zo_i;  move: idf; rewrite /fam_of_substrates; aw.
  have [j jle] := (proj2 wor _ ssr nse).
  have jp :=(aux _ jle).
  move: jle => []; rewrite iorder_sr //;move=> js jmin.
  have jsr: inc j (substrate r) by apply: ssr.
  right; exists j; split => //; move=> i ij;  ex_middle v. 
  have iis : (inc i s) by rewrite /s; apply: Zo_i =>//;rewrite - sr;order_tac.
  move: (iorder_gle1 (jmin _ iis)) => aux'; order_tac.  
move => [xp x'p aux]; apply /(orprod_gle1P la);split => //.
set s := (Zo (domain g) (fun i  => Vg x i <> Vg x' i)). 
have ssr: (sub s (substrate r)) by rewrite sr; apply: Zo_S.
move=> j []; rewrite iorder_sr //; move => js jmin.
move /Zo_P: js =>[jdg Vj].
case: aux => haux; first by rewrite haux in Vj. 
have [i [isr lti aeq]] := haux.
have iis: inc i s by move:lti => [_ ok];apply: Zo_i =>//; ue. 
have ij := (iorder_gle1 (jmin _ iis)).
case: (equal_or_not j i) => ji; first by ue. 
have ltji: glt r j i by split.
by case: Vj; apply: aeq.
Qed.

Lemma orprod_gltP r g :  orprod_ax r g -> forall x x',
  (glt (order_prod r g) x x' <-> 
  [/\ inc x (prod_of_substrates g), inc x' (prod_of_substrates g) &
      exists j, [/\ inc j (substrate r),
      glt (Vg g j) (Vg x j) (Vg x' j) &
      forall i, glt r i j -> Vg x i = Vg x' i]]).
Proof.
move => ha x y; split => //.
  by move =>[/ (orprod_gleP ha) [qa qb qc] qd]; split => //; case: qc.
move =>[qa qb qc];  split.
  by apply/ (orprod_gleP ha); split => //; right.
by move => ea; move: qc =>[j [ _ /proj2]]; rewrite ea.
Qed.

  
Lemma orprod_osr r g:
  orprod_ax r g -> order_on (order_prod r g) (prod_of_substrates g).
Proof.
move => ax; move: (ax)=> [wor sr ao].
have osr: substrate (order_prod r g) = prod_of_substrates g.
  rewrite /order_prod graph_on_sr //.
  move=> x _ j [js _]; move: js; rewrite iorder_sr //; fprops.
    by move /Zo_hi; case.
  by rewrite sr; apply: Zo_S.
split => //.
have tor: total_order r by apply: worder_total.  
split.
+ by apply: graph_on_graph.
+ by hnf; rewrite osr => y ya; apply/(orprod_gleP ax); split => //; left.
+ move => v u w ha.
  move/(orprod_gleP ax): (ha) => [ux _]; case; first by move ->.
  move => [j1 [j1sr hu1 hu2]].
  move/(orprod_gleP ax) => [_ wx]; case;first by move <-.
  move => [j2 [j2sr hv1 hv2]]; apply/(orprod_gleP ax); split => //; right.
  case (equal_or_not j1 j2) => j12.
    exists j1; rewrite - j12 in hv1 hv2; split => //.
      rewrite sr in j1sr; exact:(lt_leq_trans (ao j1 j1sr) hu1 (proj1 hv1)).
    by move => i ha1; rewrite (hu2 _ ha1) (hv2 _ ha1).
  case:(proj2 tor _ _ j1sr j2sr) => h.
    exists j1; split => //; first by rewrite - (hv2 _ (conj h j12)).
    by move => i ia;rewrite  (hu2 _ ia) (hv2 _ (lt_leq_trans (proj1 wor) ia h)).
  exists j2; split => //; first by rewrite (hu2 _ (conj h (nesym j12))).
  by move => i ia; rewrite - (hv2 _ ia) (hu2 _ (lt_leq_trans (proj1 wor) ia h)).
move => u v.
move/(orprod_gleP ax) => [_ _]; case => // [[j1 [j1sr hu1 hu2]]].
move/(orprod_gleP ax) => [_ _]; case => // [[j2 [j2sr hv1 hv2]]].
case: (equal_or_not j1 j2) => sj.
  move: hv1 => []; rewrite - sj => hv11; rewrite sr in j1sr.
  by rewrite(order_antisymmetry (ao j1 j1sr) (proj1 hu1) hv11).
case:(proj2 tor _ _ j1sr j2sr) => h.
  by move: (hv2 _ (conj h sj)) (proj2 hu1) => ->.
by move:(hu2 _ (conj h (nesym sj))) (proj2 hv1) => ->.
Qed.

Lemma orprod_sr r g:
  orprod_ax r g -> substrate(order_prod r g) = prod_of_substrates g.
Proof. move => h;exact: (proj2 (orprod_osr h)). Qed.

Lemma orprod_or r g:
  orprod_ax r g -> order (order_prod r g).
Proof. move => h;exact: (proj1 (orprod_osr h)). Qed.

(** A product of total orders is total *)

Lemma orprod_total r g:
  orprod_ax r g ->
  (allf g total_order) ->
  total_order (order_prod r g).
Proof. 
move=> la alt.
have [ol sl] := (orprod_osr la).
have [[or wor] sr ao] := la.
split=>//; rewrite sl; move=> x y xsr ysr.
have fgf:fgraph (fam_of_substrates g) by rewrite/fam_of_substrates; fprops.
set s:=(Zo (substrate r) (fun i => Vg x i <> Vg y i)).
case: (emptyset_dichot s) => nse.
  suff xy: x = y by left; rewrite xy; order_tac; rewrite sl.
  apply: (setXb_exten xsr ysr).
  move=> i idg; ex_middle u;empty_tac1 i.
  by rewrite/s; apply: Zo_i; move: idg; rewrite/fam_of_substrates; aw; ue. 
have ssr: sub s (substrate r) by rewrite/s; apply: Zo_S. 
have  [j jle] := (wor _ ssr nse).
move: (jle)=> [];rewrite iorder_sr // => js jp.
have jdg: inc j (domain g) by rewrite - sr; apply: ssr. 
have [orj torj] := (alt _ jdg).
have px: (inc (Vg x j) (substrate (Vg g j))) by apply:prod_of_substrates_p.
have py: (inc (Vg y j) (substrate (Vg g j))) by apply:prod_of_substrates_p.
  move:ysr; rewrite /prod_of_substrates/fam_of_substrates; aw.  
have [ois sir] :=(iorder_osr or ssr). 
move: js => /Zo_hi  h h'.
case: (torj _ _ px py) => leaux.
  left; apply /(orprod_gle1P la); rewrite - sr; split => // k kl.
  rewrite - (unique_least ois jle kl); split =>//.
right; apply /(orprod_gle1P la); split => //.
have <-: s=(Zo (domain g) (fun i => Vg y i <> Vg x i)). 
   rewrite /s sr; set_extens t; move/Zo_P => [pa pb]; apply: Zo_i; fprops.
move => k kl.
by rewrite - (unique_least ois jle kl); split =>//; apply /nesym.
Qed.

(** Disjoint union of families of substrates *)

Definition sum_of_substrates g := disjointU (fam_of_substrates g).

Lemma du_index_pr1 g x: inc x (sum_of_substrates g) ->
  [/\ inc (Q x) (domain g), inc (P x) (substrate (Vg g (Q x))) & pairp x].
Proof. 
move=> xdu; move :(disjointU_hi xdu) => [].
rewrite fos_d => h; rewrite LgV// => h1; split.
Qed. 

Lemma disjoint_union_pi1 g x y:
  inc y (domain g) -> inc x (substrate (Vg g y)) ->
  inc (J x y) (sum_of_substrates g). 
Proof. by move=> ydg xsv; apply: disjointU_pi; aw; trivial; rewrite LgV. Qed.

Lemma canonical2_substrate r r':
  fam_of_substrates (variantLc r r') = variantLc (substrate r) (substrate r').
Proof. 
rewrite /fam_of_substrates /variantLc.
  apply: fgraph_exten; aww.
by move=> x xtp; rewrite LgV //;  try_lvariant xtp.  
Qed.

(** ordinal sum of a family of orders g indexed by the substrate of r *)

Definition orsum_ax r g:=
  [/\ order r, substrate r = domain g & order_fam g].

Definition order_sum_r r g x x' := 
    (glt r (Q x) (Q x') \/ (Q x = Q x' /\ gle (Vg g (Q x)) (P x) (P x'))).

Definition order_sum r g := 
  graph_on (order_sum_r r g) (sum_of_substrates g).

Section OrderSumBasic.
Variables r g: Set.
Hypothesis osa: orsum_ax r g. 

Lemma orsum_gleP x x': gle (order_sum r g) x x' <->
  [/\ inc x (sum_of_substrates g), inc x' (sum_of_substrates g) &
    order_sum_r r g x x'].
Proof. apply: graph_on_P1. Qed.

Lemma orsum_gle1 x x':
  gle (order_sum r g) x x' ->
  (glt r (Q x) (Q x') \/ (Q x = Q x' /\ gle (Vg g (Q x)) (P x) (P x'))).
Proof. by move /orsum_gleP => [_ _].  Qed.

Lemma orsum_gle2 a b a' b':
  gle (order_sum r g) (J a b)(J a' b') ->
  (glt r b b' \/ (b = b' /\ gle (Vg g b) a a')).
Proof. by move => h2; move:(orsum_gle1 h2); aw. Qed.

Lemma orsum_gle_id  x x':
  gle (order_sum r g) x x' -> gle r (Q x) (Q x').
Proof.
move /orsum_gleP => [xs _ ] [] [] => // <- _. 
move: (du_index_pr1 xs)=> [qd _ _].  
move: osa => [or srdg _]; order_tac; ue.
Qed.

Lemma orsum_or: order (order_sum r g).
Proof. 
move: osa=> [or sr alo].
rewrite /order_sum; set s := _ r g; set x:= _ g.
have ->: (graph_on s x = graph_on (fun a b => [/\ inc a x, inc b x & s a b]) x).
  by apply : Zo_exten1 => t /setX_P [_ pa pb]; split => //;move => [_ _].
apply: order_from_rel; split => //; rewrite /s/order_sum_r.
- move=> u v w [ux vx suv] [_ xw suw];split => //.
  case: suv; case: suw.
  + by left; order_tac.
  + by move=> [sq leq]; rewrite sq; left.
  + by move=> h [sq leq]; rewrite sq;left.
  + move=> [sq1 le1][sq2 le2]; right; split; first by ue. 
    move: (du_index_pr1 ux) => [qdg _ _].
    by rewrite  - sq2 in le1; move: (alo _ qdg)=> ov;  order_tac.
- move=> u v [ux vx suv] [_ _ svu]. 
  have [qudg puv pu] := (du_index_pr1 ux).
  have [qvdg pvv pv] := (du_index_pr1 vx).
  case: suv; case: svu.
  + move=> lt1 lt2; order_tac.
  + by move => [eq _] [_ lt1]; case: lt1.
  + by move => [_ lt1]  [eq _]; case: lt1.
  + move=> [eq le1][_ le2]; rewrite eq in le1; move: (alo _ qudg) => ou. 
    apply: pair_exten =>//;order_tac.
- move=> u v [ux vx suv].
  have [qudg puv pu] := (du_index_pr1 ux).
  have [qvdg pvv pv] := (du_index_pr1 vx).
  by split; split => //;right; split => //;
     [move: (alo _ qudg) | move: (alo _ qvdg) ] => ou; order_tac.
Qed.

Lemma orsum_sr: substrate (order_sum r g) = sum_of_substrates g.
Proof. 
rewrite /order_sum graph_on_sr // =>  a asg.
have [qudg puv pu] := (du_index_pr1 asg).
by right; split => //;move: osa =>[_ _ alo];move: (alo _ qudg) => ou; order_tac.
Qed.

Lemma orsum_osr: order_on (order_sum r g) (sum_of_substrates g).
Proof. by split; [apply: orsum_or | rewrite orsum_sr]. Qed.

End OrderSumBasic.

Hint Resolve orsum_or orprod_or: fprops.

Definition order_prod2 r r' :=
  order_prod canonical_doubleton_order (variantLc r' r).

Definition order_sum2 r r' :=
  order_sum canonical_doubleton_order (variantLc r r').

Lemma order_sp_axioms r r': 
  order r -> order r' -> order_fam  (variantLc r r').
Proof. 
by move => or or';hnf; aw;move=> i itp; try_lvariant itp.  
Qed.

Hint Resolve order_sp_axioms: fprops.

Section OrderSum2Basic.
Variables r r': Set.
Hypotheses (or: order r) (or': order r').

Lemma orsum2_osr: 
  order_on (order_sum2 r r') (canonical_du2 (substrate r) (substrate r')).
Proof.
move: cdo_wor => [[ord _ ] sr].
have aw: orsum_ax canonical_doubleton_order (variantLc r r').
   by  split => //; aw; fprops.
split; first by apply: orsum_or.
rewrite  orsum_sr // /canonical_du2 /order_sum2 /sum_of_substrates. 
rewrite canonical2_substrate //.  
Qed.

Lemma orprod2_osr: 
  order_on (order_prod2 r r')(product2 (substrate r')  (substrate r)).
Proof.
have [wor sr] := cdo_wor.
have aux: orprod_ax canonical_doubleton_order (variantLc r' r).
  by split => //; aw; fprops.
split; first by apply: orprod_or.
rewrite /order_prod2 orprod_sr // /prod_of_substrates canonical2_substrate //.
Qed.

Lemma orsum2_or: order (order_sum2 r r').
Proof. exact: (proj1 orsum2_osr). Qed.

Lemma orsum2_sr: 
  substrate (order_sum2 r r') = canonical_du2 (substrate r) (substrate r').
Proof.  exact: (proj2 orsum2_osr). Qed.


Lemma orprod2_or: order (order_prod2 r r').
Proof. exact: (proj1 orprod2_osr). Qed.

Lemma orprod2_sr: 
  substrate(order_prod2 r r') = product2 (substrate r')  (substrate r).
Proof. exact: (proj2 orprod2_osr). Qed.


Lemma orsum2_gleP x x':
  gle (order_sum2 r r') x x' <->
  [/\ inc x (canonical_du2 (substrate r) (substrate r')),
    inc x' (canonical_du2 (substrate r) (substrate r')) &
    [\/ [/\ Q x = C0, Q x' = C0 & gle r (P x) (P x')],
        [/\ Q x <> C0, Q x' <> C0 & gle r' (P x) (P x')] |
        (Q x = C0 /\ Q x' <> C0)]].
Proof. 
have Ha: C1 <> C0 by fprops.
set S1:= (canonical_du2 (substrate r) (substrate r')).
have S1p: S1 =  (sum_of_substrates (variantLc r r')).
  by rewrite /sum_of_substrates  canonical2_substrate.
split. 
  move /orsum_gleP; rewrite - S1p.
  move=> [xs xns' osr]; split => //; move: osr => [] [].
    move /cdo_gleP => aux nsQ;case: aux.
      by move=> [e1 e2];  rewrite e1 e2 in nsQ;case: nsQ.
    case; first by move=> e1 e2; rewrite e1 e2 in nsQ; case: nsQ.
    move=> [e1 e2];  constructor 3; rewrite e2; split => //.
  move=> <-.
  case: (candu2_pr2 xs) => ->; aw; [constructor 1| constructor 2]; split => //. 
move=> [xs1 x's1 etc]; apply/orsum_gleP; split => //; try ue.
case: etc.
   move=> [qxa qx'a lrxx']; right; rewrite qxa qx'a; aw;split => //.
  move=> [qxa qx'a lrxx']; right.
  have ->:  (Q x' = C1) by case: (candu2_pr2 x's1) => //.
  have ->:  (Q x = C1)  by case: (candu2_pr2 xs1) => //.
  aw; split => //.
move=> [qxa qx'a]; left; rewrite qxa.
have ->: Q x' = C1 by case: (candu2_pr2 x's1) => //.
apply: cdo_glt1.
Qed.

Lemma orsum2_gle_spec x x':
  inc x (substrate r) -> inc x' (substrate r') ->
  glt (order_sum2 r r') (J x C0) (J x' C1).
Proof. 
move=> xsr xsr'; split; last by move => h; move: (pr2_def h); fprops.
apply /orsum2_gleP; split; first by apply: candu2_pra.
  by apply: candu2_prb.
constructor 3; aw; split; fprops.
Qed.

Lemma orprod2_gleP  a b:
  gle (order_prod2 r r') a b <->
  [/\ inc a  (product2 (substrate r') (substrate r)),
     inc b  (product2 (substrate r') (substrate r))&
    ( (Vg a C0 = Vg b C0 /\ gle r (Vg a C1) (Vg b C1)) 
      \/ (glt r' (Vg a C0)(Vg b C0)))].
Proof.
have [wor sr] := cdo_wor.
have la:  orprod_ax canonical_doubleton_order (variantLc r' r).
  by split => //; aw; fprops.
apply: (iff_trans (orprod_gleP la a b)).
have ->: prod_of_substrates (variantLc r' r) =
     (product2 (substrate r') (substrate r)).
  rewrite  - orprod2_sr // /order_prod2 orprod_sr //.
rewrite (proj2 cdo_wor).
split; move => [ap2 bp2 h];split => //. 
  case: h.
     move => <-; left;split => //; order_tac. 
     by move: ap2 => / setX2_P [_ _ _]. 
  move=> [j [ /C2_P [] ->]]; aw;first by move => h _; right.
  move=> p1 p2.
  by move: (p2 _ cdo_glt1) => p4; move: p1 => [p1 _]; left.
case: h. 
  move=> [p1 p2]; case: (equal_or_not  (Vg a C1) (Vg b C1)).
    move:ap2 bp2 => /setX2_P [fga da Vaa VBa].
    move => /setX2_P  [fgb db Vab VBb].
    move=> VV; left; apply: fgraph_exten =>//; first by ue. 
    by rewrite da; move=> ix xda;try_lvariant xda. 
  move => nVV; right; exists C1; split => //; fprops; aw; first by split.
  move=> i [] /cdo_gleP p3 p4; case: p3; [ | by case | by move=> [-> _]].
  by move=> [r1 r2]; rewrite -r2 in r1. 
move => pa; right; exists C0;aw;split => //; fprops.
move=> i [] /cdo_gleP []; case => // -> -> //.
Qed.

End OrderSum2Basic.

Lemma orprod2_totalorder r r':
  total_order r -> total_order r' -> total_order (order_prod2 r r').
Proof.
move: cdo_wor => [ha hb].
move => pa pb; move:(pa)(pb) => [oa _][ob _]; apply: orprod_total.
  split => //; [ by aw | by hnf; aw => x xi; try_lvariant xi].
by hnf;aw => x xi; try_lvariant xi.
Qed.

Lemma order_prod_pr r r': order r -> order r' ->
 (order_prod2 r r') \Is (order_sum r' (cst_graph (substrate r') r)).
Proof.
move => or or'. 
have oa: (orsum_ax r' (cst_graph (substrate r') r)).
  by hnf; saw; hnf; aw;move=> i isr ;rewrite LgV.
set fo:=order_sum r' (cst_graph (substrate r') r).
have odf: order fo by rewrite /fo; fprops.
move: (orsum_sr oa) => s1.
move: (orprod2_or or or').
move: (orprod2_sr or or'). 
set io := order_prod2 r r'; move => s2 o2.
pose f x := J (Vg x C1) (Vg x C0).
have ta: (lf_axiom f (substrate io) (substrate  fo)). 
  move=> t; rewrite /fo s1 s2; move /setX2_P => [fgt dt va vb]. 
  by apply: disjointU_pi; aw; trivial; rewrite !LgV//; aw.
have bf: bijection (Lf f (substrate io) (substrate fo)).
  apply: lf_bijective =>//. 
    move=> u v;rewrite s2 /f; move=> ud vd eq.
    move: (pr2_def eq)(pr1_def eq) => p1 p2.
    by apply: (setXf_exten ud vd); move=> i itp;  try_lvariant itp.
  rewrite s1 /fam_of_substrates  /cst_graph.
  move=> y ys; move:(du_index_pr1 ys); rewrite Lgd.
  move=> [Qsr]; rewrite LgV//; move=> Psr py.
  exists (variantLc (Q y) (P y)).
    rewrite s2; apply /setX2_P;split => //; aww.
  by symmetry;rewrite /f; aw.
exists (Lf f (substrate io) (substrate fo));hnf; split => //.
   saw.
hnf; aw; move=> x y xs ys; aw.
move : (ta _ xs) (ta _ ys) => qa qb.
have p1: inc (Vg x C0) (substrate r').
  by  move: xs; rewrite s2; move /setX2_P => [_ _ ].
apply (iff_trans (orprod2_gleP or or' _ _)); rewrite - s2.
symmetry; apply (iff_trans (orsum_gleP _ _ _ _)).
have ->: sum_of_substrates (cst_graph (substrate r') r) = substrate fo by aw.
rewrite !LfV //.
split; move => [_ _ xx]; split => //; move: xx;
 rewrite /f /order_sum_r !pr1_pair !pr2_pair !LgV //; case; fprops.
Qed.

Lemma orsum_total r g:
  orsum_ax r g -> total_order r ->
  (forall i, inc i (domain g) -> total_order (Vg g i)) ->
  total_order (order_sum r g).
Proof. 
move=> oa  [_ tor] alt; rewrite /total_order.
move: (oa) => [or sr alo]; rewrite orsum_sr //.
rewrite sr in tor.
split =>//; first by fprops.
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
have [ha hb] := cdo_wor.
have hc:= (worder_total ha).
have hd := proj1 ha.
move => pa pb; move:(pa)(pb) => [oa _][ob _];  apply: orsum_total => //.
   hnf; split => //; [ by aw | by hnf; aw => x xi; try_lvariant xi].
by hnf;aw => x xi; try_lvariant xi.
Qed.

Lemma orsum_wor r g: 
  worder_on r (domain g) ->  worder_fam g ->
  worder (order_sum r g). 
Proof.
move=> [wor sr] alw; move: (proj1 wor) => or.
have oa: orsum_ax r g by split => // i ie; exact (proj1 (alw _ ie)).
apply:(worder_prop_rev (orsum_or oa)); rewrite orsum_sr // => x xs [x0 x0x].
set A := fun_image x Q. 
have Asr: (sub A (substrate r)).
  move=> t /funI_P [z zx ->].
  rewrite sr;exact (proj31 (du_index_pr1 (xs _ zx))).
have neA: nonempty A by exists (Q x0); apply /funI_P; ex_tac.
move: (worder_prop wor Asr neA)=> [a aA ale].
set B:= Zo x (fun z => Q z = a).
set C := fun_image B P.
move: (Asr _ aA); rewrite sr => adg.
have Cs: (sub C (substrate (Vg g a))). 
  move=> t /funI_P  [z zB ->].  
  move: zB => /Zo_P [zx] <-; exact (proj32 (du_index_pr1 (xs _ zx))).  
have neC: nonempty C.
  move: aA => /funI_P [z zx qz].
  by exists (P z); apply /funI_P;exists z => //; apply: Zo_i.
move: (worder_prop (alw _ adg) Cs neC)=> [b bC leB].
have Jx: inc (J b a) x.
   move: bC => /funI_P [z /Zo_P [zx <-] ->].
   by rewrite (proj33 (du_index_pr1 (xs _ zx))). 
have ors: order (order_sum r g) by fprops.
ex_tac => c cx.
move: (du_index_pr1 (xs _ cx))=> [Qc Pc pc]. 
apply /orsum_gleP;split; fprops.
hnf; rewrite pr1_pair pr2_pair. 
have QcA:  (inc (Q c) A) by apply /funI_P; ex_tac.
move: (ale _ QcA) => leac.
case: (equal_or_not a (Q c)). 
  move=> aQc; right;split => //.
  have Pcb: (inc (P c) C) by apply/funI_P; exists c => //; apply: Zo_i.
  exact: (leB _ Pcb).
by move => nac; left.
Qed.

End Worder.
Export Worder.
