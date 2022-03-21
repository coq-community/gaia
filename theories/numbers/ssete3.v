(** * Theory of Sets : Exercises sections 2 and 3 
  Copyright INRIA (2009-2014 2018) Apics/Marelle Team (Jose Grimm). 
*)
(* $Id: ssete3.v,v 1.5 2018/09/04 07:58:00 grimm Exp $ *)

From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Export sset14 ssete1 ssete2.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Exercise3.

(** ---- Exercise 2.1. The maximal elements for [finer_order]  are total orders; 
any ordering is the intersection of all total orderings that extent it; 
an ordering is isomorphic to a subset of a product of total orders *)

Lemma induced_sub_pr1 r X x:
  (forall a b, gle r a b -> sub a b) ->
  upper_bound r X x -> sub (union X) x.
Proof. 
move=>  h [xs ub] t /setU_P [y ty yX].
by apply: (h _ _ (ub _ yX)).
Qed.

Lemma induced_sub_pr2 r X:
  order r ->
  (forall a b, inc a (substrate r) -> inc b (substrate r) ->
    (gle r a b <-> sub a b)) ->
  sub X (substrate r) -> inc (union X) (substrate r) ->
  least_upper_bound r X (union X).
Proof.
move=> or rs Xsr Usr. 
apply /(lubP or Xsr); split.
  split => // y yx; apply/rs=> // ;[ by apply: Xsr | by apply: setU_s1 ]. 
move=> z zu; move: (zu)=> [zr zu1]; apply/rs => //.
apply: (induced_sub_pr1 (r:=r)) =>// a b ab; rewrite -rs //; order_tac.
Qed.

Lemma inc_coarse a b E: inc a E -> inc b E ->
  inc (J a b) (coarse E).
Proof. move=> aE bE; apply /setXp_P; split => //. Qed.

Definition orders x := Zo (\Po (coarse x))(order_on ^~ x).

Lemma ordersP x z:
  inc z (orders x) <-> (order_on z x).
Proof. 
split; [by move /Zo_hi | move => h; apply: Zo_i => //].
apply /setP_P; move: h => [or <-].
apply: sub_graph_coarse_substrate; fprops.
Qed.

Definition finer_order x := sub_order (orders x). 

Lemma fo_osr x: order_on (finer_order x)(orders x).
Proof. apply: sub_osr. Qed.

Lemma fo_gleP x u v:
  gle (finer_order x) u v <->
  [/\ order u, order v, substrate u = x, substrate v = x & sub u v].
Proof.
split. 
 by move /sub_gleP => [] /ordersP [pa pb] /ordersP [pd pe] pf.
move => [pa pb pc pd pe]. 
by apply /sub_gleP;split => //; apply/ordersP.
Qed.

Lemma fo_gle1P x u v:
  gle (finer_order x) u v <->
  [/\ order u, order v, substrate u = x, substrate v = x &
  forall a b, inc a x -> inc b x -> gle u a b -> gle v a b].
Proof. 
split.
  move /fo_gleP => [ou ov su sv h]; split => //.
  by move=> a b ax bx ab; apply: h.
move => [ou ov su sv h]; apply /fo_gleP;split => //.
have gu: (sgraph u) by fprops.
move=> t tu.
have pt : (pairp t) by apply: gu. 
move: tu;rewrite -pt => tu.
have p1: (inc (P t) x) by rewrite - su; substr_tac. 
have p2: (inc (Q t) x) by rewrite - su; substr_tac. 
by apply: (h _ _ p1 p2). 
Qed.

Lemma Exercise2_1a r x y
  (E :=  substrate r)
  (r':= r \cup (Zo (coarse E)(fun z=>  gle r (P z) x /\ gle r y (Q z)))):
  order r -> inc x (substrate r) -> inc y (substrate r) ->
  ~ gle r y x -> 
  (gle (finer_order E) r r' /\ inc (J x y) r').
Proof. 
move=> or xsr ysr h; split; last first.
  apply: setU2_2; apply:Zo_i; first by apply:inc_coarse. 
  by saw; order_tac.
apply/fo_gleP.
have gr: sgraph r by fprops.
have gr': sgraph r'.   
  by move=> t /setU2_P; case; [ apply: gr | move => /Zo_P [] /setX_P []].
have sr1: forall a b, inc (J a b) r' -> (inc a E /\ inc b E).
  move => a b; case /setU2_P; first by move => pr; rewrite /E; split;substr_tac.
  by move => /Zo_S/setXp_P.
have sr': substrate r' = E. 
  set_extens t.
      by move /(substrate_P gr');case; move => [z si]; case: (sr1 _ _ si).
 by move =>  tE; apply: (@arg1_sr r' t t); apply /setU2_P; left; order_tac.
split => //; last by apply: subsetU2l.
split => //. 
    by move => a; rewrite sr' => aE; apply: setU2_1; order_tac.
  move => a b c pa pb.
  have ae: inc a E by rewrite - sr'; substr_tac.
  have be: inc b E by rewrite - sr'; substr_tac.
  have ce: inc c E by rewrite - sr'; substr_tac.
  have jc: inc (J b c) (coarse E) by apply : inc_coarse.
  case /setU2_P : pa=>  pa.
    case  /setU2_P: pb => pb; first by apply /setU2_P; left; order_tac.
    apply /setU2_P; right;apply /Zo_P; saw. 
    move /Zo_P: pb => [pb []]; aw;  rewrite /gle/related => pc pd. 
    split => //;order_tac.
  apply /setU2_P; right;apply /Zo_P; saw.
  move /Zo_P: pa => [pa []]; aw; rewrite /gle/related => pc pd.
  case  /setU2_P: pb => pb; first by split => //; order_tac.
  move /Zo_P: pb => [pb []]; aw; rewrite /gle/related => pe pf. 
  split => //; order_tac.
move => a b pa pb.
case /setU2_P : pa=>  pa.
  case  /setU2_P: pb => pb; first by order_tac.
  move /Zo_P: pb => [pb []]; aw => pc pd; case: h.
  have ab:gle r a b by done.
  have ax:gle r a x by order_tac.
  order_tac.
move /Zo_P: pa => [pa []]; aw => qa qb.
case  /setU2_P: pb => pb; case: h.
  have ab:gle r b a by done.
  have ax:gle r y a by order_tac.
  order_tac.
move /Zo_P: pb => [pb []]; aw => pc pd; order_tac.
Qed.

Lemma Exercise2_1bP E r:
  maximal (finer_order E) r <-> (total_order r /\ substrate r = E).
Proof. 
rewrite /maximal (proj2 (fo_osr _)); split.
  move=>  [] /ordersP [oa sa] ha; split => //; split =>//.
  move=> x y xsr ysr; case: (p_or_not_p (gle r y x)) => ngge; first by right.
  by left; case(Exercise2_1a oa xsr ysr ngge); rewrite sa; move/ha ->.
move=> [[oa ta] sa]; split => //; first by apply  /ordersP;split => //.
move=> x /fo_gle1P [_ ox _ sx sv].
symmetry; apply: order_exten => // u v;split => h. 
   apply: sv =>//; rewrite - sa; order_tac.
move:(arg1_sr h)(arg2_sr h); rewrite sx => usr vsr.
rewrite sa in ta; case: (ta _ _ usr vsr) => //.
move => uv; move: (sv _ _ vsr usr uv) => h'. 
move: uv; have -> //: u = v by order_tac.
Qed.

Lemma fo_inductive E: inductive (finer_order E).
Proof. 
move=> X XsE tX.
move:(fo_osr E) => [or sr].
case: (emptyset_dichot X) => xE.
  exists (diagonal E); split; last by rewrite xE => y /in_set0.
  rewrite sr;apply /ordersP; exact: (diagonal_osr E). 
have pa: forall x, inc x X -> (order_on x E).
  by move=> x xX; move: (XsE _ xX); rewrite sr =>  /ordersP.
move: xE => [w wX]; move: (pa _ wX) => [sw ow].
exists (union X).
set r:=finer_order E.
have op: (forall a b, inc a (substrate r) -> inc b (substrate r) ->
    (gle r a b <-> sub a b)). 
  move=> x y xsr ysr; split; first by move /fo_gleP => [_ _ _ _].
  move => sa; apply /fo_gleP.
  by move: xsr ysr;rewrite sr => /ordersP[ra rb] /ordersP [rc rd].
have oq a b: inc a (substrate r) -> inc b (substrate r) -> gle r a b -> sub a b.  by move => ha hb hc; apply/op.
have ug: (sgraph (union X)). 
  move=> y /setU_P [z yz zX];move: (pa _ zX) =>  [oz _].
  by apply: (order_sgraph oz).
have su: (substrate (union X) = E).
  set_extens t. 
   move /(substrate_P ug); case; move=> [y] => /setU_P [z Jz zX];
      move: (pa _ zX); move=> [oe <-]; substr_tac.
  move => te. 
  have Jx: (inc (J t t) w) by order_tac; ue.
  have jy: inc (J t t) (union X) by union_tac.
  substr_tac.
move: tX => [orX]; rewrite iorder_sr // => tX.
suff usr: (inc (union X) (substrate r)). 
  by move: (induced_sub_pr2 or op XsE usr) => /(lubP or XsE) [].
rewrite /r sr; apply /ordersP;split => //.
split => //.
    move => t; rewrite su => te; apply /setU_P; exists w => //; order_tac; ue.
  move => y x z /setU_P [a Ja aX] /setU_P [b Jb bX].
  move: (pa _ aX) (pa _ bX) =>  [sa oa] [sb ob].
  move: (XsE _ aX) (XsE _ bX) => asr bsr.
  case: (tX _ _ aX bX); move=> ab;move:(iorder_gle1 ab)=> cp.
    exact:(setU_i (proj43 sb _ _ _  (oq a b asr bsr cp _ Ja) Jb) bX). 
  exact:(setU_i(proj43 sa _ _ _ Ja (oq b a bsr asr cp _ Jb)) aX).
move => x y /setU_P [a Ja aX] /setU_P [b Jb bX].
move: (pa _ aX) (pa _ bX) =>  [sa oa] [sb ob].
have ia: inc a (substrate r) by apply: XsE.
have ib: inc b (substrate r) by apply: XsE.
case: (tX _ _ aX bX); move=> ab;move:(iorder_gle1 ab) => cp.
  move:(oq _ _ ia ib cp _ Ja)=> Jb'; order_tac.
move:(oq _ _ ib ia cp _ Jb)=> Jb'; order_tac.
Qed.

Lemma order_total_extension r: order r ->
  exists r', [/\ total_order r', substrate r' = substrate r & sub r r'].
Proof.
move=> or.
set (E:= substrate r).
move: (fo_osr E) => [or1 sr1].
have rr: (inc r (substrate (finer_order E))) by rewrite sr1; apply /ordersP. 
move: (inductive_max_greater or1 (@fo_inductive E) rr) => [m]. 
move/ Exercise2_1bP => [tm sm] /fo_gleP [_ _ _ _ rm].
by exists m.
Qed.

Lemma Exercise2_1c r: 
 order r -> r = intersection (Zo (orders (substrate r))
   (fun r' => total_order r' /\ sub r r')).
Proof. 
move=> or; set bs:= Zo _ _. 
move: (order_total_extension or) => [r' [tor' sr' sr]].
have rb': (inc r' bs). 
  by apply: Zo_i => //; apply /ordersP; split => //; move: tor'=> [or'_ ].
set_extens t.
   move => tr;apply: setI_i;first by ex_tac.
   by move=> y => /Zo_hi [_ ]; apply.
move=> tb; move: (setI_hi tb rb') => tr'.
move: tor'=> [or' tor'].
have pt: (pairp t) by apply: (order_sgraph or'). 
have tp: (t = J (P t) (Q t)) by aw. 
rewrite tp in tr'.
have p1: (inc (P t) (substrate r)) by rewrite - sr'; substr_tac.
have p2: (inc (Q t) (substrate r)) by rewrite - sr'; substr_tac.
case: (p_or_not_p (gle r (P t) (Q t))); first by rewrite /gle/related -tp.
move=> grqp.
move:(Exercise2_1a or p2 p1 grqp)=> /=.
set r'':= union2 _ _.
move => [] /fo_gleP [_ or'' _ sr'' rr''] Jr''.
move: (order_total_extension or'')=> [r''' [tr''' sr''' srr]].
move: (tr''') => [o3 _].
have aux: (inc r''' bs).
   apply: Zo_i; last by split => //;apply: sub_trans srr.
  by apply /ordersP;split => //; transitivity (substrate r'').
move:(setI_hi tb aux)  (srr _ Jr''); rewrite {1} tp => p3 p4.
have pq: (P t = Q t) by order_tac.
by rewrite tp pq;order_tac.
Qed.

Lemma Exercise2_1d r: order r -> exists g h,
  [/\ order_fam g,
   (allf g total_order) &
  order_morphism h r (order_product g)].
Proof. 
move=> or.
move: (Exercise2_1c or);set bs :=  Zo _ _ => rp.
set (g:= Lg bs id).
have poa: order_fam g.
  rewrite /g;hnf; aw; move=> i ib; rewrite LgV//.
  by  move: ib =>/Zo_P [_ [[oi _] _]].
set (h := Lf (cst_graph bs)  (substrate r) (prod_of_substrates g)).
exists g, h; split => //.
  by rewrite /g; hnf;aw; move=> i idg; rewrite LgV//; move: idg =>  /Zo_hi [].
move: (order_total_extension or) => [x [tox sx rx]].
move: (tox)=> [ox _].
have xb: (inc x bs) by apply: Zo_i=> //; apply /ordersP.
have ta: (lf_axiom  (cst_graph bs) (substrate r) (prod_of_substrates g)).
  move=> y ysr; apply /setXf_P; rewrite /cst_graph /g !Lgd;split;fprops.
  move => j jb; rewrite !LgV//.
  by move: jb =>/Zo_P [] /ordersP [_ ->].
move: (order_product_osr poa) => [o1 s1].
rewrite /h; split => //.
  saw; [ by apply: lf_function | done ].
red;aw;move=> u v usr vsr; rewrite !LfV//; split.
  move => h1; apply /order_product_gleP;split;fprops.
  rewrite /g /cst_graph; aw; move=> i idg; rewrite !LgV//.
  by move: idg => /Zo_hi [_ ]; apply.
move/order_product_gleP => [_ _]; rewrite /g/cst_graph;aw => h1. 
hnf;rewrite (Exercise2_1c or) -/bs; apply:setI_i; first by ex_tac.
by move=> y yb; move: (h1 _ yb); rewrite ! LgV.
Qed.

(** ---- Exercise 2.2. Applying Zorn's lemma to some specific ordering says: 
in any ordered set, there is at least one well-ordered subset that has no 
strict upper bound  *)

Lemma Exercise2_2a r
   (B:= Zo (\Po (substrate r)) (fun z=> worder (induced_order r z)))
   (sso := Zo (coarse B)(fun z=> segmentp (induced_order r (Q z)) (P z))):
   order r ->
   (order_on sso B /\ inductive sso).
Proof.
move=> or.
have HaP: forall x y, gle sso x y <->
    [/\ inc x B, inc y B & segmentp (induced_order r y) x].
  move=> x y; split; first by move => /Zo_P [] /setXp_P []; aw.
  move => [pa pb pc]; apply /Zo_P;split => //; [ by apply /setXp_P | by aw ].
have Hb: sgraph sso by move=> t => /Zo_P [] /setX_P [].
have Hc: forall x y, gle sso x y -> sub x y.
   move=> x y => /HaP  [_ ]  /Zo_P [] /setP_P ysr _; case; rewrite iorder_sr //.
have Hf: forall x, inc x B -> sub x (substrate r).
  by move=> x /Zo_P [ ] /setP_P.
have Hd: forall x, inc x B -> gle sso x x.
  move=> x xB; apply /HaP; split => //;split; first by rewrite iorder_sr; fprops. 
  by move=> a b ax /(iorder_gle3); case. 
have He:substrate sso = B. 
  set_extens t. 
     by case /(substrate_P Hb) => [] [y] /Zo_P [] /setXp_P [].
  move=> /Hd; rewrite /gle=> Js ; substr_tac.
have os: order sso.
  split => //.
      move => t; rewrite He; apply: Hd.
    move => y x z /HaP [xB yB [xs p1]] /HaP [_ zB [ys p2]].
    apply /HaP;split => //;  move: (Hf _ xB)(Hf _ yB)(Hf _ zB) => xs1 ys1 zs1.
    move: xs ys; rewrite iorder_sr // => xs ys.
    split; first by aw ; apply: (@sub_trans  y). 
    move=> a b ax p3; move: (iorder_gle1 p3) (iorder_gle3 p3)=> ba [bz az].
    apply: (p1 _ _ ax); apply /iorder_gle0P => //; last by apply: xs.
    by apply: (p2 _ _ (xs _ ax)); aw.
  by move => // x y r1 r2;  apply: extensionality; apply: Hc.
split => //.
red;rewrite He => X XE toi.
have su: (sub  (union X) (substrate r)).
  move=> t /setU_P [y ty yX]; exact: (Hf _ (XE _ yX)).
move: (iorder_osr or su) => [o1 sr1].
have woi: worder (induced_order r (union X)). 
  split => //; rewrite sr1.
  move => x xu [a ax];move: (xu _ ax) => /setU_P [b ab bX].
  set (Z := x \cap b). 
  have neZ:(nonempty Z) by exists a; apply: setI2_i.
  move: (XE _ bX) => /Zo_P [] /setP_P bsr [wo1 ]; rewrite iorder_sr // =>wo2.
  have p1: (sub Z b) by apply: subsetI2r.
  move: (wo2 _ p1 neZ) => [y]; aw; rewrite iorder_trans //.
  have Z1: (sub Z (substrate r)) by apply: (sub_trans p1).
  have xr: sub x (substrate r) by apply: sub_trans su.
  rewrite iorder_trans //; move=> []; rewrite iorder_sr//; move=> yZ yp.
  have yx:= (@setI2_1 x b _ yZ).
  exists y; red;rewrite iorder_sr //; split => // z zx; aw.
  move: (xu _ zx) => /setU_P [t zt tX].
  move: toi => [toi1]; rewrite iorder_sr //; last by ue. 
  move=> aux; move: (aux _ _ tX bX). 
  case => h1; move:(iorder_gle1 h1) => h2;move: (Hc _ _ h2) => h3.
    have zZ: inc z Z by apply: setI2_i => //; apply: h3.
    apply /iorder_gle0P => //.  
    exact:(iorder_gle1 (yp _ zZ) ).
  have yb: inc y b by apply: p1. 
  have yt: inc y t by apply: h3.
  move :(XE _ tX) => /Zo_P [xx wor]. 
  have st: sub t (substrate r) by move: xx => /setP_P.
  move: (worder_total wor) => [_ ]; rewrite iorder_sr // => tor.
  apply /iorder_gle0P => //.
  case: (tor _ _ yt zt)=> h4; first exact: (iorder_gle1  h4).
  move: h2 => /HaP [_ _ [_ se]].
  move: (se _ _ yb h4) => zb.
  have zZ: inc z Z by apply: setI2_i => //; apply: h3.
  exact: (iorder_gle1(yp _ zZ)).
have uXb:inc (union X) B by apply: Zo_i => //; apply /setP_P.
exists (union X); split; first by rewrite He.
move => y yX; apply /HaP;split;fprops.
split; first by rewrite iorder_sr//; apply: setU_s1 => //. 
move=> u v uy uv; move: (iorder_gle1 uv) => vu.
move:(iorder_gle3 uv)=> [vU uU]. 
move: vU => /setU_P [w uw wX].
move:toi => [_ ]; rewrite iorder_sr //; last by ue.  
move=> h; move: (h _ _ yX wX).
case => h1; move: (iorder_gle1 h1) => aux; move: (Hc _ _ aux); last by apply.
move: aux => /HaP [yB wB [s1 s2]] yw.
apply: (s2 _ _ uy); apply /iorder_gle0P=> //; apply: yw; fprops.
Qed.

Lemma Exercise2_2b  r: order r ->
  exists x, [/\ sub x (substrate r), worder (induced_order r x) &
    forall z, upper_bound r x z -> inc z x].
Proof. 
move=> or; move: (Exercise2_2a or).
set B:= Zo (\Po _)  _. 
set ss_order := Zo _ _.
move => [[sso sss] iss].
move: (Zorn_lemma sso iss)=> [a [ais am]]. 
move:(ais); rewrite sss => /Zo_P [] /setP_P asr woia.
exists a; split => // z [zsr zu].
set (y:= a +s1 z).
have zy: inc z y by rewrite /y;fprops.
rewrite -(am y)  //. 
have ysr: (sub y (substrate r)).
  move=> t /setU1_P; case ; [apply: asr| by move => ->].
apply: Zo_i.
  move: (iorder_osr or ysr) => [pr1 sr1].
  apply /setXp_P;split => //;first (by ue); apply: Zo_i;first by apply /setP_P.
  split => //; rewrite sr1 => x xy nex.
  set (t:= x \cap a). 
  have Ha: sub t a by apply: subsetI2r. 
  have Hb: sub t y.  
    by apply: (@sub_trans  x) => //;  apply: subsetI2l.  
  have Hc: sub t (substrate r) by apply: (@sub_trans y). 
  have Hd: sub x (substrate r) by apply: (@sub_trans y). 
  rewrite iorder_trans //.
  case: (emptyset_dichot t) => te.
    have xs: (forall u, inc u x -> u = z).
      move=> u ux; move: (xy _ ux); case /setU1_P => //.
      by move=> ua; empty_tac1 u; apply: setI2_i.
    move: nex => [w wx]; move: (xs _ wx) => wz.
    exists w; red; rewrite iorder_sr //;split => //.
    move => // v vx; apply /iorder_gleP;split => //; rewrite  (xs _ vx) - wz.
    by order_tac; apply: Hd.
  move: woia => [_]; rewrite iorder_sr //; move=> h; move: (h _ Ha te) => [w]. 
  rewrite iorder_trans //; move=> []; rewrite iorder_sr//;move=> ws wl;exists w.
  have wx: inc w x by apply: (@setI2_1 x a).
  red; rewrite iorder_sr//;split => // v vx; apply /iorder_gle0P=> //.
  move: (xy _ vx); case /setU1_P => //.
    move=> va; exact: (iorder_gle1 (wl _ (setI2_i vx va))).
  move => ->; exact: (zu _ (Ha _ ws)).
aw;split; first by rewrite iorder_sr//; move=> t; rewrite /y; fprops.
move=> u v xa h; move: (iorder_gle3 h)(iorder_gle1 h)  => [vy uy] vu.
move: vy; case /setU2_P => // /set1_P vz.
move: (zu _ xa); rewrite -vz => uz. 
by rewrite (order_antisymmetry or vu uz).
Qed.

(** ---- Exercise 2.3. Any set can be partitioned into a well-ordered set 
and a set that has no least element; We give an example where there 
are many solutions   *)

Lemma complement_p1 C A B:
  A \cup B = C -> A \cap B = emptyset ->
  (sub A C /\ A = C -s B).
Proof.
move => uab iab.
have sa: sub A C by move=> t tA; rewrite -uab; fprops.
have sb: sub B C by move=> t tB; rewrite -uab; fprops.
split => //;  set_extens t.
  move=> tA; apply /setC_P;split => //; first by apply: sa.
  by move=> tB; empty_tac1 t; apply: setI2_i.
rewrite - uab; move /setC_P => [tc tb]; case /setU2_P: tc => //.
Qed.

Lemma complement_p2 C A B:
  A \cup B = C -> A \cap B = emptyset ->
  (sub B C /\ B = C -s A).
Proof. rewrite setI2_C setU2_C; apply: complement_p1. Qed.

Lemma complement_p3 C B (A:= C -s B):
  sub B C ->  (A \cup B = C /\ A \cap B = emptyset).
Proof.
move=> BC; rewrite /A;split.
  set_extens t.
    case /setU2_P; [ by move => /setC_P  [] | apply: BC ].
  move => tC; case:(inc_or_not t B) => tB; apply /setU2_P; [right | left] =>//.
  by apply /setC_P.
by apply /set0_P => y /setI2_P [] /setC_P [].
Qed.

Lemma complement_p4 C A (B:= C -s A):
  sub A C -> (A \cup B = C /\ A \cap B = emptyset).
Proof. rewrite setI2_C setU2_C; apply: complement_p3. Qed.


Lemma Nat_greatest A: sub A Nat -> nonempty A ->
  (exists x, upper_bound Nat_order A x) ->
  (has_greatest (induced_order Nat_order A)).
Proof.
move=> AB  neA [w [_ wp]].
move:Nat_order_wor => [wor sr];move:(proj1 wor) => or.
have asr: sub A (substrate Nat_order) by ue.
apply: finite_set_torder_greatest; rewrite ? iorder_sr//. 
  apply: (total_order_sub (worder_total wor) asr).
apply: sub_finite_set (finite_Nintcc \0c w).
by move => t /wp /Nat_order_leP [_ wN le]; apply/(NintcP wN).
Qed.
 
Definition ex23_prop r A B:= 
  [/\ A \cup B = substrate r, A \cap B = emptyset, 
  worder (induced_order r A) &
  ~ (has_least (induced_order r B))].


Lemma Exercise2_3a r: order r -> exists A B, ex23_prop r A B.
Proof.
move=> or.
pose no_least B :=  ~ has_least (induced_order r B).
set (B:= union (Zo (\Po (substrate r)) no_least)).
have Bsr: (sub B (substrate r)). 
   by move=> t /setU_P [y ty] /Zo_S /setP_P; apply.
move: (complement_p3 Bsr); set A := complement _ _.
move=> [p1 p2].
exists A, B; split => //.
  have AE: (sub A (substrate r)) by apply: sub_setC. 
  move: (iorder_osr or AE) => [or1 sr1].
  split => //; rewrite sr1.
  move=> x xA [y yx]; rewrite iorder_trans //;  ex_middle h.
  have xB: (sub x B). 
    move=> t tx; apply: (setU_i tx); apply: Zo_i h. 
    apply /setP_P; apply: (sub_trans xA AE).
  empty_tac1 y.
move=> [y []];rewrite iorder_sr//.
move =>  /setU_P [t yt aux] h; move: (aux) => /Zo_P [] /setP_P tr; case.
exists y; split; rewrite iorder_sr//  =>  x xt; apply /iorder_gle0P => //. 
exact: (iorder_gle1 (h _ (setU_i xt aux))).
Qed.


Lemma Exercise2_3b n (r := opp_order Nat_order)
  (A := Nint n) (B:= Nat -s A) :
   natp n -> (order r /\ ex23_prop r A B).
Proof.
move=> nN.
move: Nat_order_wor => [[o1 _] s1].
move: (opp_osr o1)=> [or]; rewrite s1 => sr.
have sAC: sub A (substrate r) by rewrite sr; apply: Nint_S1. 
move: (iorder_osr or sAC) => [or1 sr1].
move: (complement_p4 sAC) => [p1 p2].
split => //; split => //.
- by rewrite /B - sr.
- by rewrite /B - sr.
- split => //; rewrite sr1.
  move=> x xA nex; rewrite iorder_trans//.
  rewrite sr in sAC; move: (@sub_trans _ _ _ xA sAC) => sxB.
  have p3: (exists n, upper_bound Nat_order x n).
     have aux: upper_bound Nat_order A n.
       split; [ue | move=> y; rewrite /A]; move /(NintP nN).
       move=> [yn _] ; apply /Nat_order_leP;split => //. 
       by apply: (NS_le_nat yn nN).
     by move: (sub_upper_bound aux xA) => p3; exists n.
   move: (Nat_greatest sxB nex p3) => [y yg]; exists y.
   have s2: sub x (substrate Nat_order) by ue.
   have s3: sub x (substrate r) by ue.
   move: yg; rewrite /greatest /least ! iorder_sr//.
   move=> [yx h]; split => // z zx; move: (h _ zx).
   by move /(iorder_gle0P _ zx yx)  /opp_gleP => ha; apply /iorder_gleP.
- have bsr: sub B (substrate r) by rewrite sr; apply: sub_setC.
case => y [];rewrite iorder_sr//;move=> yb etc.
move: (yb) => /setC_P [yB]  /(NintP nN) nyn.
move: (cltS yB) => [le2 ne1].
have ysB: inc (csucc y) B.
  apply /setC_P;split; first by apply:NS_succ.
  move/(NintP nN) =>le1; case: nyn;  exact: cle_ltT le2 le1.
move: (iorder_gle1 (etc _ ysB)) => /opp_gleP /Nat_order_leP [_ _ le3].
by case: ne1; apply: cleA.
Qed.

Lemma Exercise2_3c 
  (r := diagonal C3) (A1:= C0) (A2:= C1):
  [/\ order r,
     (ex23_prop r A1 ((substrate r) -s A1)) &
     (ex23_prop r A2 ((substrate r) -s A2)) ].
Proof.
move: (diagonal_osr C3)  => []; rewrite -/r => or sr; rewrite sr.
have pa: forall A, sub A (substrate r) ->
   (order_on (induced_order r A)  A).
  by move => A Ai; apply: iorder_osr.
have tws: inc C2 (substrate r) by rewrite sr; apply /set3_P; in_TP4.
have os: inc C1 (substrate r) by rewrite sr; apply /set3_P; in_TP4.
have nc:  gle r C1 C2 -> False.
  move /diagonal_pi_P => [_ bad];  by case: card_12.
split; first by exact.
  have s1: sub A1 (substrate r) by rewrite /A1; fprops.
  move: (complement_p4 s1) => [ta tb].
  move: (pa _ s1) => [tc td]; rewrite - sr; split => //.
    rewrite {2} /A1 in td. 
    rewrite (empty_substrate_zero  td); exact (proj1 set0_wor).
  have ->: (substrate r -s A1) = substrate r.
    set_extens t; first by move => /setC_P [].
    move => ts; apply /setC_P;split => //; case; case.
  rewrite (iorder_substrate or); move => [y [ysr yl]].
  case: (equal_or_not y C1) => y1.
    by move: (yl _ tws); rewrite y1. 
  by move: (yl _ os) =>  /diagonal_pi_P [_ bad].
have s1: sub A2 (substrate r). 
   rewrite sr;move => t /set1_P ->; apply /set3_P; in_TP4.
move: (complement_p4 s1) => [ta tb].
move: (pa _ s1) => [tc td]; rewrite - sr; split => //.
    rewrite {2} /A2 in td; exact: (worder_set1 (conj tc td)).
have ->: (substrate r -s A2) = doubleton C1 C2.
   rewrite sr /A2; set_extens t.
     move /setC_P => []; case /set3_P; first (by move => t1 /set1_P);
     move => ->; fprops.
   case /set2_P => ->; apply /setC_P; split; try (apply /set3_P => //;in_TP4);
      move => /set1_P; fprops.
have sd: sub (doubleton C1 C2) (substrate r).
  by move => t; case /set2_P => ->.
move => [y []]; rewrite (iorder_sr or sd) => [te tf].
case: (equal_or_not y C1) => y1.
  by move: (iorder_gle1 (tf _ (set2_2 C1 C2)));rewrite y1. 
move:  (iorder_gle1 (tf _ (set2_1 C1 C2))).
by move /diagonal_pi_P => [_ ].
Qed.


(** ---- Exercise 2.4: we say that [F] is partially well-ordered if every totally
    ordered subset is well-ordered. In any ordered set, there is a cofinal
    partially well-ordered set  *)

Lemma Exercise2_4 r 
   (pworder :=  fun F => forall X,
    sub X F -> total_order (induced_order r X) -> worder (induced_order r X)):
  order r ->  exists2 F, pworder F & cofinal r F.
Proof. 
move=> or.
set (FF:= Zo (\Po (substrate r)) pworder).
pose f x y := forall a b, inc a x ->
    inc b (y -s x) -> ~ gle r b a.
set (r' := graph_on (fun x y => sub x y /\ f x y) FF).
have r'P: forall x y, gle r' x y <-> [/\ inc x FF, inc y FF, sub x y & f x y].
  move=> x y; split; first by move /Zo_P => [] /setXp_P[xf yf][];aw. 
  move => [pa pb pc pd]; apply /Zo_P;split => //; aw; last by split.
  by apply /setXp_P.
have HpP: forall F, sub F (substrate r) ->  (pworder F <->
    (forall X, sub X F -> nonempty X -> total_order (induced_order r X) 
      -> has_least (induced_order r X))). 
  move => G Fsr;split.
    move=> pwog X XG neX toX; move: (pwog _ XG toX)=> [_].   
    move: (sub_trans XG Fsr) => Xsr.
    rewrite iorder_sr // => wor.
    move: (wor _ (@sub_refl X) neX); rewrite iorder_trans //.
  move=> h X XG torX; move: (torX) =>[orX _].
  move: (sub_trans XG Fsr) => Xsr.
  split; fprops; rewrite iorder_sr //; move=> x xX neX.
  have aux := (iorder_trans r xX).
  rewrite aux; apply: h => //; first by apply: sub_trans XG.
  rewrite - aux; apply: total_order_sub => //; rewrite iorder_sr//.
have Hf: forall x F, inc x (substrate r) -> inc F FF -> inc (F +s1 x) FF.
  move=> x F xsr =>/Zo_P [] /setP_P Fsr pwf.
  have stF: (sub (F +s1 x) (substrate r)).
    move=> t /setU1_P; case; [apply: Fsr | by move => ->]. 
  apply: Zo_i; first by apply /setP_P.
  apply/(HpP _ stF) => X Xt neX toX.
  move: pwf => /(HpP _ Fsr) pwf.
  case: (inc_or_not x X) => tX; last first.
    apply: pwf =>// w wX; move: (Xt _ wX); case /setU1_P => // wx; case: tX; ue.
  move: (sub_trans Xt stF) => Xsr.
  case: (equal_or_not X (singleton x)) => eq.
    exists x; split;rewrite iorder_sr //; move=> t;rewrite eq => /set1_P ->.
    by apply /iorder_gle0P;fprops;order_tac; apply: Xsr.
  move:(@subsetI2r X F)(@subsetI2l X F); set (Y := X \cap F) => sYF sYX.
  move: (sub_trans sYF Fsr) => Ysr.
  case: (emptyset_dichot Y) => Ye. 
     case: eq; set_extens t; last by move /set1_P ->.
     move => tx; move: (Xt _ tx);case /setU1_P; last by move => ->; fprops.
     by move => tf;  empty_tac1 t; apply /setI2_P.
  have tos: (total_order (induced_order r Y)).
    have ->: (induced_order r Y) = (induced_order (induced_order r X) Y).
      by rewrite iorder_trans.
    by apply: total_order_sub => //; rewrite iorder_sr.
  move: (pwf _ sYF Ye tos) => [y []]; rewrite iorder_sr // => yY yl.
  move: (total_order_lattice toX) => lX.
  move: (sYX _ yY) => yX.
  have xsX: inc x (substrate  (induced_order r X)) by  rewrite iorder_sr.
  have ysX: inc y (substrate  (induced_order r X)) by  rewrite iorder_sr.
  move: (lattice_inf_pr lX xsX ysX).
  set z := (inf (induced_order r X) x y).
  move=> [p1 p2 p3]; exists z;red; rewrite iorder_sr//.
  move: (iorder_gle3 p1)(iorder_gle1 p1) (iorder_gle1 p2) => [zX _] zx zy.
  split => // w wx; apply /iorder_gle0P => //. 
  move: (Xt _ wx); case /setU1_P => ezx; last by ue.
  have wY: inc w Y by apply: setI2_i.
  by move:(yl _ wY) => wy; move:  (iorder_gle1 wy) => p4; order_tac.
have or' :(order r').
  apply: order_from_rel;split => //. 
      move=> y x z [xy fxy] [yz fyz]; split => //;first by apply: sub_trans yz.
      move=> a b ax /setC_P [bz nbx].
      case: (inc_or_not b y) => iby; first by  apply: fxy =>//; apply /setC_P.
      apply: fyz =>//; [by  apply: xy | apply /setC_P; split => // ].
    by move=> x y  [xy _] [yx _ ]; apply: extensionality.
   by move=> x y _; split => //; split => // a b ax /setC_P; case.
have sr': substrate r' = FF.
  by apply: graph_on_sr=> x xp; split => //; move=> a b ax => /setC_P [].
have isr': inductive r'. 
  move=> X Xsr []; rewrite iorder_sr// => orX' tor'.
  have tor'': forall x y, inc x X -> inc y X ->
    ((sub x y /\ f x y) \/ (sub y x /\ f y x)).
    move=> x y xX yX.
    case: (tor' _ _ xX yX) =>h; move: (iorder_gle1 h) =>  /r'P.
      move=> [_ _ xy fxy]; left; split => //.
    move=> [_ _ xy fxy]; right; split => //.
  have su: sub (union X) (substrate r).  
    move=> t /setU_P [y ty yX]; move: (Xsr _ yX); rewrite sr' => /Zo_P [].
    by move=> /setP_P ysr _; apply: ysr.
  have uxf: (inc (union X) FF).
    apply: Zo_i => //; first by  apply /setP_P. 
    move => t tu tort;  move: (sub_trans tu su) => tsr.
    move: (iorder_osr or tsr) => [or1 sr1].
    split => //; rewrite sr1 => x xt [u ux]; rewrite iorder_trans //.
    move: (tu _ (xt _ ux)) => /setU_P [i ui iX].
    set (K:=x \cap i). 
    move: (Xsr _ iX); rewrite sr' => /Zo_P  [isr pwoi].
    have K1: (sub K i) by apply: subsetI2r.
    move: (sub_trans xt tsr) => xsr.
    have K2: (sub K t) by apply: sub_trans xt; apply: subsetI2l. 
    move: (sub_trans K2 tsr) => K3.
    have to3:(total_order (induced_order r K)). 
      have ->: (induced_order r K) = (induced_order (induced_order r t) K).
        by rewrite iorder_trans.
      apply: total_order_sub => //; rewrite iorder_sr//.
    have neK: nonempty K by exists u; apply /setI2_P.
    move:isr pwoi => /setP_P isr / (HpP _ isr)  pwoi.
    move: (pwoi _ K1 neK to3).
    move=> [y []]; rewrite iorder_sr// => yK ylK.
    have yx: inc y x by apply: (setI2_1 yK).
    exists y; split; rewrite iorder_sr//.
    move=> v vx; move: (tu _ (xt _ vx)) => /setU_P [w vw wX].
    apply /iorder_gle0P => //.
    case: (inc_or_not v i) => vi.
      have wK: (inc v K) by apply: setI2_i.
      move: (ylK _ wK) => ge1; apply: (iorder_gle1 ge1).
    case: (tor'' _ _ wX iX); first by move=> [wi _]; case: vi; apply: wi. 
    move=> [i3 fiw].
    have vc: inc v (w -s i) by fprops.
    move: (fiw _ _ (K1 _ yK) vc) => r1.
    move: (xt _ yx) (xt _  vx) => yt vt.
    move: tort => [_ ]; rewrite iorder_sr// => tor1.
    case: (tor1 _ _ yt vt) => h; move: (iorder_gle1 h) => //.
  exists (union X); split; first by ue. 
  move=> y yX; apply /r'P; split => //.
      by rewrite - sr'; apply: Xsr.
    by apply: setU_s1.
  move=> a b ay => /setC_P [bu iby]; move: bu => /setU_P [z bz zX].
  case: (tor'' _ _ zX yX); first by move=> [yz _]; case: iby; apply: yz.
  move=> [yz fyz]; apply: fyz => //; apply /setC_P;split => //.
move: (Zorn_lemma or' isr') => [a []]; rewrite sr' => aFF h.
move: (aFF) => /Zo_P [] /setP_P asr pwoan; exists a => //.
split => // x xsr.
case: (inc_or_not x a)=> xa; first by ex_tac;order_tac.
ex_middle aux;case: xa.
suff rat: (gle r' a (a +s1 x)) by rewrite -(h _ rat); fprops.
have pa: sub a (a +s1 x) by fprops.
apply /r'P; split => //; first by apply: Hf => //.
move => t s ta /setC_P [] /setU1_P; case => //.
by move => -> _ ha; case: aux; exists t.
Qed.
 
(** ---- Exercise 2.5: in an inductive set, there is a greatest free subset*)
Lemma Exercise2_5 r: order r -> inductive r ->
  has_greatest (free_subset_order r).
Proof. 
move=> or isr;set (A:= Zo (substrate r) (maximal r)).
have fs: (free_subset r A). 
  by move => x y => /Zo_hi [_ xm] _ xy; rewrite (xm _ xy). 
have Af:(inc A (free_subsets r)) 
  by apply: Zo_i => //; apply /setP_P; apply: Zo_S.
move: (fs_order_osr or) => [fso fsr].
exists A; split; first by ue. 
rewrite fsr => x xs; apply /fs_order_gleP; split => //.
move=> y yx.
move:xs =>/Zo_P [] /setP_P xsr _.
move: (inductive_max_greater or isr (xsr _ yx)) => [m [mm ym]].
exists m => //; apply: Zo_i => //; order_tac.
Qed.

(** ---- Exercise 2.6 *)

(** We start with two auxiliary lemmas. In a well-ordered set, 
if [a] has a strict upper bound, there is a successor [b]; 
this means that [x<=a] and [x<b] are equivalent. 
The emptyset is an initial segment (with end-point the least element  *)

Lemma worder_has_empty_seg r: worder r ->
  nonempty (substrate r) -> exists2 x,
    inc x (substrate r) & segment r x = emptyset.
Proof. 
move=> wor nes.  
move:(worder_least wor nes) =>[x [xsr xle]]; ex_tac.
apply /set0_P => y /segmentP ys.
have ysr: inc y (substrate r) by order_tac.
move: (xle _ ysr) (proj1 wor) => le1 or; order_tac.
Qed.

Lemma Exercise2_6g r a (m := Zo (substrate r) (fun z => glt r a z)) :
  worder r -> inc a (substrate r) ->
  nonempty m -> exists2 b, 
      inc b (substrate r) & (segmentc r a = segment r b).
Proof.
move=> wor asr nem.
move: (worder_total wor) => tor.
have sms: (sub m (substrate r)) by apply: Zo_S. 
move: wor => [or wor1];  move: (wor1 _ sms nem) => [y[]]; rewrite iorder_sr // => ym yl.
move: (sms _ ym) => ysr; ex_tac.
move: (ym)=> /Zo_hi ya.
set_extens t; first by  move /segmentcP => ta; apply /segmentP; order_tac.
move /segmentP => ta; apply /segmentcP.
have tsr: inc t (substrate r) by order_tac.
case: (total_order_pr2 tor asr tsr) => // lat.
have tm: inc t m by apply: Zo_i.
move: (iorder_gle1 (yl _ tm)) => h'; order_tac.
Qed.


(** We assume that [f:E->E] is defined on an ordered set and [f(x) >=x].
Let [bigS] be the set of all [M] stable by [f], such that any non-empty subset
[N] of [M] that has a least upper bound [x] is such that [x] belongs to [M].
The chain of [a] is the intersection of all elements of [M] that contain [a]
*)
Section Exercise2_6.
Variables r f : Set.

Definition bigS :=
  Zo (\Po (substrate r))
  (fun M => (forall x, inc x M -> inc (Vf f x) M) /\
    (forall N x, sub N M -> nonempty N -> least_upper_bound r N x -> inc x M)).

Definition chainx a := intersection (Zo bigS (inc a)).

Hypothesis or: order r.
Hypothesis ff: function f.
Hypothesis sf: substrate r = source f.
Hypothesis tf: substrate r = target f.
Hypothesis fxx: forall x, inc x (substrate r) -> gle r x (Vf f x).

(** Bourbaki says "Deduce from (a)  that if [E] is inductive, then [f] 
has a fix-point". But this is trivial *)

Lemma Exercise2_6i: inductive r ->
  exists2 a, inc a (source f) & Vf f a = a.
Proof.
move => ir; move: (Zorn_lemma or ir) => [a [asr am]].
rewrite - sf;exists a;fprops.
Qed.

(** We show: if the chain  of [a] has a least upper bound, 
it is in the chain and is a fix-point of [f] *)
Lemma Exercise2_6a: inc (substrate r) bigS. 
Proof.
apply: Zo_i; aw; first by apply /setP_P; fprops.
split.
   move => x xsr; move: (fxx xsr) => h; order_tac.
by move=> N x Nsr [y yN] /(lubP or Nsr) [[p1 _] _].
Qed.

Lemma Exercise2_6b a:
  inc a (source f) -> nonempty (Zo bigS (inc a)).
Proof. 
move=> asf;exists (substrate r); apply: Zo_i;[ apply: Exercise2_6a| ue].
Qed.

Lemma Exercise2_6c a: inc a (source f) -> inc a (chainx a).
Proof. 
move=> asf; apply: setI_i; first by apply: Exercise2_6b =>//.
by move=> y /Zo_hi.
Qed.

Lemma Exercise2_6d a: 
  inc a (source f) -> inc (chainx  a) bigS.
Proof. 
move => asf. 
move: (Exercise2_6b asf) =>ne; move: (ne) => [u ub].
apply: Zo_i.
  apply /setP_P; move=> t td; move: (setI_hi td ub). 
  by move: ub => /Zo_P [] /Zo_P [] /setP_P usr _ _ tu ; apply: usr.
split.
  move=> x xc; apply: setI_i => //.
  move=> y yb; move: (setI_hi xc yb).
  by move: yb => /Zo_P [] /Zo_P [] /setP_P _ [p _] _ tu; apply: p.
move=> N x Nca neN leN.
apply: setI_i => // y yb; move: (yb) => /Zo_P [yc ay].
move: yc => /Zo_P [_ [_ p]]; apply: (p N x) => //.
move=> t tN ; exact: (setI_hi (Nca _ tN) yb).
Qed.

Lemma Exercise2_6e a b:
  inc a (source f) -> least_upper_bound r  (chainx a) b ->
  (inc b  (chainx a) /\ Vf f b = b).
Proof. 
move=> asf leb.
move: (Exercise2_6c asf) => aca.
move:(Exercise2_6d asf) => /Zo_P [p1 [p2] aux]; move: p1 => /setP_P p1.
have neca: nonempty (chainx a) by exists a.
have ba: inc b (chainx a) by apply: (aux _ _ (@sub_refl (chainx a)) neca leb).
split => //; move: leb => /(lubP or p1) [[_ ub] _ ].
move: (ub _ (p2 _ ba)) (fxx  (p1 _ ba)) => le1 le2; order_tac.
Qed.


(** A chain is well-ordered. Proof.
We consider a set [M0], two subsets [M1] and [M2];
two quantities [p1], [p2]; we deduce [M] and [p]. For [x] in [M]; [p(x)] is not 
in [x]. By [Zermelo_aux] there exists a well-ordered set [q], 
such that [p(Sx)=x]  (where [Sx] is the segment with end point [x] in [q]) 
and [q] is not in [M].
As a consequence, the chain of [a] is a subset of [q]; since the ordering of [q] coincides with that of [E], it follows that the chain is well-ordered.
 *)
Lemma Exercise2_6h a:
  inc a (source f) -> worder (induced_order r  (chainx a)).
Proof.
move=> asf.
set (E:= substrate r).
set(M0 :=  Zo (\Po E) (fun z => inc a z /\ exists b, least_upper_bound r z b)).
have aE: inc a E by rewrite /E sf.
have p0: forall x, inc x M0 -> sub x (substrate r).
  by move=> x => /Zo_P [] /setP_P.
have p1: (forall z, inc z M0 -> least_upper_bound r z (supremum r z)).
   move=> z /Zo_P [zp [az [b leb]]]. 
   by apply: supremum_pr1 => //; exists b.
have p2: forall x, inc x M0 -> (inc  (supremum r x) (substrate r)
    /\ inc (Vf f (supremum r x)) (substrate r)).
  move => x xM0; move: (p0 _ xM0) => xE; move: (p1 _ xM0).
  move => /(lubP or xE) [[sE _] _]; split => //;move: (fxx sE) => aux;order_tac.
pose sif x := glt r x (Vf f x).
set (M1 := Zo M0 (fun z => ~ (inc (supremum r z) z))).
set (M2 := Zo M0 (fun z => sif (supremum r z))).
set(M:= (M1 \cup M2) +s1 emptyset). 
pose p x := Yo (x= emptyset) a 
    (Yo (inc x M1)  (supremum r x) (Vf f (supremum r x))).
have Ha:sub (M1 \cup M2) M0 by apply: setU2_12S; apply: Zo_S.
have p3: (forall x, inc x M -> (inc (p x) (E -s  x))).
  move=> x xM;  rewrite /p; apply/setC_P.
  Ytac xe; first by split => // xie; empty_tac1 a.
  Ytac xM1. 
    by move: xM1 => /Zo_P [/p2  [xM0 _] ni].
  move: xM; case /setU1_P;[ case /setU2_P => // H | done].
  move /Zo_P:H => [xM0 lt1]; move: (p2 _ xM0) => [p3 p4]; split => //.
  move=> h; move: (p0 _ xM0) => xE;move: (p1 _ xM0); move /(lubP or xE).
  rewrite /sif in lt1;  move=> [ [_ ub ] _]; move: (ub _ h) => p5; order_tac.
have p4: sub M (\Po E).
  move=> t th; apply /setP_P.
  case /setU1_P: th => h; [ apply: (p0 _ (Ha _ h)) | rewrite h; fprops]. 
move: (Zermelo_aux p4 p3).
rewrite /Zermelo_ax; set r' := union _; set (q:= substrate r').
move=> [[wor' qE xqp] nqM].
have aq: (inc a q).
  case: (emptyset_dichot q) => qe; first by case: nqM; rewrite /M qe; fprops.
  move: (worder_has_empty_seg wor' qe) => [x xsr' se]. 
  by move: (proj2 (xqp _ xsr')); rewrite se /p Y_true // => ->.
have compat:  (forall u v, gle r' u v -> gle r u v). 
  move=> u v uv.
  have vq: (inc v q) by rewrite /q; order_tac.  
  have bE: inc v E by apply: qE.
  case: (equal_or_not u v) => auv; first by rewrite auv; order_tac.
  have suv:(inc u (segment r' v)) by apply: segment_inc. 
  have nes: segment r' v <>  emptyset by apply/nonemptyP; ex_tac.
  move: (proj1 (xqp _ vq)); case /setU1_P => // h.
  move:  (p1 _ (Ha _ h)); set c := supremum r _.
  have ss: sub (segment r' v) (substrate r).
    apply: (@sub_trans q) => //; apply: sub_segment.
  move=> /(lubP or ss) [[_ p5] _]; move: (p5 _ suv) => le1.
  have csr: (inc c (substrate r)) by order_tac.
  move: (proj2(xqp _ vq)); rewrite /p ; Ytac0; Ytac c1; first by move => <-.
  move: h; case /setU2_P; first by move => H.
  move /Zo_P => [_ [le2 _]] eq1; rewrite eq1 in le2; order_tac.
move: (wor') => [or' _].
have p5: forall y, least_upper_bound r q y -> (inc y q /\ Vf f y = y).
  move=> y ley.
  have qM0: inc q M0 by apply: Zo_i; [ apply /setP_P | split => //; exists y].
  case: (inc_or_not y q) => yq.
    case: (equal_or_not y (Vf f y)) => w //. 
    move: nqM => /setU1_P; case; left; apply /setU2_P; right.
    apply /Zo_i => //; red; rewrite -  (supremum_pr2 or ley); split =>//.
    by apply: fxx; apply: qE.
  move: nqM => /setU1_P; case; left; apply /setU2_P; left.
  by apply /Zo_i => //; rewrite -  (supremum_pr2 or ley).
have stable: (forall x, inc x q -> inc (Vf f x) q). 
  move=> x xq; set (m:=Zo q (fun z => glt r' x z)). 
  case: (emptyset_dichot m) => em.
    have gx: (greatest r' x). 
      split => // y ysr; case: (total_order_pr2 (worder_total wor') xq ysr)=>//.
      move=> bad; empty_tac1 y;apply: Zo_i => //; order_tac.
    have gx':(greatest (induced_order r q) x). 
      split;rewrite iorder_sr//; move=> y yq; apply /iorder_gle0P => //; apply: compat.
      by move: gx => [_]; apply.
    move: (greatest_is_sup or qE gx') => sq.
    by move: (p5 _ sq) => [r1 r2]; rewrite r2.
  move: (Exercise2_6g wor' xq em) => [z zsr].
  case: (xqp _ zsr); set s := segment r' z => p5' p6 ss.
  have xs: inc x s by rewrite - ss; apply:  inc_bound_segmentc.
  have ssr': sub s (substrate r') by apply: sub_segment. 
  have ssr: sub s (substrate r) by apply: (@sub_trans  q).  
  have aux y: inc y s -> gle r' y x by rewrite - ss => /segmentcP.
  have gx: (greatest (induced_order r' s) x). 
    by split;rewrite iorder_sr// => y ysr; apply /(iorder_gle0P _ ysr xs); apply: aux.
  have gx':(greatest (induced_order r s) x). 
   by split; rewrite iorder_sr // => y yq; apply /iorder_gle0P => //; apply: compat; apply: aux.
  move: (greatest_is_sup or ssr gx') => sq.
  move:(supremum_pr2 or sq) => xsq.
  move: p5' p6; rewrite /p; Ytac se; first by empty_tac1 x. 
  case /setU1_P => //;  Ytac nsm1.
     move: nsm1 => /Zo_hi;rewrite -xsq //. 
  case /setU2_P; [ done |  by rewrite -xsq;move=> _ -> ].
move: (worder_total wor') => [_ tor'].
have toq: forall a b, inc a q -> inc b q -> gle r a b \/ glt r b a.
  move => u v uq vq.
  case:(equal_or_not u v) => uv; first by rewrite uv; left;order_tac; apply: qE.
  rewrite /glt; case: (tor' _ _ uq vq) => h; move: (compat _ _ h);fprops. 
have compat': forall u v, inc u q -> inc v q -> gle r u v -> gle r' u v.
  move=> u v uq vq uv.
  case: (tor' _ _ uq vq) => h; move: (compat _ _ h) => //.
  by move=> vu; move: h; rewrite (order_antisymmetry or uv vu).
have aux: (forall N y, sub N q -> nonempty N -> least_upper_bound r N y ->
     inc y q).
  move => N y Nq neN infN.
  move: (sub_trans Nq qE) => NE.
  move: infN => /(lubP or NE) [[ys uny] luny].
  set (bN:=Zo q (fun z=> gle r y z)).
  case: (emptyset_dichot bN) => bne.
    suff le1: (least_upper_bound r q y) by exact: (proj1 (p5 _ le1)).
    apply /(lubP or qE); split; last first.
      by move=> z [zr uz]; apply: luny; split => // t tn; apply: uz; apply: Nq.     split =>// z zq; case: (p_or_not_p (exists t, inc t N /\ glt r z t)).
      move => [t [/uny tN [zt _]]]; order_tac.
    move =>bad; empty_tac1 z; apply: Zo_i => //. 
    apply: luny; split; first by apply: qE.
    move=> t tN; case: (toq _ _ (Nq _  tN) zq) => // zt; case: bad; ex_tac.
  have bNq:  (sub bN q) by apply: Zo_S. 
  move: (proj2 wor' _ bNq bne) => [z []];rewrite iorder_sr// => zbN zlbn.
  move: (zbN) => /Zo_P [zq yz].
  case: (inc_or_not z N) => zN. 
    by move: (uny _ zN) => zy; rewrite (order_antisymmetry or yz zy).
  have zlb1: (forall u, inc u q -> gle r y u -> gle r' z u).
    move=> u uq r1; have ub: (inc u bN) by apply: Zo_i.
    exact: (iorder_gle1 (zlbn _ ub)).
  have Ns: (sub N (segment r' z)). 
    move=> t tN ; apply /segmentP; split; last by dneg tz; ue.
    move: (uny _ tN) => ty; apply: compat' => //;[ by apply: Nq | order_tac].
  have /nonemptyP Nes: (nonempty (segment r' z)).
    by move: neN => [w wN];  exists w; apply: Ns.
  case: (xqp _ zq); case /setU1_P; last by done.  
  rewrite /p;Ytac0; move=> aux; move: (p1 _  (Ha _ aux)).
  have aux1: sub (segment r' z) (substrate r)
      by apply: (@sub_trans q) => //; apply: sub_segment.
  set s := (supremum r (segment r' z)); move /(lubP or  aux1)=> [[p6 p7] p8].
  have ys1: (gle r y s) by apply: luny; split => // t tn; apply: p7; apply: Ns.
  have sz: (gle r s z).
    by apply: p8; split;fprops; move => t /segmentP [le _]; apply: compat.
  have sns: ~ (inc s (segment r' z)) .
     move / segmentP => [r1 r2].
     have sq: (inc s q) by  rewrite / q; order_tac.
     move: (zlb1 _ sq ys1) => aux2; case: r2;  order_tac.
  have  p9: (inc (segment r' z) M1) by apply: Zo_i => //; apply: Ha.
  Ytac0; move=> sz1.
  suff:(gle r s y) by move=> sy; rewrite - (order_antisymmetry or sy ys1) sz1.
  apply: p8; split => // t /segmentP tz.
  have tq: (inc t q) by rewrite /q; order_tac.
  case: (p_or_not_p (exists2 u, inc u N & glt r t u)). 
    move=> [u uN [tu _]]; move: (uny _ uN) => uy; order_tac.
  move=> bad.
  have good: (forall u, inc u N -> gle r u t).  
    move=> u uN; case: (toq _ _ (Nq _ uN) tq) => // tu; case: bad; ex_tac.  
  have ubt: (upper_bound r N t) by split =>//; apply: qE. 
  move:(zlb1 _ tq (luny _ ubt)) => p10; order_tac.
have sc: (sub (chainx a) q).
  move => t tc; apply: (setI_hi (y:=q) tc);apply: Zo_i => //.
  apply: Zo_i; [ by apply /setP_P | split => //].
move: (sub_trans sc qE) => sE.
move: (iorder_osr or sE) => [or1 sr1]. 
split => //; rewrite sr1 => x xc nex; move: (sub_trans xc sc) => xcq.
move: (sub_trans xcq qE) => xE.
move: wor' => [_ wor''];move: (wor'' _ xcq nex) => [z []]; rewrite iorder_sr//.
move=> zx zl; exists z; rewrite iorder_trans //;split => //;rewrite iorder_sr//.
move=> b bx;apply /iorder_gle0P => //. 
apply:(compat _ _ (iorder_gle1 (zl _ bx))).
Qed.

End Exercise2_6.


(** ---- Exercise 2.7.  Properties of closures.
If [E] is ordered, we consider the closures; let [I(f)] be the set of 
fixed-points of [f]. We have [f <= g] iff  [sub (I g) (I f)]. 
There is a least function, the identity. *)
Section Exercise27.
Variable r: Set.
Hypothesis or: order r.
Let E := substrate r.

Definition closures  :=
  Zo (functions E E) (fun z=> closure z r).

Definition closure_ordering  :=
    induced_order (order_function E E r) (closures).

Lemma Exercise2_7aP f g: 
  gle (closure_ordering) f g <->
  [/\ inc f (closures), inc g (closures) &
    forall i, inc i (substrate r) -> gle r (Vf f i) (Vf g i)].
Proof. 
move: (order_function_osr E or (refl_equal E)) => [or' sr'].
have p1: (sub (closures) (substrate (order_function E E r))).
  rewrite sr'; apply: Zo_S. 
rewrite /closure_ordering; split => h.
  move: (iorder_gle1 h)(iorder_gle3 h) => fg [fs gs]; split => //.
  by move: fg => /order_functionP [_ _ ok].  
move: h => [h1 h2 h3];apply/iorder_gle0P => //.
by move: h1 h2 => /Zo_P [h1 h2] /Zo_P [h3' h4]; apply /order_functionP.
Qed.

Lemma Exercise2_7b: 
  order_on closure_ordering closures.
Proof. 
rewrite /closure_ordering.
move: (order_function_osr E or (refl_equal E)) => [p1 p2].
apply:iorder_osr => //; rewrite p2; apply: Zo_S.
Qed.

Lemma Exercise2_7c: 
  least (closure_ordering) (identity (substrate r)).
Proof. 
have ifsr: inc (identity E) closures.
  apply: Zo_i ;first by apply /functionsP;red;aw;split;fprops.
  split => //.
  - split => //; first by apply: identity_prop.
    move=> x y xy; rewrite ! idV//; rewrite /E;order_tac.
  - by move=> x xsr; rewrite idV//; order_tac.
  - move => x xsr; rewrite ! idV//.


move: Exercise2_7b => [p1 p2].
red; rewrite p2;split => // x xs; apply /Exercise2_7aP; split => //.
move => i isr; rewrite idV//.
by move: xs => /Zo_hi [_ p4 _];apply: p4.
Qed.

Lemma Exercise2_7dP f g:
  inc f closures -> inc g closures ->
  (gle (closure_ordering) f g <-> 
     sub (fixpoints g) (fixpoints f)).
Proof. 
move=> fs gs; move: (fs) => /Zo_P [/functionsP [ff sf tf] [q1 q2 q3]].
move: (gs) => /Zo_P [/functionsP [fg sg tg] [q4 q5 q6]]. 
split.
  move /Exercise2_7aP=> [_ _ h] t /Zo_P [tsg wg]; apply /Zo_P;split. 
    by rewrite sf - sg.
  rewrite sg in tsg;  move: (q2 _ tsg) => p11.
  move: (h _ tsg) ; rewrite wg=> p7; order_tac.
move=> h; apply /Exercise2_7aP;split => // i isr.
move: (q5 _ isr) (q6 _ isr) => le1 le2.
have : inc (Vf g i) (fixpoints f). 
   apply: h; apply: Zo_i=> //; rewrite sg - tg; Wtac; ue.
by move /Zo_P=> [_ <-]; move: q1 => [_ _ _ incf]; apply: incf.
Qed.

(** If [f_i] is a family of closures, if [inf_i (f_i x)] exists for all [x],
  then this is the infimum of the family. Thus: (a) if any pair has an infimum 
  in [E], the same holds for closures; (b) if [E] is a complete lattice so is
  the set of closures 
 *)

Lemma Exercise2_7e f g:
  (forall x y, inc x E -> inc y E ->
    has_infimum r (doubleton x y)) ->
  inc f (closures) -> inc g (closures)  ->
  has_infimum (closure_ordering) (doubleton f g).
Proof.
move=> hid fc gc.
have Ht:sub (doubleton f g) (closures). 
  by move=> t /set2_P; case => ->.
move: (fc) (gc) =>  /Zo_P[p1 [q1 q2 q3]] /Zo_P [p3  [q4 q5 q6]].
have Ha: forall x, inc x E -> inc (Vf f x) E. 
  move=> x xE; move: (q2 _ xE) => aux; rewrite /E; order_tac.
have Hb: forall x, inc x E -> inc (Vf g x) E.
  move=> x xE; move: (q5 _ xE) => aux; rewrite /E; order_tac.
set (hh:= fun z=> inf r (Vf f z) (Vf g z)).
have hp: forall x, inc x E -> 
    [/\ gle r (hh x) (Vf f x),  gle r (hh x) (Vf g x) &
      forall z, gle r z (Vf f x) ->  gle r z (Vf g x) -> gle r z (hh x)].
  move => x xE; move: (Ha _ xE) (Hb _ xE) => fE gE.
  move: (inf_pr or fE gE (hid _ _ fE gE)) => [qa qb qc]; split => //.
have h1: forall x, inc x E -> gle r x (hh x). 
  move=> x xE; apply:(proj33 (hp _ xE)); [ by apply: q2 | by apply: q5 ].
have ep: forall x y,  gle r x y -> (inc x E /\ inc y E).
   move=> x y xy; rewrite /E; split; order_tac.
have h2: forall x y, gle r x y -> gle r (hh x) (hh y).
  move=> x y xy; move: (ep _ _ xy) => [xE yE].
  move: q1 => [_ _ _ incf]; move: (incf _ _ xy) => r4.
  move: q4 => [_ _ _ incg]; move: (incg _ _ xy) => r5.
  move: (hp _ xE)=> [r1 r2 _]; apply: (proj33 (hp _ yE)); order_tac.
set (h:= Lf hh E E).  
have ta: lf_axiom hh E E. 
   by move => w xe; move: (h1 _ xe) => h3; rewrite /E;order_tac.
have fh: function h  by apply: lf_function.
have ch: closure h r.
  split => //. 
      split => //; first by rewrite /h; saw.
      rewrite /h; move=> x y xy; move: (ep _ _ xy) => [xE yE].
      by rewrite !LfV//;  apply: h2.
    by move=> x xE; rewrite /h LfV//; apply: h1.
  move=> x xE; move: (ta _ xE) => hE; rewrite /h (LfV  ta xE) (LfV  ta hE). 
  move: (hp _ hE) => [r3 r4 _].
  move: (hp _ xE) => [r5 r6 r9].
  move: q1 => [_ _ _ incf]; move: (incf _ _ r5).
  move: q4 => [_ _ _ incg]; move: (incg _ _ r6).
  rewrite (q6 _ xE) (q3 _ xE) => r7 r8.
  move: (r9 _ (order_transitivity or r3 r8) (order_transitivity or r4 r7)).
  move: (h1 _ hE) => r10 r11; order_tac.
move: (Exercise2_7b) => [oco sco].
have hco: inc h closures 
  by apply: Zo_i => //; apply /functionsP; split => //; rewrite /h;aw.
have hsco: inc h (substrate (closure_ordering)) by  rewrite sco.
have sd: sub (doubleton f g) (substrate closure_ordering) by ue.
exists h.
apply /(glbP oco sd); split.
  by split => //y /set2_P; case => ->; apply /Exercise2_7aP;
    split => // i isr;rewrite /h LfV //; move: (hp _ isr)=>[s1 s2 _].
move=> z [ze zh]. 
move: (zh _ (set2_1 f g)) (zh _ (set2_2 f g)).
move /Exercise2_7aP =>  [zc _ s1] /Exercise2_7aP  [_ _ s2].
apply/Exercise2_7aP;split => //.
move=> i isr; move: (s1 _ isr)(s2 _ isr)(hp _ isr)=> s3 s4 [_ _ s5].
by rewrite /h LfV//; apply: s5.
Qed.

Lemma Exercise2_7f: complete_lattice r ->
  complete_lattice (closure_ordering).
Proof.
move=> [_ cl1];move: (Exercise2_7b) => [oco sco].
apply: Exercise1_11h => //; rewrite sco => X Xc.
have xp1: forall f, inc f X -> closure f r. 
  by move=> f fx; move: (Xc _ fx) => /Zo_P [ _ ].
set (iv := fun x => fun_image X (Vf ^~ x)). 
have ivs: (forall x, inc x (substrate r) -> sub (iv x) (substrate r)).
  move=> x xsr t => /funI_P [z zX ->].
  move: (xp1 _ zX) => [_ s1 _]; move: (s1 _ xsr) => s2; order_tac.
set (hh := fun x => infimum r (iv x)).
have hp1: (forall x, inc x (substrate r) -> (lower_bound r (iv x) (hh x) /\ 
    forall z, lower_bound r (iv x) z -> gle r z (hh x))).
  move=> x xsr; move:(ivs _ xsr)=> isr; move: (cl1 _ isr ) => [_ hi].
  apply:  (infimum_pr or isr hi).
have ta: (lf_axiom hh (substrate r) (substrate r)). 
  by move=> t tsr; move: (hp1 _ tsr) => [[ok _] _].
set (h:= Lf hh (substrate r) (substrate r)).
have fh: (function h) by  apply: lf_function.
have p1: (forall x f, inc x (substrate r) -> inc f X ->
    gle r (Vf h x) (Vf f x)). 
  move=> x f xsr fX;move: (hp1 _ xsr) => [[_ xx] _]; rewrite /h LfV//. 
  apply: xx; apply /funI_P; ex_tac.
have p2: forall x y, inc x (substrate r) ->  inc y (substrate r) ->
    (forall f, inc f X -> gle r y  (Vf f x)) -> gle r y (Vf h x).
  move=> x y xsr ysr h1; rewrite /h LfV//;  move: (hp1 _ xsr) => [_]; apply.
  by split => //; move=> t /funI_P [z zX ->]; apply: h1.
have p3: (increasing_fun h r r).
  rewrite /h;split => //; first saw; move=> x y xy.
  have xE: (inc x (substrate r)) by order_tac.
  have yE: (inc y (substrate r)) by order_tac.
  rewrite !LfV//; move: (hp1 _ xE)(hp1 _ yE) => [[h1 h2] _] [_]; apply.
  split => //; move=>  z /funI_P [f fX] ->.
  move: (xp1 _ fX) => [[_ _ _ incf] _ _ ].
  move: (incf _ _ xy) => h3.
  have h4: (inc  (Vf f x) (iv x)) by apply /funI_P; ex_tac.
  move: (h2 _ h4) => h5;order_tac.
have p4: (forall x, inc x (substrate r) -> gle r x (Vf h x)).
  move=> x xsr; apply: (p2 _ _ xsr xsr). 
  by move=> f fX; move: (xp1 _ fX) => [_ h2 _]; apply: h2. 
have p5:(forall x, inc x (substrate r) -> Vf h (Vf h x) = Vf h x). 
  move=> x xE; move: (ta _ xE) => ws.
  have W1: Vf h x = hh x by rewrite /h LfV.
  symmetry; apply: (order_antisymmetry or).
    by move: (p4 _ ws); rewrite -W1.
  move: (hp1 _ xE) => [_]; rewrite W1;apply.
  split; first by rewrite /h LfV//; apply: (ta _ ws). 
  move => y /funI_P [z zX ->].
  move: (p1 _ _ ws zX) => p5.
  move: (xp1 _ zX) => [[_ _ _ incf] _ aa].
  move: (incf _ _  (p1 _ _ xE zX)); rewrite (aa _ xE) W1=> p6; order_tac.
have ch: (closure h r) by split => //.
have hco: inc h closures 
   by apply: Zo_i => //; apply /functionsP;split => //; rewrite /h;aw.
have hsco: inc h (substrate (closure_ordering)) by  rewrite sco.
have Wsr:sub X (substrate closure_ordering) by ue.
exists h.
apply /(glbP oco Wsr); split.
  split => //; move=> y; aw => yX;apply /Exercise2_7aP.
   move: (Xc _ yX)=> ys;split;fprops.
move=> z [z1 z2]; apply/Exercise2_7aP; split => //; first by ue.
move=> i isr; rewrite /h LfV//;move: (hp1 _ isr) => [_ ]; apply.
move: z1; rewrite sco  => /Zo_P [] /functionsP [fx sz tz] cz.
split => //; first by rewrite -/E; Wtac; ue.
move=> y /funI_P [t tX ->].
by move: (z2 _ tX) =>/Exercise2_7aP [_ _ ]; apply.
Qed.

(** Bourbaki says: Each pair of closures has a supremum if [E] is inductive.
This assertion is false.

We consider two closures [u] and [v], with fix-points
[Iu] and [Iv]; we search a closure [w], with fixed point [Iw], that is 
the least upper bound. Let [T = intersection2 Iu Iv].
Let [f] be the composition of [u] and [v]. Its set of fixed points is [T].
Let [Ixf(x)] the set of all fixed-points of [f] that are [>=x]. 
If [w] is an upper bound, then [w(x)] is a fixed-point of [u] and [v],  
and thus of [f], so is in [Ixf(x)]. *)


Definition Ixf x f :=  Zo E (fun z => gle r x z /\ Vf f z = z).
Definition Jf f := (forall x, inc x E -> exists y, 
        least (induced_order r (Ixf x f)) y).

Lemma Exercise2_7g u v:
  inc u (closures) -> inc v (closures) ->
   Jf (u \co v) ->
   has_supremum (closure_ordering) (doubleton u v).
Proof.
move=> uc vc Jcuv.
have Ht:sub (doubleton u v) (closures). 
  by move=> t /set2_P;case => ->.
move: (uc) (vc); move => /Zo_P [p1 p2] /Zo_P [p3 p4].
move: p2 p4=> [q1 q2 q3] [q4 q5 q6].
have Ha: forall x, inc x E -> inc (Vf u x) E. 
  move=> x xE; move: (q2 _ xE) => aux; rewrite /E; order_tac.
have Hb: forall x, inc x E -> inc (Vf v x) E.
  move=> x xE; move: (q5 _ xE) => aux; rewrite /E; order_tac.
move: p1 p3 =>/functionsP [fu su tu] /functionsP  [fv sv tv].
have cp: u \coP v by split => //;ue. 
set f := u \co v.
have ff: (function f) by rewrite /f; fct_tac.
set (gg := fun x => the_least (induced_order r (Ixf x f))).
have sI: (forall x, inc x E -> sub (Ixf x f) (substrate r)). 
  move=> x xE; apply: Zo_S. 
have sI1: forall x, inc x E -> substrate(induced_order r (Ixf x f)) = (Ixf x f).
  move=> x xE; move: (sI _ xE) => aux; rewrite iorder_sr //.
have lg: forall x, inc x E -> least (induced_order r (Ixf x f)) (gg x).
  move=> x xE; move: (Jcuv _ xE) => ey. 
  apply: the_least_pr => //; apply: (proj1 (iorder_osr or (sI _ xE))).
have gp: forall x, inc x E ->
   [/\ inc (gg x) (substrate r), gle r x (gg x), Vf f (gg x) = gg x &
      (forall y, inc y (Ixf x f) -> gle r (gg x) y)].
  move=> x xE; move: (lg _ xE);rewrite /least; rewrite (sI1 _ xE).
  move => [] /Zo_P [pa [pb pc]] p2; split => //. 
  move=> y yI; move: (p2 _ yI) => h;apply: (iorder_gle1 h).
have ta:(lf_axiom gg E E). 
  by move=> t tE; move: (gp _ tE) => [ok _]. 
have p0P: forall x, inc x E -> ((gg x = x) <-> (Vf f x = x)).
  move=> x xE; move: (gp _ xE) => [p1 p2 p3 p4]. 
  split => h; first by rewrite -h. 
  have xI: inc x (Ixf x f) by apply: Zo_i => //; split => //; order_tac.
   move: (p4 _ xI) => p5; order_tac.
have p1: (forall x, inc x E -> gle r x (gg x)). 
  by move=> x xE; move: (gp _ xE) => [_ ].
have p2: (forall x, inc x E -> gg (gg x) = gg x). 
  by move=> x xE; apply /(p0P _ (ta _ xE)); move: (gp _ xE) => [_ _].
have p3: forall x y, gle r x y -> gle r (gg x) (gg y).
  move=> x y xy.
  have xE:(inc x E) by rewrite /E;order_tac.
  have yE:(inc y E) by rewrite /E;order_tac.
  move: (gp _ yE) => [s1 s2 s3 s4].
  have gyI: (inc (gg y) (Ixf x f)) by apply: Zo_i => //; split => //; order_tac.
  by move: (gp _ xE) => [_ _ _]; apply.
set (g:= Lf gg E E). 
have fg: (function g) by  apply: lf_function.
have cg: (closure g r). 
  split => //; rewrite /g.  
     split => //; first by saw.
      move=> x y xy. 
      have xx: gle r (gg x) (gg y) by apply:p3.
      rewrite !LfV///E; order_tac. 
    by move=> x xE;rewrite LfV//; apply: p1.
  by move=> x xE; rewrite (LfV  ta xE) (LfV  ta (ta _ xE)); apply: p2.
move: (Exercise2_7b) => [oco sco].
have hco: inc g closures 
  by apply: Zo_i => //; apply /functionsP; split => //; rewrite /g;aw.
have hsco: inc g (substrate (closure_ordering)) by  rewrite sco.
have sd: sub (doubleton u v) (substrate closure_ordering) by ue.
have sg: source g = E by rewrite /g;aw.
have sf: source f = E by rewrite /f; aw.
have ig: fixpoints g = fixpoints f.
  set_extens t => /Zo_P []; rewrite ?sf ? sg => [r1 r2];
    apply /Zo_P;split => //; try ue;
     move : r2; rewrite /g LfV//; move /(p0P _ r1) => //.
have sif: fixpoints f = 
    (fixpoints u) \cap (fixpoints v).
  rewrite /fixpoints su sv sf; set_extens t.
    move /Zo_P => [tE wf].
    have tsv: inc t (source v) by ue.
    have Wtsv: inc (Vf v t) (substrate r) by rewrite -/E -tv; fprops.
    move: wf; rewrite /f compfV// => wf.
    move: (f_equal (fun z=> Vf u z) wf); rewrite q3 // wf => f1.
    move: (q2 _ Wtsv)  (q5 _ tE); rewrite wf => le1 le2.
    apply /setI2_P; split => //; apply /Zo_P;split => //;order_tac.
  move /setI2_P => [] /Zo_P [tE Wu] /Zo_P [_ Wv]; apply /Zo_P;split => //.
 by rewrite /f compfV// ?sv // Wv Wu. 
exists g.
apply /(lubP oco sd); split.
  split => //; move=> y ys.
  have aux: inc y closures by rewrite - sco; apply: sd.
  by apply /(Exercise2_7dP aux hco); case /set2_P: ys => ->; 
    rewrite ig sif => t /setI2_P [].
move=> z [ze zh]. 
have zc: inc z closures by ue.
move: (zh _ (set2_1 u v)) (zh _ (set2_2 u v)).
move /(Exercise2_7dP uc zc) => h1  /(Exercise2_7dP vc zc) => h2.
apply (Exercise2_7dP hco zc);rewrite ig sif.
move => t ts; apply: setI2_i;fprops.
Qed.

(**
If [Ixf(x)] has a least element [g(x)], then [g] is a closure, and has the same 
fixed-points as [f], thus is the least upper bound. If the set is inductive, 
then there is a maximal element [>=x] which is thus in [Ixf(x)]. If the set is
well-ordered, then [Ixf(x)] has least element; Thus any pair of closures 
has a supremum  *)

Lemma Exercise2_7h u v: 
  inductive r -> worder r ->
  inc u (closures) -> inc v (closures) ->
   has_supremum (closure_ordering) (doubleton u v).
Proof.
move=> ir [_ wor] uc vc; apply: Exercise2_7g => //.
move=> x xsr.  
set y := (Ixf x (compose u v)).
have sy: sub y (substrate r) by apply: Zo_S.
move: (inductive_max_greater or ir xsr) => [m [ms mm xm]].
move: uc vc => /Zo_P [p1 p2] => /Zo_P [p3 p4].
move: p2 p4=> [q1 q2 q3] [q4 q5 q6].
move: p1 p3 => /functionsP [fu su tu] /functionsP[fv sv tv].
have cuv: composable u v by split => //; ue.  
have mv: inc m (source v) by ue.
move: q1 =>[_ _ _ incf]; move: (incf _ _ (q5 _ ms)) => le1.
move: (q2 _ ms) => le2.
have ne: nonempty y.
  exists m; apply: Zo_i => //; split => //; rewrite compfV//; apply: mm; order_tac.
apply: (wor _ sy ne).
Qed.

Lemma Exercise2_7B1 u: inc u closures  -> cofinal r (fixpoints u).
Proof.
move /Zo_P => [/functionsP [ff sf tf] [pa pb pc]].
split; first by move => t /Zo_P[]; rewrite sf.
move => x xsr; exists (Vf u x); last by apply: pb.
apply/Zo_P; split; [ rewrite sf;Wtac; ue| by  apply: pc].
Qed.  


Lemma Exercise2_7B2 F: cofinal r F -> worder (induced_order r F) ->
  exists2 u, inc u closures & (fixpoints u) = F.
Proof.
move => [pa pb] pc.
pose M x:= Zo F (gle r x).
pose u x := the_least (induced_order r (M x)).
have  Ha x: inc x E -> nonempty (M x).
  by move/pb =>[y yF le]; exists y; apply/Zo_P.
have Hb x: inc x E -> sub (M x) (substrate (induced_order r F)).
  by move => xE; rewrite iorder_sr//; apply: Zo_S.
have Hc x: inc x E -> [/\ inc (u x) F, gle r x (u x)&
      forall t, inc t F -> gle r x t -> gle r (u x) t].
  move => xE; move: (Hb _ xE) => hb.
  have hc: sub (M x) F by apply/Zo_S.
  have hd:= (sub_trans hc pa).
  move: (iorder_osr or hd) => [qa qb].
  move: (proj2 pc _ hb (Ha _ xE)) => [y]; rewrite iorder_trans // => yl.
  move:(the_least_pr2 qa yl); rewrite -/(u x) => ->.
  case: yl; rewrite iorder_sr //;move/Zo_P => [he hf] hg; split => // t tf tg.
  have: inc t (M x) by apply/Zo_P.
  by move/hg/iorder_gle1.
have Hd x: inc x F -> u x = x.
   move => xF; move: (Hc _ (pa _ xF))=> [ha hb hc].
   have lexx: gle r x x by move: (pa _ xF) => xsr; order_tac.
   move: (hc _ xF lexx)=> leux; order_tac.
have ax: lf_axiom u E E by move => x /Hc/proj31/pa.
have He: function_prop (Lf u E E) (substrate r) (substrate r).
  by saw; apply: lf_function.
exists (Lf u E E).
   apply/Zo_P; split; first by apply/functionsP.
   split.
   -  split => // a b lab.
      move: (arg1_sr lab) (arg2_sr lab) => aE bE.
      rewrite ! LfV//;move: (Hc b bE)=> [qa qb _]; apply: (proj33 (Hc a aE) _ qa); order_tac.
   - move => x xE; rewrite LfV//; exact: (proj32 (Hc _ xE)).
   - move => x xE; move: (proj31 (Hc _ xE))=> uF.
     by rewrite (LfV ax xE) (LfV ax (pa _ uF)); apply: Hd.
set_extens t.
  move /Zo_P; aw; move => [tE]; rewrite LfV // => <-.
  exact:(proj31 (Hc _ tE)).
move => tF; move: (pa _ tF) => tR; apply/Zo_i; aw; trivial.
by  rewrite LfV//; apply: Hd.
Qed.  

Lemma Exercise2_7B3 F: cofinal r F -> worder (induced_order r F) ->
  ~ (has_greatest r) -> exists F1 F2,
   [/\ cofinal r F1, worder (induced_order r F1), 
       cofinal r F2, worder (induced_order r F2) & disjoint F1 F2].
Proof.
move => [sfE cof] wo1 nger.
move:(iorder_sr or sfE) => sif.
pose aux X:= sub X F /\ forall x, inc x F -> exists2 y, inc y X & gle r x y. 
have Ha X: aux X ->  cofinal r X.
  move => [ss hyp]; split; first  by apply: (sub_trans ss sfE).
  move => t /cof [y /hyp [z za zb] zc]; ex_tac; order_tac.
suff: exists F1 F2,
   [/\  aux F1, aux F2 & disjoint F1 F2].
  move => [f1 [f2 [ha hb he]]]; exists f1, f2.
  move:(Ha _ ha)(Ha _ hb)   => cf1 cf2.
  move: (proj1 ha)(proj1 hb);  rewrite - sif => hb' hd'.
  move:(induced_wor wo1 hb') (induced_wor wo1 hd').
  rewrite (iorder_trans _ (proj1 ha)) (iorder_trans _ (proj1 hb)) => hb'' hd''.
  done.
move:(the_ordinal_iso1 wo1)(OS_ordinal wo1); set f := the_ordinal_iso _. 
set alpha := ordinal _ => isf oa.
move: isf =>[ora orf]; rewrite ordinal_o_sr sif; move => [bf sf tf] fiso.
move: (proj1 (proj1 bf)) => ff.
have alim x: inc x alpha -> inc (osucc x) alpha.
  move => xa; case: (ordinal_limA oa).
  - rewrite /ord_zero;move => h; empty_tac1 x.
  - move => [y oy yv].
    have ya: inc y alpha by rewrite yv; fprops.
    set z := Vf f y; case nger; exists z.
    have zF: inc z F by  rewrite /z; Wtac.
    have zE: inc z E by exact: (sfE _ zF).
    split => // t /cof [u ua ub].
    rewrite - tf in ua; move: (proj2 (proj2 bf) _ ua) =>[v vsf vv].
    rewrite - sf in ya.
    have le1: gle (ordinal_o alpha) v y.
       apply/ordo_leP; rewrite - sf; split => //.
       by move: vsf; rewrite sf yv; apply: ordinal_sub3.
       move/(fiso v y vsf ya): le1 => /iorder_gle1.
    rewrite -/z - vv=> le2; order_tac.
  - by move/limit_ordinal_P => [_ ] h; apply/(oltP oa)/h /(oltP oa).
have osa x: inc x alpha -> ordinalp x by apply: Os_ordinal.
pose even x := orem x \2o = \0o.
pose evena x :=  inc x alpha /\ even x.
pose odda x :=  inc x alpha /\ ~even x.
have ooq x: ordinalp x -> ordinalp (oquo x \2c).
   move => ox; exact: (proj41 (oquoremP ox olt_02)).
have evenp1 x: ordinalp x -> even x -> x = \2o *o oquo x \2o.
  move => ox ex; move: (proj43 (oquoremP ox olt_02)).
  by rewrite ex (osum0r (OS_prod2 OS2 (ooq _ ox))).
have evens x: evena x -> odda (osucc x).
   move: OS1 olt_12 => qa qb [ha hb]; split; [by apply: alim | move => bad].
   move:  (osa _ ha) => ox; move: (ooq _ ox) => op.
   move: (sym_eq (osucc_pr ox)).
   rewrite {2} (evenp1 _ ox hb) => eq1.
   have dp: (odiv_pr0 (osucc x) \2o (oquo x \2o) \1c) by split.
   move: (proj2(oquoremP2 (OS_succ ox) olt_02 dp)); rewrite bad.
   exact: C1_ne_C0.
have odds x: odda x -> evena (osucc x).
  move =>[ax nex]; split; first by apply: alim.
  move:  (osa _ ax) => ox.
  move:(oquoremP ox olt_02)=> [orq orr qv]. 
  rewrite - {2}osucc_one; move/oltSleP.
  case: (equal_or_not(orem x \2o) \1o); last first.
    move => q1 q2; move: (conj q2 q1);rewrite - osucc_zero; move/oltSleP.
    by move/ole0=> bad; case: nex.
  move => eq1 _.
  have qa :=  (OS_succ orq).
  have dp: (odiv_pr0 (osucc x) \2o (osucc (oquo x \2o)) \0c).
    split;[ exact: qa | exact: OS0 | | exact: olt_02]. 
    rewrite (osum0r (OS_prod2 OS2 qa)) (oprod2_succ OS2 orq) - {3} osum_11_2.
    by rewrite (osumA (OS_prod2 OS2 orq) OS1 OS1) -{1} eq1 - qv osucc_pr.
   by move: (proj2(oquoremP2 (OS_succ ox) olt_02 dp)). 
have bde x: inc x alpha -> exists2 y, evena y & x <=o y.
   move => xa;move:(osa _ xa) => ox; case: (p_or_not_p (even x)) => ex.
     exists x; split => //.   
   move: (odds x (conj xa ex))=> ey.
   by exists (osucc x) => //; apply: oleS.
have bdo x: inc x alpha -> exists2 y, odda y & x <=o y.
   move => xa;move:(osa _ xa) => ox; case: (p_or_not_p (even x)) => ex.
      exists (osucc x); [ exact:(evens _ (conj xa ex)) | by apply: oleS].
   by exists x; split.
set F1 := Zo F (fun z => even (Vf (inverse_fun f) z)).
set F2 := Zo F (fun z => ~even (Vf (inverse_fun f) z)).
exists F1, F2; split.
- split; [ apply: Zo_S | move => x xf]; set y := Vf (inverse_fun f) x.
  have xtf: inc x (target f) by ue.
  have ya: inc y alpha by rewrite - sf; apply:(inverse_Vis bf).
  move:(bde _ ya) => [z [za zb]] le1. 
  have le2: gle (ordinal_o alpha) y z.
      by apply/ordo_leP; split => //; case: le1.
  rewrite - sf in ya za.
  move/(fiso _ _ ya za): le2 => /iorder_gle1.
  rewrite /y (inverse_V bf xtf) => eq1; exists (Vf f z) => //.
  apply/Zo_P; rewrite (inverse_V2 bf za); split => //; Wtac.
- split; [ apply: Zo_S | move => x xf]; set y := Vf (inverse_fun f) x.
  have xtf: inc x (target f) by ue.
  have ya: inc y alpha by rewrite - sf; apply:(inverse_Vis bf).
  move:(bdo _ ya) => [z [za zb]] le1. 
  have le2: gle (ordinal_o alpha) y z.
      by apply/ordo_leP; split => //; case: le1.
  rewrite - sf in ya za.
  move/(fiso _ _ ya za): le2 => /iorder_gle1.
  rewrite /y (inverse_V bf xtf) => eq1; exists (Vf f z) => //.
  apply/Zo_P;rewrite (inverse_V2 bf za); split => //; Wtac.
- by apply: disjoint_pr => t /Zo_P [_ ha] /Zo_P [_]; case.
Qed.


Lemma Exercise2_7B4 F: cofinal r F -> worder (induced_order r F) ->
  ~ (has_greatest r) -> nonempty E ->
  exists u v, [/\ inc u closures, inc v closures &
   ~  has_supremum closure_ordering (doubleton u v)].
Proof.
move => cof wor nge be.
move: (Exercise2_7B3 cof wor nge)=> [F1 [F2 [cof1 wor1 cof2 wor2 dis]]].
move:(Exercise2_7B2 cof1 wor1) (Exercise2_7B2 cof2 wor2) =>[u ua ub] [v va vb].
exists u,v; split => //.
move: (Exercise2_7b) => [oce sce] hs.
move: (ua)(va); rewrite - sce => ua' va'.
case: (sup_pr oce ua' va' hs); set w := sup _ _ _ => wa wb _.
move/Exercise2_7aP:(wa)=> [_ wc _].
move/(Exercise2_7dP ua wc): wa; rewrite ub => qa.
move/(Exercise2_7dP va wc): wb; rewrite vb => qb.
move: be => [x xE].
move/Zo_P: wc => [/functionsP [fw sw tw] [qc qd qe]].
have xzf: inc (Vf w x) (fixpoints w).
  by apply/Zo_P; split; [ rewrite sw; Wtac| apply: qe].
empty_tac1 (Vf w x). 
Qed.

Lemma Exercise2_7B5 : has_greatest r -> has_greatest (closure_ordering).
Proof.
move => [a [asr age]].
have ha: cofinal r (singleton a).
  split; [ by  move =>t /set1_P-> |  move => x xsr; ex_tac].
have hb: worder (induced_order r (singleton a)). 
  move: (iorder_osr or (set1_sub asr)) => hb.
  apply: (worder_set1 hb).
move: (Exercise2_7B2 ha hb) =>[u uc etc].
exists u => //; split; rewrite (proj2 Exercise2_7b) => // v vc.
apply/ (Exercise2_7dP vc uc); rewrite etc => t /set1_P ->.
move: vc =>/Zo_P[/functionsP[ff sf tf] [qa qb qc]].
apply/Zo_P; rewrite sf; split => //.
move: (qb _ asr) => h1. move: (age _ (arg2_sr h1))=> h2; order_tac.
Qed.

End Exercise27.


Lemma Exercise2_7B6 r: 
  has_greatest r -> inductive r.
Proof. move=> [u [us ug]] x xsr tor; exists u; split;fprops.   Qed.


Lemma Exercise2_7B7 r: total_order r -> inductive r -> has_greatest r.
Proof.
move=> tor h; set F := substrate r; have si:= (@sub_refl F).
move:(h F si (total_order_sub tor si)) =>[x [xa xb]].
by exists x.
Qed.



(** Let's consider a counter-example; we consider all pairs 
[(x,0)] and [(x,1)], where [x] is an integer, ordered by:
 [(x,0) < (y,1)] and [(x,0)<(y,0)] whenever [x<y], 
while  [(x,1)<(y,1)]  whenever [y<x]. It has a greatest element, 
thus is inductive  *)

Lemma Exercise2_7A2 r r': order r  -> order r' ->
  has_greatest r' -> inductive  (order_sum2 r r').
Proof. 
move=> or or' [u ug];apply: Exercise2_7B6. 
by move: (orsum2_greatest' or or' ug)=> h; exists  (J u C1).
Qed.

Definition NNstar := 
  order_sum2 Nat_order (opp_order Nat_order).

Lemma Exercise2_7A3: 
  [/\ order_on NNstar (canonical_du2 Nat Nat) &
    (forall x x', gle NNstar x x' <->
    [/\ inc x (canonical_du2 Nat Nat),
      inc x' (canonical_du2 Nat Nat) &
     [\/  [/\ Q x = C0, Q x' = C0 & (P x) <=c (P x')], 
          [/\ Q x <> C0, Q x' <> C0 & (P x') <=c (P x)] |
         (Q x = C0 /\ Q x' <> C0)]])].
Proof. 
rewrite /NNstar.
move: Nat_order_wor=> [[or _] s1].
move: (opp_osr or) => [or1]; rewrite s1 => s2.
split; first split.
     by apply: orsum2_or.
   by rewrite orsum2_sr // s1 s2.
move=> x x'; split.
  move /orsum2_gleP; rewrite  s1 s2; move => [p1 p2 p3];split => //.
  case: p3; first by move => [q1 q2] /Nat_order_leP [_ _ s4]; constructor 1.
   by move =>  [q1 q2] /opp_gleP /Nat_order_leP [_ _ s4]; constructor 2.
  by move => q1; constructor 3.
move => [p1 p2 p3]; apply /orsum2_gleP; rewrite  s1 s2; split => //.
have aux: forall z, inc z (canonical_du2 Nat Nat) -> inc (P z) Nat.
   by move=> z /candu2P[_ ]; case; case.
case: p3.
    move => [q1 q2 q3]; constructor 1;split => //;apply /Nat_order_leP. 
    by split => //; apply: aux.
  move => [q1 q2 q3]; constructor 2;split => //. 
  by apply /opp_gleP/Nat_order_leP;split => //; apply: aux.
by move => q1; constructor 3.
Qed.

Lemma Exercise2_7A4: inductive NNstar.
Proof. 
move: (Nat_order_wor) => [[or _] bs].
apply:  Exercise2_7A2 => //.
  apply: (proj1 (opp_osr or)).
exists \0c; apply: least_opposite =>//.
have ns0 := NS0.
split; first by rewrite bs.
move => x; rewrite bs => xb; apply /Nat_order_leP; split => //. 
exact: (cle0n xb).
Qed.

(** If [f: N -> N] is a function; we extent it to [E] by
  [g((x,0)) = (f(x),0)] and [g((x,1)) = ( x,1)]. If [f] is a closure so is [g] *)


Definition extension_to_NNstar f :=
  Lf (fun z=> Yo (Q z = C0) (J (Vf f (P z)) C0) z) 
  (substrate NNstar) (substrate NNstar).

Lemma Exercise2_7A5 f (g:= extension_to_NNstar f) (E:= substrate NNstar):
 function_prop f Nat Nat ->
   [/\ (forall x, natp x -> Vf g (J x C0) = (J (Vf f x) C0)),
       (forall x, inc x E -> Q x = C0 -> 
         (P (Vf g x)  = Vf f (P x) /\ Q (Vf g x) = C0)),
    (forall x, inc x E -> Q x <> C0 ->  Vf g x = x) & 
    function_prop g E E].
Proof.
move=>  [ff sf tf].
move: Exercise2_7A3 => [[_ ss] _]. 
have ta:(lf_axiom (fun z=> Yo (Q z = C0) (J (Vf f (P z)) C0) z)
  (canonical_du2 Nat Nat) (canonical_du2 Nat Nat)).
  move: C1_ne_C0 => tpd.
  move=> t /candu2P.
  move=> [pt]; case; move=> [Pt Qt]; rewrite Qt; Ytac0. 
    apply: candu2_pra; Wtac.
  by rewrite - pt Qt; apply: candu2_prb.
rewrite /g /extension_to_NNstar /E ss.
split => //.
    move=> x xB; rewrite LfV//; aw; [by Ytac0 | by apply: candu2_pra].
  move=> x xE; rewrite LfV//; move=> ->; Ytac0; saw.
  move=> x xE; rewrite LfV//; move=> h; Ytac0; fprops.
by red; saw; apply: lf_function.
Qed.

Lemma Exercise2_7A6: forall f, closure f Nat_order ->
  closure  (extension_to_NNstar f) NNstar.
Proof. 
move=> f [ [ob _ [ff sf tf] incf] c1 c2].
move: (proj2 Nat_order_wor) => bos. 
have fp: function_prop f Nat Nat by split => //; ue.
move: (Exercise2_7A5 fp). 
set g:= (extension_to_NNstar f); set (E:=substrate NNstar).
move=> [ga0 ga gb [fg sg tg]].
move: Exercise2_7A3 => [[oNN sNN] leNNP].
rewrite /E sNN in sg tg ga gb.
split.
    split;fprops; first by  saw; ue.
    move=> x y =>/leNNP [p1 p2 p3]; apply /leNNP; split; try Wtac.
  case: p3.
        move=> [q1 q2 q3]; constructor 1.
        move: (ga _ p1 q1) (ga _ p2 q2) => [r1 r2] [r3 r4].
        rewrite r1 r2 r3 r4; split => //.
        have aux: gle Nat_order (P x) (P y).
          apply /Nat_order_leP => //; split => //.
            by move:p1 => /candu2P [ _ ]; case; move=> [px qx].
          by move:p2 => /candu2P [ _ ]; case; move=> [px qx].
        by move: (incf _ _ aux) => /Nat_order_leP [_ _].
      move=> [q1 q2 q3];  constructor 2.
      by move: (gb _ p1 q1) (gb _ p2 q2) => -> ->.
    move=> [q1 q2];  constructor 3.
    by move: (ga _ p1 q1) (gb _ p2 q2) => [_] -> ->.
  rewrite sNN; move=> x xs; apply /leNNP; split => //.
  rewrite -tg; apply: Vf_target=> //; ue.
  move: (xs) =>/candu2P [ _ ]; case.
    move=> [pb qx]; move: (ga _ xs qx); move=> [pw qw]; constructor 1.
    rewrite pw qw;split => //; rewrite bos in c1; move: (c1 _ pb).
    by move /Nat_order_leP => [_ _].
  move=>  [pb qx]; have qqx: (Q x <> C0) by  rewrite qx; fprops.
  move: (gb _ xs qqx) => ->; constructor 2; split;fprops.
move=> x; rewrite sNN => xs.
move: (xs) => /candu2P [ _ ]; case.
  move=> [px qx]; move: (ga _ xs qx) ; move=> [pw qw].
  have wa: inc (Vf g x) (canonical_du2 Nat Nat).
     rewrite -tg; apply: Vf_target => //; ue.
  move: (ga _ wa qw) ; move=> [pw2 qw2].
  have wb: inc (Vf g (Vf g x)) (canonical_du2 Nat Nat) by Wtac.
  move: wa => /candu2P [pw3 _ ].
  move: wb =>/candu2P [pw4 _ ].
  apply: pair_exten => //; [ rewrite pw2 pw c2 //; ue | rewrite qw2 //].
move=> [_ qx]; have qqx: (Q x <> C0) by  rewrite qx; fprops.  
by move: (gb _ xs qqx) => aux; rewrite {1} aux. 
Qed.

(** Let [u(x)] be [x+1] if [x] is even and [x] otherwise,
and let [v(x)] be [x+1] if [x] is odd and [x] otherwise. These are closures, 
and have no common fix-point, thus no least upper bound.
Note that the set of integers is not inductive, so that this is not a 
counter-example to Bourbaki *)

Lemma Exercise2_7A7:
  (lf_axiom (fun z => Yo (evenp z) z (csucc z)) Nat Nat).
Proof. by move=> t tb /=; Ytac h => //; apply:NS_succ.  Qed.

Lemma Exercise2_7A8:
  (lf_axiom (fun z => Yo (evenp z) (csucc z) z) Nat Nat).
Proof. by move=> t tb /=; Ytac h => //; apply:NS_succ. Qed.


Lemma Exercise2_7A9:  
  closure (Lf (fun z => Yo (evenp z) z (csucc z)) Nat Nat) Nat_order.
Proof. 
move: Nat_order_wor Exercise2_7A7 => [[ob _] sb]  ta.
split => //.
    split => //; first by  saw => //; apply: lf_function. 
    move=> x y /Nat_order_leP [xB yB xy]; rewrite !LfV//.
    apply /Nat_order_leP;split => //; try apply:ta => //.
    Ytac evx; Ytac evy => //.
        exact: (cleT xy (cleS yB)).
      apply /(cleSltP xB); split =>// q; apply: evx; ue.
    by apply /(cleSSP (CS_nat xB) (CS_nat yB)). 
  move=> x; rewrite sb => xN; move:(NS_succ xN) =>sxN.
  rewrite LfV//; apply /(Nat_order_leP); split => //; Ytac evx; fprops. 
move=>x ;rewrite sb => xN; rewrite (LfV  ta xN);move: (NS_succ xN) => sxN.
by Ytac evx; rewrite LfV//; [ | move: (succ_of_odd (conj xN evx)) => ok ]; Ytac0.
Qed.

Lemma Exercise2_7A10:  
  closure (Lf (fun z => Yo (evenp z) (csucc z) z) Nat Nat) Nat_order.
Proof. 
move: Nat_order_wor Exercise2_7A8 => [[ob _] sb] ta.
split => //.
   split => //; first by red;aw; split =>//; apply: lf_function. 
    move=> x y /Nat_order_leP [xN yN xy]; rewrite !LfV//; apply /Nat_order_leP.
    move: (NS_succ xN)(NS_succ yN) => sxN syN.
    split => //;fprops; Ytac evx => //;Ytac evy => //.
        by apply /(cleSSP (CS_nat xN) (CS_nat yN)).
      apply /(cleSltP xN); split =>// q; apply: evy; ue.  
    exact: (cleT xy (cleS yN)).
  move=> x;rewrite sb => xN;  move: (NS_succ xN) => sxN.
  apply /Nat_order_leP; rewrite LfV//;split => //; Ytac evx; fprops.
move=>x ;rewrite sb => xN;  move: (NS_succ xN) => sxN.
rewrite (LfV ta xN); Ytac evx; rewrite LfV//; fprops;last by Ytac0.
by rewrite (Y_false (proj2(succ_of_even evx))).
Qed.

Lemma Exercise2_7A11 x w
    (u :=Lf (fun z => Yo (evenp z) (csucc z) z) Nat Nat)
    (v :=Lf (fun z => Yo (evenp z) z (csucc z)) Nat Nat):
   natp x -> (Vf u x) <=c w -> (Vf v x) <=c w ->
   x <> w.
Proof. 
move=> xB le1 le2 xw; rewrite /u/v.
suff: (csucc x) <=c w  by apply /(cleSltP xB); case.
move: (Exercise2_7A7)(Exercise2_7A8) => p1 p2.
by move: le1 le2;rewrite /u/v !LfV//; Ytac evx; Ytac0. 
Qed.

(** Consider the extensions of [u] and [v] to [E]. These are closures in an 
inductive set. We have to many upper bounds, for instance [x -> sup(x,y)], 
where [y] has the form [(z,1)] is an upper bound, and [y=(0,1)] gives the
 greatest upper bound.

If [w] is any upper bound, for any [x],  [w(x,0)] has the form [(y,1)]
since [u] and [v] have no common fix-point. Assume [w(0,0) = (k,1)].
Since [(0,0)] is the least element we have [w(x) = (k,1)] whenever [x <=(k,1)].
Remembet that [(k+1,1) < (k,1)].
Let [f] be the function that maps [x] to [(k+1,1)] if [x<= (k+1,1)] and [w(x)] 
otherwise. Then [f<w] and is an upper bound.

*)
Lemma Exercise2_7A12: exists r u v,
  [/\ order r, inductive r,
  inc u (closures r), inc v (closures r) &
   ~  has_supremum (closure_ordering r) (doubleton u v)].
Proof. 
move: Exercise2_7A7 Exercise2_7A8 Exercise2_7A9 Exercise2_7A10 Exercise2_7A11.
set (u :=Lf (fun z => Yo (evenp z) (csucc z) z) Nat Nat).
set (v :=Lf (fun z => Yo (evenp z) z (csucc z)) Nat Nat).
move=> ta1 ta2 c1 c2 ns.
move:(Exercise2_7A6 c1) (Exercise2_7A6 c2).
set (u1:=  extension_to_NNstar u).
set (v1:=  extension_to_NNstar v).
move=> c3 c4.
exists NNstar, u1,v1.  
move: Exercise2_7A3 Exercise2_7A4 => [[oNN sNN] gNNP] iNN.
have wc:forall w, closure w NNstar -> inc w (closures NNstar).
  move=> w wc; apply: Zo_i => //. 
  by move: wc =>[[_ _  xx _] _ _]; apply /functionsP.
move: (wc _ c3) (wc _ c4) => vc uc.
split => //.
move: (Exercise2_7b oNN) => [oce sce] hs.
rewrite - sce  // in uc vc.
move: (sup_pr oce uc vc hs).
set w := sup _ u1 v1.
move => [/(Exercise2_7aP oNN) [_ wcl le1] /(Exercise2_7aP oNN) [_ _ le2] ale3].
have fpu: (function_prop u Nat Nat).
  by red; rewrite /u; aw;split => //; apply: lf_function.
have fpv: (function_prop v Nat Nat).
  by red; rewrite /v; aw;split => //; apply: lf_function.
move: (Exercise2_7A5 fpu) => /=;  rewrite -/u1.
move=> [upa1 upa upb [fu1 su1 tu1]].
move: (Exercise2_7A5 fpv) => /=;  rewrite -/v1.
move=> [vpa1 vpa vpb [fv1 sv1 tv1]].
move: (wcl) => /Zo_P [] /functionsP [fw sw tw] cw.
have wp1: forall x, inc x Nat -> Q (Vf w (J x C0)) = C1. 
  move=> x xB.
  have ps: (inc (J x C0) (substrate NNstar)).
    by rewrite sNN; apply: candu2_pra. 
  have: (inc (Vf w (J x C0)) (substrate NNstar)). 
    rewrite -tw; Wtac.
  rewrite sNN => /candu2P [p1]; case; case=> //. 
  set (y := P (Vf w (J x C0))). 
  move=> p2 p3.
  have aux: (J y C0 = Vf w (J x C0)).
    by symmetry;rewrite /y;apply: pair_exten;fprops; aw.
  have Js: (inc (J y C0) (substrate NNstar)).
    by rewrite sNN; apply: candu2_pra.
  move: (cw) => [_ _ p4]; move: (p4 _ ps);rewrite -aux => aux1.
  move: (le1 _ Js) (le2 _ Js) => /gNNP [p5 p6 p7] /gNNP [p8 p9 p10]. 
  move: p7; rewrite aux1 pr2_pair; case; last first.
      by move => [_]; case.
    by move => [_ h _]; case: h.
  move: p10; rewrite aux1 pr2_pair; case; last first.
      by move => [_]; case.
    by move => [_ h _]; case: h.
  move=>  [p13 _ p14] [p11 _ p12].
  have aux2: Q (J y C0) = C0 by aw.
  move: (vpa _ Js aux2); aw;  move=> [p15 _]; rewrite p15 in  p14.
  move: (upa _ Js aux2); aw;  move=> [p16 _]; rewrite p16 in  p12.
  have yB: inc y Nat.
   by move: p9 => /candu2P [_]; case; case.
  by case: (ns _ _ yB p12 p14); aw.
move: (wp1 _ NS0) NS0 => p1 ns0. 
set (k:= Vf w (J \0c C0)).
have Js:(inc (J \0c C0) (substrate NNstar)). 
  rewrite sNN; apply: candu2_pra; fprops.
have ks: (inc k (substrate NNstar)) by rewrite /k;Wtac; rewrite sw sNN; fprops.
have Pk: (inc (P k) Nat).
  by move: ks; rewrite sNN => /candu2P [ _ ]; case; case.
move: (wp1 _ NS0) => Qk.
move: cw => [[_ _ _ incf] wca wcb].
have Pk1: (forall x, gle NNstar x k -> Vf w x = k).
  move=> x xk. 
  have aux : (gle NNstar (J \0c C0) x).
    have xs: (inc x (substrate NNstar)) by order_tac. 
    apply/gNNP; rewrite - sNN; saw.  
    move: xs; rewrite sNN  => /candu2P  [ _]; case; move => [px qx].
        by constructor 1; split => //; apply: cle0n. 
      rewrite qx;constructor 3;split;fprops.
   move: (incf _ _ xk)(incf _ _ aux); rewrite (wcb _ Js) -/k => r1 r2.
   order_tac.
have q7:  Vf w k = k by rewrite Pk1 //; order_tac.
move: (NS_succ Pk)  => SPK.
set (k':= J (csucc (P k)) C1).
have j's: (inc k' (substrate NNstar)).
  rewrite /k' sNN;  apply: candu2_prb; fprops.
have lt1: (glt NNstar k' k).
  have ha: inc k' (substrate NNstar) by rewrite /k' sNN; apply:candu2_prb.
  move: (cltS Pk) => [leP neP].
  split. 
    apply /gNNP; rewrite - sNN /k';saw; constructor 2.
    rewrite -/k Qk; split;fprops;apply: leP.
    by move=> kk'; move: (f_equal P kk');rewrite /k'; aw => aux;case: neP. 
set (ww := fun z=> Yo (gle NNstar z k') k' (Vf w z)).
have ta: (lf_axiom ww (substrate NNstar) (substrate NNstar)).
  move=> z zs; rewrite /ww;Ytac cp => //; Wtac.
set (w' := Lf ww (substrate NNstar) (substrate NNstar)).
have fw': (function w') by apply: lf_function.
have q3: Q k' <> C0 by rewrite /k'; aww.
have q4: forall x, gle NNstar x k' -> Vf w' x = k'.
  by move=> x xk; rewrite /w' /ww LfV//; [ Ytac0 | order_tac].
have q5: forall x, inc x (substrate NNstar)  -> ~ (gle NNstar x k') 
  -> Vf w' x = Vf w x.
  by move=> x xs xk; rewrite /w' /ww LfV//; Ytac0.
have q6: forall y, inc y (substrate NNstar) -> ~ gle NNstar y k'
   ->  gle NNstar k y.
  move=> y ysr ng;apply  /gNNP; rewrite - sNN; split => //; constructor 2.
  move: (ysr); rewrite sNN =>/candu2P [py];  case.
    move=> [pyb Qya]; case: ng;apply /gNNP; rewrite - sNN. 
    by split => //; constructor 3. 
  move=> [Pyb Qy]; split => //; [ rewrite Qk; fprops |  rewrite Qy; fprops |].
  have cy:cardinalp (P y) by fprops.
  have ck:cardinalp (P k) by fprops.
  case:  (cleT_el cy ck) => //.
  move=> lt2; case: ng; apply /gNNP; rewrite - sNN; split => //; constructor 2.
  rewrite Qy;split => //; fprops.
  by rewrite /k'; aw; apply /cleSltP. 
have w1: (forall x, inc x (substrate NNstar) ->
    (gle NNstar (Vf u1 x)  (Vf w' x) /\  gle NNstar (Vf v1 x)  (Vf w' x))). 
  move=> x xs.
  move: (le1 _ xs) (le2 _ xs) => le1s le2s.
  case:  (p_or_not_p  (gle NNstar x k')) => xk; last first.
    have ->:(Vf w' x = Vf w x) by rewrite /w' /ww LfV//; Ytac0. 
    split => //; rewrite (q4 _ xk).
  rewrite (q4 _ xk).
  case: (equal_or_not (Q x)  C0) => qx.
    move: (upa _ xs qx)(vpa _ xs qx) => [_ q1] [_ q2].
    by split; apply /gNNP; rewrite - sNN ?q1 ?q2;
      split => //;try order_tac; constructor 3. 
  by move: (upb _ xs qx)(vpb _ xs qx) => -> ->. 
have icw':increasing_fun w' NNstar NNstar.
  rewrite /w';split => //; first saw; move=> x y xy.
  have xs1: inc x (substrate NNstar) by  order_tac.
  have xs2: inc y (substrate NNstar) by  order_tac.
   case: (p_or_not_p  (gle NNstar x k')) => xk; last first.
    have  yk: ~ gle NNstar y k' by dneg wk; order_tac.
    by rewrite (q5 _ xs1 xk)  (q5 _ xs2 yk); apply: incf.
  case: (p_or_not_p  (gle NNstar y k')) => yk.
    by rewrite (q4 _ xk)  (q4 _ yk); order_tac.
  rewrite  (q4 _ xk)  (q5 _ xs2 yk).
  move: (incf _ _ (q6 _ xs2 yk)); rewrite q7.
  move: lt1 => [lt1 _] le3; order_tac.
have cw': (closure w' NNstar). 
  split => //; move=> x xs.
   case: (p_or_not_p  (gle NNstar x k')) => xk; first by rewrite (q4 _ xk). 
   by rewrite (q5 _ xs xk); apply: wca.
  case: (p_or_not_p  (gle NNstar x k')) => xk.
    rewrite (q4 _ xk); apply: q4; order_tac; order_tac.
  rewrite (q5 _ xs xk).
  case: (p_or_not_p  (gle NNstar (Vf w x) k')) => xk'; last first.
    have ws: inc (Vf w x) (substrate NNstar) by move: (wca _ xs)=> h; order_tac.
    by rewrite (q5  _ ws xk'); apply: wcb.
  move: (incf _ _ (q6 _ xs xk)).
  rewrite (q4 _ xk') -/k'; rewrite q7 => aux.
  have aux1:  gle NNstar k k' by order_tac. 
  order_tac.
have res0: inc w' (closures NNstar).
  by apply: Zo_i => //; apply /functionsP;split => //; rewrite /w';aw.
have res1: gle (closure_ordering NNstar) u1 w'.
   apply /(Exercise2_7aP oNN);split => //.
    by apply  Zo_i => //; apply /functionsP. 
  by move=> i isr; case: (w1 _ isr).
have res2: gle (closure_ordering NNstar) v1 w'.
  apply /(Exercise2_7aP oNN);split => //.
     by apply  Zo_i => //; apply /functionsP.
  by move=> i isr; case: (w1 _ isr).
move:(ale3 _  res1 res2).
apply /(Exercise2_7aP oNN). 
move=> [_ _ bad]; move: (bad _ j's); rewrite q4; last by order_tac.
move: lt1 => [lt2 lt3].
rewrite (Pk1  _ lt2) => aux; case: lt3; order_tac.
Qed.

(** ---- Exercise 2.8. Ramified and completely ramified sets *)
Definition ramified r :=
  forall x y, glt r x y -> exists z, [/\ glt r x z, ~ gle r y z &  ~ gle r z y].

Definition ramifiedc r :=
  ramified r /\ not (exists x, maximal r x).

Lemma Exercise2_8a r: order r -> anti_directed r -> ramified r.
Proof. 
move=> or /(Exercise1_23hP or)  [p1 p2]. 
move=> x y xy; move: (p1 _ _ xy) => [z xz p3]; exists z.
have zz:  (gle r z z) by order_tac; order_tac. 
have yy:  (gle r y y) by order_tac; order_tac. 
split => //;[ move=> yz; exact (p3  _  yz zz)| move=> zy;exact: (p3  _  yy zy)].
Qed.


(** The following set has a maximal element *)
Definition  Exercise2_8a_R r a :=
  Zo (\Po (substrate r))
  (fun z => ramified (induced_order r z) /\ 
    least  (induced_order r z) a).

Lemma Exercise2_8b r a F: order r ->
  (inc F (Exercise2_8a_R r a) <->
  [/\ sub F (substrate r),
      forall x y, glt r x y -> inc x F -> inc y F -> 
       exists z, [/\ glt r x z, ~ gle r y z,  ~ gle  r z y & inc z F],
     inc a F &
     (forall z, inc z F -> gle r a z)]).
Proof. 
move=> or; split.
  move => /Zo_P [] /setP_P Fd [p1 p2]. 
  move: (p2) => []; rewrite iorder_sr // => pa pb.
  have pb': forall z , inc z F -> gle r a z.
   by move => z zf; move /iorder_gleP: (pb _  zf) => [_ _].
  split => //  x y xy xF yF. 
  have xy': glt (induced_order r F) x y by apply /iorder_gltP. 
  move: (p1 _ _ xy'); move=> [z []] /iorder_gltP [_ zF xz] /iorder_gleP p4 
   /iorder_gleP p5; exists z; split => // h; [ by case: p4 | by case: p5].
move=> [pF p1 p2 p3]; apply: Zo_i; first by apply /setP_P.
split; last by split; rewrite iorder_sr // => x xF;apply /iorder_gle0P=> //; apply: p3.
move=> x y; move/iorder_gltP  =>[xF yF xy].
move: (p1 _ _ xy xF yF) => [z [z1 z2 z3 z4]]; exists z;split.
    by apply /iorder_gltP.
  by move /iorder_gleP => [_ _].
by move /iorder_gleP => [_ _].
Qed.

Lemma Exercise2_8c r a: order r -> inc a (substrate r) ->
  exists A, maximal (sub_order  (Exercise2_8a_R r a)) A.
Proof.
move=> or ar; apply: Zorn_lemma; first by fprops. 
red; aw;  set (F := Exercise2_8a_R r a).
move: (sub_osr F) => [oF sF].
move => X Xsr []; rewrite iorder_sr // => [oX toX]; rewrite /upper_bound sF.
have asr: sub (singleton a) (substrate r) by move => t /set1_P ->.
have leX: (forall x y, inc x X -> inc y X -> sub x y \/ sub y x).
  move => x y xX yX; move: (toX _ _ xX yX).
  case => aux; move: (iorder_gle1 aux) => /sub_gleP [_ _ h]; in_TP4.
case: (emptyset_dichot X)=>xe. 
  exists (singleton a); split.
    apply: Zo_i; first by apply /setP_P; apply: set1_sub.
    split.
       by move=> x y [cxy]; move: (iorder_gle3 cxy) => [] /set1_P -> /set1_P ->.
     red; rewrite iorder_sr//;split;fprops;move=> x /set1_P ->; apply /iorder_gle0P;fprops.
     by order_tac.
  move => y yX; empty_tac1 y.
rewrite sF in  Xsr.
have uX: (inc (union X) F).
  rewrite /F (Exercise2_8b _ _ or); split => //.
        move=> t /setU_P [y ty yX]; move: (Xsr _ yX) => /Zo_P. 
        by move=> [yp _]; move: yp => /setP_P; apply.
      move => x y xy /setU_P  [x' xx' xX'] /setU_P [y' yy' yX'].
      have [z [zX xz yz]] : (exists z, [/\ inc z X, inc x z & inc y z]). 
        case: (leX _ _ xX' yX') => xy';[ exists y'| exists x']; split; fprops.
      move: (Xsr _ zX); rewrite (Exercise2_8b _ _ or); move=> [_ h _].
      move: (h _ _ xy xz yz) => [t [t1 t2 t3 t4]]; exists t; split => //.
      union_tac.
    move: xe => [e ex]; move: (Xsr _ ex); rewrite (Exercise2_8b _ _ or). 
    move=> [_ _ h _]; union_tac.
  move=> z /setU_P [x zx zX]; move: (Xsr _ zX).
  by rewrite (Exercise2_8b _ _ or); move=> [_ _ _ ]; apply.
exists (union X); split => //.
by move => x xF;apply/sub_gleP;split;fprops; apply: setU_s1.
Qed.

(** Bourbaki says  "every maximal element of [Exercise2_8a_R]
 is completely ramified". Is this true ? *)

Lemma Exercise2_8d r a A: order r -> inc a (substrate r) ->
  branched r ->
  maximal (sub_order  (Exercise2_8a_R r a)) A
  -> ramifiedc (induced_order r A).
 Proof.
move=> or asr br [As mz]; rewrite (proj2 (sub_osr _)) in As.
have aux: forall x, inc x (Exercise2_8a_R r a) -> sub A x-> x = A.
  move=> x xs xA; apply: mz; apply /sub_gleP; split => //.
move: (As) => /Zo_hi  [rA _].
move: As; rewrite (Exercise2_8b _ _ or); move => [p1 p2 p3 p4].
split => // [][b] []; rewrite iorder_sr // => bA bm.
move: br => [_ br1].
move: (br1 _  (p1 _ bA)) => [c [d [bc bd bcd]]]. 
Abort.

(** TODO: Give an example of a branched set  which is not ramified.  The
branched set defined in Exercise 1.24 (c) is completely ramified.

(d) Let [E] be a set in which each interval [interval_uc c] is
totally ordered. Show that [E] has an antidirected  cofinal subset*)



(** ---- Exercise 2.9; An ordinal sum is well-ordered if and only if [I] and
 each [Ei] is well-ordered. We have shown one half in the main text. For the 
converse we must assume all [Ei] nonempty.
*)

 
Lemma orsum_wor_aux r g: orsum_ax r g  -> worder (order_sum r g) -> 
   (allf g worder).
Proof. 
move=> [or sr alog] [or1 wor]i idg.
split; first by apply: alog.
move=> x xsr xne.
set (y := fun_image x  (fun z => (J z i))).
have ysr: (sub y (substrate (order_sum r g))).
   move => t /funI_P [z zx ->]. 
  by rewrite orsum_sr //;apply: disjoint_union_pi1 => //; apply: xsr.
have ney: (nonempty y) by apply: funI_setne.
move: (wor _ ysr ney) => [z []]; rewrite iorder_sr // => zy zle.
move: (zy);move=> /funI_P [t tx zt].
have Px: (inc (P z) x) by rewrite zt; aw.
exists (P z); red; rewrite iorder_sr//;last by apply: alog. 
split => //; move=> s sx; apply /iorder_gleP => //.
have py: (inc (J s i) y) by apply /funI_P; ex_tac.
move: (iorder_gle1(zle _ py)) => /orsum_gleP [_ _ ].
by rewrite /order_sum_r zt /glt; aw; case; case.
Qed.


Lemma orsum_wo_P r g: 
  orsum_ax r g -> allf g ne_substrate ->  
  (worder (order_sum r g) <-> worder r /\   allf^~ worder g).
Proof. 
move=> oa alne; move:(oa) =>[or sr alog].
split; last by move=> [p1 p2]; apply: orsum_wor => //.
move=> h; split; last exact:(orsum_wor_aux oa h).
split => // x xsr xne.
set (y := fun_image x  (fun z => (J (rep (substrate (Vg g z))) z))).
have ys:  (sub y (substrate (order_sum r g))).
  rewrite orsum_sr // => t /funI_P.
  move => [z zx ->]; have zdg: inc z (domain g) by rewrite - sr; apply: xsr.
  by apply: disjoint_union_pi1 => //; apply: rep_i; apply: alne.
have ney: nonempty y by apply: funI_setne.
move:h =>[ors wor].
move: (wor _ ys ney) => [z []]; rewrite iorder_sr//; move => zy zle.
have Qzx: (inc (Q z) x) by move: zy => /funI_P[t tx ->]; aw.
exists (Q z); red; rewrite iorder_sr//; split => //;  move=> t tx;apply /iorder_gle0P => //.
have py: (inc  (J (rep (substrate (Vg g t))) t) y) 
  by apply /funI_P;aw; ex_tac.
move: (zle _ py) => le1; move: (iorder_gle1 le1) => le2.
by move: (orsum_gle_id oa le2); aw.
Qed.


(** ---- Exercise 2.10: proved in the main text*)

(** Exercise 2.11; A lexicographic product is well-ordered if the index is 
finite and each factor is well-ordered; We show here the converse. 
First: a striclty decreasing function between well-ordered sets has finite source
 *)

Definition all_big_substrate g := 
  (forall i, inc i (domain g) -> ~ (small_set (substrate (Vg g i)))).

Lemma all_big_substrate_prop  g : all_big_substrate g ->
  exists f1 f2, [/\ inc f1 (prod_of_substrates g),
   inc f2 (prod_of_substrates g) & 
   forall i, inc i (domain g) -> (Vg f1 i) <> (Vg f2 i)].
Proof.
move => ns.
pose h v x := [/\ inc (P x) v, inc (Q x) v & P x <> Q x].
pose f0 i := choose (fun z => h (substrate (Vg g i)) z).
have f0p: (forall i, inc i (domain g) -> h (substrate (Vg g i)) (f0 i)).
  move=> i idg; apply choose_pr.
  move: (ns _ idg); set t:= substrate (Vg g i) => ts.
  case:(emptyset_dichot t) => te; first by case:ts; move=> u v ue; empty_tac1 u.
  move: te=> [x xe]; case: (p_or_not_p (exists2 y, inc y t & x <> y)). 
    by move=> [y yt yx]; exists (J x y); rewrite /h; aw.
  move => ep;case: ts; move=> u v /= ut vt; transitivity x.
    by symmetry; ex_middle xu; case: ep; exists u.
  by ex_middle xv;case: ep; exists  v.
exists (Lg (domain g) (fun i=> (P (f0 i)))).
exists (Lg (domain g)(fun i => (Q (f0 i)))).
split => //.
  by apply: prod_of_substrates_gi => i /f0p [].
  by apply: prod_of_substrates_gi => i /f0p [].
by move => i idg; rewrite !LgV//; case: (f0p _ idg). 
Qed.


(** easy part: if the product is totally ordered, or well-ordered 
so is each factor. By assumption the index set is well-ordered *)
Section Exercise2_11.
Variables (r g: Set).
Hypothesis oa:  orprod_ax r g.

Lemma orprod_total2: allf g ne_substrate  ->
  ((total_order (order_prod r g) ->  (allf g  total_order))
  /\ 
  (worder (order_prod r g) -> (allf g  worder))).
Proof.
move=> alne.
move: (oa) => [wor sr pa].
pose f i t := Lg (domain g) (fun j => Yo (j = i) t (rep (substrate (Vg g j)))).
have aux:forall i t,  inc t (substrate (Vg g i)) ->
     inc (f i t) (substrate (order_prod r g)).
  move=> i t  ts;rewrite orprod_sr //. 
  rewrite /f; aw;apply /prod_of_substratesP;split => //; aww.
  by move => j jdg; rewrite LgV//; Ytac ji; [  ue | apply: rep_i; apply: alne].
have aux2: forall i t1 t2,  inc i (domain g) -> inc t1 (substrate (Vg g i)) -> 
  inc t2 (substrate (Vg g i)) -> gle (order_prod r g) (f i t1) (f i t2)
  -> gle (Vg g i) t1 t2.
  move=> i t1 t2 idg t1s t2s /(orprod_gleP oa) [_ _  h]. 
  move: (pa _ idg) => oi; case: h.
    move=> eq; move: (f_equal (Vg^~ i) eq); rewrite /f !LgV//; Ytac0; Ytac0.
    by move=> ->; order_tac.
  rewrite sr; move=> [j [jsr j1 j2]]; move: j1; rewrite /f /glt; rewrite !LgV//.
  by Ytac ji; Ytac0; rewrite ? ji; case.
split.
  move=> [or tor] i idg;move: (pa _ idg) => oi; split => //.
  move=> x y xsr ysr.
  by case: (tor _ _ (aux i _ xsr) (aux i _  ysr)) => h;
     [left | right ]; apply: aux2.
move=> [or1 wor1].
move=> i idg; move: (pa _ idg) => oi; split => //.
move=> x xsr xne.
set (X:= fun_image x (f i)).
have Xs:  (sub X (substrate  (order_prod r g))).
  by move=> t /funI_P [z zx ->];apply: aux; apply: xsr.
have neX: (nonempty X) by apply:funI_setne.
move: (wor1 _ Xs neX) => [y []]; rewrite iorder_sr// => yX yle.
move: yX => /funI_P [z zx fz]; exists z;red; rewrite iorder_sr //;split => //.
move=> t tx.
have ft: (inc (f i t) X) by apply /funI_P; ex_tac.
apply /iorder_gle0P => //.
aw; move: (yle _ ft); rewrite fz => le3; move: (iorder_gle1 le3) => le4. 
by apply: aux2 => //; apply: xsr.
Qed.

(** Assume no factor empty; then the product is totally ordered iff each factor 
is. Assume moreover that each factor has at least two elements. We can then
construct two elements in the product such that [f(i) < g(i)] for any [i].
Let [h_j] the function that is [f(i)] or [g(i)] depending on how [i] compares
to [j]; this is a stricty decreasing function; if the product is well-ordered 
it implies that the index set is empty.
*)


Lemma orprod_total3P:  allf g ne_substrate  ->
  ( (allf g total_order) <-> total_order (order_prod r g)).
Proof.
move=> alne; split; first by apply: orprod_total => //.
by case: (orprod_total2 alne).
Qed.


Lemma orprod_total4:
  total_order (order_prod r g) ->
  all_big_substrate g  ->
  exists f1 f2,
   [/\ inc f1 (substrate (order_prod r g)),
       inc f2 (substrate (order_prod r g)) &
       forall i, inc i (domain g) -> glt (Vg g i) (Vg f1 i) (Vg f2 i)].
Proof.
move=> tor ns.
move:(all_big_substrate_prop ns) => [f1 [f2 [f1s f2s cf12]]].
move/prod_of_substratesP: f1s => [_ _ f1s].
move/prod_of_substratesP: f2s => [_ _ f2s].
have alne:(allf g ne_substrate).
  by move=> i idg; move: (f1s _ idg)=> h; exists (Vg f1 i).
move/(orprod_total3P alne): tor => ror.
have f0p i: inc i (domain g) ->
            glt (Vg g i) (inf (Vg g i) (Vg f1 i) (Vg f2 i))
                (sup (Vg g i) (Vg f1 i) (Vg f2 i)). 
  move => idg.
  move:(ror _ idg) (f1s _ idg) (f2s _ idg) (cf12 _ idg) => [os tos] xsr ysr xy.
  case (tos _ _ xsr ysr) => h.
     rewrite inf_comparable1 // sup_comparable1 //.
     rewrite inf_C  sup_C inf_comparable1 // sup_comparable1 //; split; fprops.
exists (Lg (domain g) (fun i=> (inf (Vg g i) (Vg f1 i) (Vg f2 i)))).
exists (Lg (domain g) (fun i=> (sup (Vg g i) (Vg f1 i) (Vg f2 i)))).
move: (oa) => [wor sr alo].
rewrite orprod_sr; split => //.
  apply: prod_of_substrates_gi => i idg; move: (f0p _ idg) => h; order_tac.
  apply: prod_of_substrates_gi => i idg; move: (f0p _ idg) => h; order_tac.
move => i idg; rewrite !LgV//; exact: (f0p _ idg). 
Qed.

Lemma ordprod_worder_bisP:
  all_big_substrate g ->
  ( ( allf g  worder /\ finite_set (substrate r))
   <-> worder (order_prod r g)). 
Proof.
move=> ad; move: (oa) => [wor sr alo]; split.
  move=> [p1 p2]; apply: orprod_wor => //.
move=> wop.
move: (orprod_total4 (worder_total wop) ad) => [f1 [f2 [f1s f2s f12]]].
split.
  have p1: (allf g ne_substrate).
    move=> i idg; move: (f12 _ idg); exists (Vg f1 i); order_tac.
  by move: (orprod_total2 p1) => [_]; apply.
set (f := fun i =>  Lg (domain g) 
    (fun z => Yo (glt r z i) (Vg f1 z) (Vg f2 z))).
have fs: (forall i, inc i (domain g) -> inc (f i) (substrate (order_prod r g))).
  move=> i idg; rewrite orprod_sr // /f; aw.
  apply: prod_of_substrates_gi. 
  move=> j jdg; move: (f12 _ jdg)  (alo _ jdg)  =>  le2 o2.
  Ytac ca; order_tac. 
rewrite - sr in fs; apply: (worder_decreasing_finite wor wop fs).
move=> i j ij.
have isr: (inc i (substrate r)) by order_tac.
have jsr: (inc j (substrate r)) by order_tac.
have idg: (inc i (domain g)) by ue.
have jdg: (inc j (domain g)) by ue.
have aux: ~ glt r i i by case.
have aux1: glt (Vg g i) (Vg (f j) i) (Vg (f i) i).
  by rewrite /f !LgV//; Ytac0; Ytac0; apply: f12.
split; last first.
  by move: aux1 => [_ neq1]; dneg eq1; rewrite eq1.
rewrite orprod_sr // in fs.
apply /(orprod_gleP oa) ; split => //; try (apply: fs => //).
right; exists i; split => //; move=> k ki.  
have kdg: (inc k (domain g)) by rewrite - sr; order_tac.
have kj: glt r k j by move: wor => [or _];order_tac.
by rewrite /f !LgV//;  Ytac0; Ytac0.
Qed.

End Exercise2_11.


(** ---- Exercise 2.12; Study of lexciographic product.

Lemma: A subset of the union of two well-ordered sets in a totally ordered set 
is well-ordered  *)

Lemma union2_wor r A B C:
  total_order r -> sub A (substrate r) ->  sub B (substrate r) ->  
  sub C (A \cup B) ->
  worder (induced_order r A) ->worder (induced_order r B) ->
  worder (induced_order r C).
Proof.
move => [or tor] Asr Bsr cab [or1 wo1] [or2 wo2].
have cs: sub C (substrate r).
   by move => t tc;move:(cab _ tc);case /setU2_P => h; [apply: Asr| apply: Bsr].
move:(iorder_osr or Asr)(iorder_osr or Bsr)(iorder_osr or cs). 
move=>[oA sA][oB sB][oC sC].
split => //; rewrite sC => X XC neX.
rewrite  sA in wo1; rewrite sB in wo2.
have Xp: (X \cap A) \cup (X \cap B) = X. 
  by rewrite - (set_IU2r X A B); apply/ setI2id_Pl; apply: (sub_trans XC cab).
rewrite (iorder_trans _ XC). 
case: (emptyset_dichot  (X \cap A)) => ne1.
  have XB: sub X B by  rewrite -Xp ne1 set0_U2; apply:setI2_2.  
  by move:(wo2 _ XB neX); rewrite (iorder_trans _ XB).
case: (emptyset_dichot  (X \cap B)) => ne2.
  have XA: sub X A by rewrite -Xp ne2 setU2_0; apply:setI2_2.
  by move:(wo1 _ XA neX); rewrite (iorder_trans _ XA).
have pc: sub (X \cap A) A by apply: subsetI2r.
have pd: sub (X \cap B) B by apply: subsetI2r.
move: (wo1 _ pc ne1)(wo2 _ pd ne2). 
rewrite (iorder_trans _ pc) (iorder_trans _ pd).
move: (sub_trans XC cs) => qa.
move: (sub_trans pc Asr) => qb.
move: (sub_trans pd Bsr) => qc.
move => [a ap][b bp]; move: ap bp; rewrite /least ! iorder_sr//.
move => [] /setI2_P [aX aA] al [] /setI2_P  [bX bB] bl.
have [c [cX ca cb]]: exists c, [/\ inc c X,  gle r c a & gle r c b].
  case: (tor _ _ (Asr _ aA)(Bsr _ bB)) => aux.
    exists a; split => //; order_tac; exact (Asr _ aA).
    exists b; split => //; order_tac; exact (Bsr _ bB).
exists c;split => //; rewrite iorder_sr//;  move => x xX; apply /iorder_gle0P => //.
move: xX; rewrite - Xp => /setU2_P; case => h.
  move: (al _ h) => h1; move: (iorder_gle1 h1) => h2; order_tac.
move: (bl _ h) => h1; move: (iorder_gle1 h1) => h2; order_tac.
Qed.

(** Assumptions [I] is an index set, totally ordered by [r]; [E(i)] is a family 
[g] of ordered sets, and [E] is the product. If [x] and [y] are in [E] then 
[olex_nsv x y] is the set of indices on which [x] and [y] differ. We say [x<y] 
is this set is well-ordered and [x(i)<y(i)] when [i] is the least element.
*)

Definition olex_nsv r x y:=  Zo (substrate r) (fun i =>  (Vg x i <> Vg y i)).
Definition olex_io r x y:=   (induced_order r (olex_nsv r x y)).

Definition olex_comp1_r r g x y :=
  worder (olex_io r x y) /\
  let i := the_least  (olex_io r x y) in glt (Vg g i) (Vg x i) (Vg y i). 
Definition olex_comp2_r r g x y :=
  [/\ (inc x (prod_of_substrates g)),
      (inc y (prod_of_substrates g)) &
      (x = y \/ olex_comp1_r r g x y) ].

Definition olex r g := graph_on  (olex_comp2_r r g) (prod_of_substrates g).
Definition olex_ax r g:=[/\ total_order r,substrate r = domain g & order_fam g].

Lemma olex_nsvS r x y:   olex_nsv r x y = olex_nsv r y x.
Proof.
by set_extens t; move => /Zo_P [pa pb]; apply /Zo_P; split => //; apply:nesym.
Qed.

Lemma olex_ioS r x y:   olex_io r x y = olex_io r y x.
Proof. by rewrite /olex_io olex_nsvS. Qed.

(** This relation is an ordering of [E] *)
Section Olex_basic.
Variables (r g: Set).
Hypothesis ax: olex_ax r g.

Lemma olex_R x:
 inc x (prod_of_substrates g) -> olex_comp2_r r g x x.
Proof. by move => h; split => //; left. Qed.


Lemma olex_gleP x y: gle  (olex r g) x y  <->  olex_comp2_r r g x y.
Proof.
split; first by move /Zo_hi; aw. 
move =>h;apply Zo_i;last by aw.
by move: h => [pa pb _];  apply : setXp_i.
Qed.

Lemma olex_nsve x y: 
   inc x (prod_of_substrates g) -> inc y (prod_of_substrates g) ->
   ((x = y) <-> (olex_nsv r x y = emptyset)).
Proof. 
move=> px py;split.
  by move => ->; apply /set0_P=> t /Zo_P [pa]; case.
have pd: order_fam g by move: ax=> [_ _]. 
have sd: substrate r = domain g by move: ax => [_]. 
move=> oe; move: px => /prod_of_substratesP  [ra rb _].
move: py => /prod_of_substratesP  [rd re _].
apply: fgraph_exten =>//; first by ue.
by rewrite rb - sd => z zd;  ex_middle sv; empty_tac1 z; apply /Zo_P. 
Qed.


Lemma olex_nsve1 x y: 
  inc x (prod_of_substrates g) -> inc y (prod_of_substrates g) ->
  let r' := (olex_io r x y) in let i := the_least r' in 
    x <> y -> worder r' -> least r' i.
Proof. 
move => px py r' i pa pb.
have or: order r by move: ax => [[ok _]_ ].
have pc: sub  (olex_nsv r x y) (substrate r) by apply: Zo_S.
have sr': substrate r' = olex_nsv r x y by rewrite /r' iorder_sr.
have nse: nonempty (substrate r').
  by rewrite sr'; apply /nonemptyP; move /(olex_nsve px py).
move:  (worder_least pb nse) => [j jl].
move: (pb) => [qa1 _];move: (the_least_pr2 qa1 jl).
by rewrite /i; move => ->.
Qed.

Lemma olex_glt_aux x y (r' := olex_io r x y) (i := the_least r'):
  glt (olex r g) x y  ->
  (inc i (substrate r) /\ forall j, glt r j i -> Vg x j = Vg y j).
Proof.
move => [h nxy] .
move:h => /olex_gleP [pa pb]; case => pc; first by contradiction.
move: pc => [wor]; move: (olex_nsve1 pa pb nxy wor).
rewrite /= -/i; move => [pc pd] pe.
have or: order r by move: ax => [[ok _]_ ].
have pf: sub  (olex_nsv r x y) (substrate r) by apply: Zo_S.
have sr': substrate r' = olex_nsv r x y by rewrite /r' iorder_sr.
have pg: inc i (substrate r) by apply: pf; rewrite - sr'. 
split => //.
move => k ki; ex_middle aux.
have kp: inc k (substrate r') by rewrite sr' ; apply:Zo_i => //; order_tac.
move: (pd _ kp); rewrite /r' => aux1; move: (iorder_gle1 aux1) => aux2.
order_tac.
Qed.

Lemma olex_sr: substrate (olex r g) =  (prod_of_substrates g).
Proof. by  rewrite /olex graph_on_sr // => x; apply:  olex_R.   Qed.

Lemma olex_osr: order_on  (olex r g) (prod_of_substrates g).
Proof.
split => //; last by apply:olex_sr.
move: (ax) => [[or tor] _ _].
have sd: substrate r = domain g by move: ax => [_].
apply: order_from_rel; split => //; last first.
    by move => x y [pa pb _];split; apply: olex_R.
  move=> x y => pa pb; ex_middle xny; symmetry.
  have pa':  glt (olex r g) x y by split => //; apply /olex_gleP.
  move: pa pb => [pa pb pc] [_ _ pd].
  case :pc  => //; case: pd => //; rewrite /olex_comp1_r.
  move : (olex_glt_aux pa'); rewrite (olex_ioS r y x) /=.
  set i:=(the_least _).
  move => [isr _] [_ qb][_ qd].
  suff h: order (Vg g i) by order_tac.
  by move: ax => [qe qf qh];  apply: qh; rewrite -qf.
move => y x z pa pb.
case: (equal_or_not x y) => exy; first by rewrite exy.
case: (equal_or_not y z) => eyz; first by rewrite - eyz.
have ltxy:   glt (olex r g) x y by split => //; apply /olex_gleP.
have ltyz:   glt (olex r g) y z by split => //; apply /olex_gleP.
move: pa pb => [xs ys xy] [_ zs yz]; split => //.
case: (equal_or_not x z) => xz; first by left.
right;case: xy => xy; first by contradiction.
case: yz => yz; first by contradiction.
move: (olex_glt_aux ltxy)(olex_glt_aux ltyz).
move: xy yz;  rewrite /olex_comp1_r /olex_io /olex_nsv.
set Txy:= Zo _ _; set Tyz := Zo _ _; set Txz:= Zo _ _.
set Ixy:=the_least _ .
set Iyz:=the_least _ ; set Ixz:=the_least _.
move => [woxy pxy][woyz pyz][ixys hixy][iyzs hiyz].
have sxz: sub Txz (Txy \cup Tyz).
  move => i /Zo_P [isr pa]; apply /setU2_P.
   case:(equal_or_not (Vg x i) (Vg y i)) => eq; [ right |left];apply: Zo_i =>//.
   ue.
move: (ax) => [tor1 _].
have sxy: sub Txy (substrate r) by apply: Zo_S.
have syz: sub Tyz (substrate r) by apply: Zo_S.
have sxz1: sub Txz (substrate r) by apply: Zo_S.
have p1: worder (induced_order r Txz)
  by apply:  (union2_wor tor1 sxy syz sxz woxy woyz).
have or1: order (Vg g Ixy) by move: ax => [_ _]; apply; ue.
have or2: order (Vg g Iyz) by move: ax => [_ _]; apply; ue.
split => //;case: (tor _ _ ixys iyzs) => cp.
  have lta: glt (Vg g Ixy) (Vg x Ixy) (Vg z Ixy).
    case: (equal_or_not Ixy Iyz) => eq2.
      move:pyz;rewrite -eq2; move => [aux _]; order_tac.
    have lt1: glt r Ixy Iyz by split.
    rewrite - (hiyz _ lt1)//.
  have it: inc Ixy Txz. 
    apply: Zo_i; first by order_tac.
    move =>  neq; move: lta => [ _ aux]; contradiction.
  suff eq1: Ixz = Ixy by rewrite eq1.
  apply: the_least_pr2; first by move: p1 => [ok _].
  red; rewrite iorder_sr //;split => //.
  move => j jt; apply /iorder_gleP => //.
  case: ( total_order_pr2 tor1 (sxz1 _ jt) ixys) => cp1 //.
  move: (hixy _ cp1) => eq1.
  have lt1: glt r j Iyz by order_tac.
  move: (hiyz _ lt1) => eq2.
  by move: jt =>/Zo_P; rewrite eq1 eq2;move => [_].
have lta: glt (Vg g Iyz) (Vg x Iyz) (Vg z Iyz).
  case: (equal_or_not Iyz Ixy) => eq2.
    move:pxy;rewrite -eq2; move => [aux _]; order_tac.
  have lt1: glt r Iyz Ixy by split.
  rewrite  (hixy _ lt1)//.
have it: inc Iyz Txz.
  apply: Zo_i => //. 
  move =>  neq; move: lta => [ _ aux]; contradiction.
suff eq1: Ixz = Iyz by rewrite eq1.
apply: the_least_pr2; first by move: p1 => [ok _].
red; rewrite iorder_sr //;split => //.
move => j jt; apply /iorder_gleP => //.
case: ( total_order_pr2 tor1 (sxz1 _ jt) iyzs) => cp1 //.
move: (hiyz _ cp1) => eq1.
have lt1: glt r j Ixy by order_tac.
move: (hixy _ lt1) => eq2.
by move: jt => /Zo_P; rewrite eq2 eq1;move => [_]. 
Qed.

(** Assume all [E(i)] totally ordered. Then [x] and [y] are comparable
iff [olex_nsv x y] is well-ordered. We deduce that _to be comparable_ is a 
transitive relation. Let [X] be the connected component of [x] for
_to be comparable_. This set is thus totally ordered.
 *)
Lemma olex_cc_comparable1  (r':= olex r g):
  (allf g total_order) ->
  forall x y,
      ocomparable r' x y <-> [/\ inc x (substrate r'), inc y (substrate r') &
          worder (olex_io r x y)].
Proof.
move: olex_osr => [or' sr].
have or: order r by  move: ax => [[ ok _] _].
have aux: forall t, worder (olex_io r t t).
  move => t; rewrite /olex_io /olex_nsv.
  set Z := Zo _ _; have -> : Z = emptyset.
    by apply /set0_P => z /Zo_hi.
   have aux1: sub emptyset (substrate r) by fprops.
   move: (iorder_osr or aux1) => [pa pb].
   split => //; rewrite pb => x xe [y yx]; move: (xe _ yx);case; case.
move=> h x y.
rewrite sr; split.
  case; move /olex_gleP => [pa pb pc]; split => //; case: pc => pc.
  - rewrite pc; apply: aux.
  - by move: pc => [wo _].
  - rewrite pc; apply: aux. 
  - by rewrite olex_ioS; move: pc => [wo _].
move=> [xp yp wot]. 
case: (equal_or_not x y) => xy.
   by left; rewrite xy; apply  /olex_gleP => //;apply: olex_R.
move: (olex_nsve1 xp yp xy wot).
move: (olex_ioS r y x) => ppa.
set i := (the_least _); move => [pa pb].
have pc: sub  (olex_nsv r x y) (substrate r) by apply: Zo_S.
have sd: substrate r = domain g by move: ax => [_].
have sr': substrate (olex_io r x y) = olex_nsv r x y 
  by rewrite iorder_sr.
have nsv: Vg x i <> Vg y i.
  by move: pa; rewrite sr' => /Zo_hi.
have nsv': Vg y i <> Vg x i by apply:nesym.
have pg: inc i (domain g) by rewrite - sd; apply: pc; rewrite - sr'. 
move: (h _ pg) => [ori tori].
have pd: order_fam g by move: ax=> [_ _]. 
have px: inc (Vg x i) (substrate (Vg g i)).
  by  move: xp => /prod_of_substratesP [_ _]; apply.
have py: inc (Vg y i) (substrate (Vg g i)).
  by move: yp => /prod_of_substratesP [_ _ ]; apply.
case: (tori _ _ px py) => cp;[left | right ]. 
  by apply /olex_gleP;split => //;right.
by apply /olex_gleP;split => //; right; split => //; rewrite ppa.
Qed.


Lemma olex_cc_comparable2  (r':= olex r g):
  (allf g total_order)  -> transitive_r (ocomparable r').
Proof.
move=> h y x z; rewrite ! (olex_cc_comparable1 h).
move=> [xE yE wo1] [_ zE wo2]; split => //.
move: wo1 wo2; rewrite /olex_io.
apply: union2_wor.
- by move: ax => [ok _].
- apply: Zo_S.
- apply: Zo_S.
- rewrite /olex_nsv => t /Zo_P [pa pb].
  case: (equal_or_not (Vg x t) (Vg y t)) => sv.
  apply /setU2_P; right; apply /Zo_P;split => //; ue.
  by apply /setU2_P; left; apply /Zo_P.
Qed.


Lemma olex_cc_tor  (r':= olex r g):
  (allf g total_order) -> 
  forall x, inc x (substrate r') -> 
   total_order (induced_order r' 
        (connected_comp (ocomparable r') (substrate r') x)).
Proof.
move:  olex_osr => [or' sr] h.
set E :=(substrate r'); set c := ocomparable r'.
have pa: reflexive_re c E.
  rewrite /E /r' sr.
  move => y;split.
    by move => yE; left; apply /olex_gleP; apply: olex_R.
   by case; move /olex_gleP => [ok _].
have pb: symmetric_r c by move =>  a b /=; case; [right | left].
have pc: (forall x y, c x y -> inc x E).
  rewrite /c /ocomparable /E; move => x y; case=> auxl; order_tac.
move => x xE; rewrite - (connected_comp_class pa pb pc xE).
case: (chain_equivalence_eq pa pb pc).
set Sg := chain_equivalence c E; move => es ss.
move:(sub_class_substrate es (x:=x)); rewrite ss => pd.
move: (iorder_osr or' pd) => [pa1 pb1].
split => //;rewrite pb1 => a b ac bc.
suff: c a b by  case => h1; [ left | right]; apply /iorder_gleP.
have: related Sg a b.
  move: ac bc => /(class_P es) s1 /(class_P es) s2. 
  have s3: related Sg a x by equiv_tac.
  equiv_tac.
move/graph_on_P1 => [_ _ [xc [cc <- <-] ]] {a b ac bc}.
elim: xc cc; first by  move=> a b //.  
move=> u xc Hrec; simpl; move => [cuh cc]; move: (Hrec cc) => c1.
apply: ((olex_cc_comparable2 h) _ _ _ cuh c1).
Qed.

(** Assume the index set well-ordered. Then [olex] is just the lexicographic 
product. We know that if each factor is totally ordered, then the product is 
totally ordered. Conversely, if the product  [olex] is totally ordered, and 
each factor has at least 2 elements, then the index set is well-ordered (since
the index set is some  [olex_nsv x y]) and  each factor is total 
*)
Lemma olex_lex: worder r -> olex r g = order_prod r g.
Proof.
have pd: order_fam g by move: ax=> [_ _]. 
move => h.
have pc:orprod_ax r g by move: ax => [pa pb pc]. 
move: olex_osr => [o1 sr1].
move: (orprod_osr pc) => [o2 sr2].
have ss: substrate (order_prod r g) = substrate  (olex r g) by ue.
apply/order_exten =>// => x y.
case: (equal_or_not x y) => exy.
  rewrite exy; split => pa; order_tac.
   rewrite ss; order_tac.
  rewrite - ss; order_tac.
have sd: substrate r = domain g by move: ax => [_].
have wor: worder (olex_io r x y).
  apply: induced_wor => //; apply: Zo_S.
split.
  move /(olex_gleP) => [xp yp aux]; apply /(orprod_gle1P pc);split => //.
  set io := induced_order _ _.
  have ->: io = (olex_io r x y) by rewrite /io - sd.
  case: aux; first by contradiction.
  move:(olex_nsve1 xp yp exy wor) => lp.
  move: wor => [or _ ] [_ h1] j pb; by rewrite -(unique_least or lp pb).
move /(orprod_gle1P pc) => [xp yp pe]; apply (olex_gleP); split => //.
move:(olex_nsve1 xp yp exy wor) => lp.
right; split => //; apply: pe; rewrite - sd //. 
Qed.


Lemma olex_total1: worder r -> (allf g total_order)  -> total_order (olex r g).
Proof.
move => wo alto; rewrite olex_lex //; apply orprod_total => //.
by move: ax => [pa pb pc].
Qed.


Lemma olex_total2: 
  total_order (olex r g) ->
  all_big_substrate g ->
  (worder r /\ (allf g total_order)).
Proof.
move=> pa pb.
have pd: order_fam g by move: ax=> [_ _]. 
move: (proj2 olex_osr) => sr.
move: (all_big_substrate_prop  pb) =>[x [y [xsr ysr xney]]].
move/prod_of_substratesP: (xsr) => [_ _ aux].
move:(xsr)(ysr); rewrite - sr => xsr1 ysr1.
have alne:(allf g ne_substrate).
  by move=> i idg; move: (aux _ idg)=> h; exists (Vg x i).
have sd: substrate r = domain g by move: ax => [_].
have zp:olex_nsv r x y = domain g.
  rewrite /olex_nsv sd; set_extens w; first by move => /Zo_P [].
  by move => wg; apply: Zo_i => //; apply: xney.  
have or: order r by  move: ax => [[or _] _].
case: (equal_or_not x y)=> exy.
  move: exy;rewrite  (olex_nsve xsr ysr) zp => exy.
  split; last by move => t; rewrite exy; case; case.
  split => //; move=> X Xsr [z zX]; move: (Xsr _ zX) => au; empty_tac1 z; ue.
have au: r = (olex_io r x y).
  rewrite /olex_io zp - sd iorder_substrate //.
have wor: worder r.
  move: pa => [or1 tor]; case: (tor _ _ xsr1 ysr1) =>/olex_gleP.
    move=> [_ _ ]; case; [ done | move=> []; ue].
  move=> [_ _];case; first  by move => xy; case: exy. 
  move => [h _];  by rewrite au  olex_ioS.
split =>//.
move: pa; rewrite (olex_lex wor).
have pc:orprod_ax r g by move: ax => [qa qb qc].
move: (orprod_total2 pc alne) => [pe _]; exact pe.
Qed.

End Olex_basic.


(** ---- Exercises 13, 14, 15, 16, 17, 18, 20 are proved in the main text.
The following are needed for Exercise 19.
*)

(** Exercise 4.1. Let [p(E,F)] be the property that the emptyset is in [F], 
  and adding one element of [E] to an element of [F] gives an element of [F].
  The set of finite subset of [E] is the least [F] satisfying this property.
  We deduce: the union of two finite sets is finite, the powerset of a finite 
  set is finite.
*)

Definition finite_subsets E := Zo(\Po E) finite_set.

Definition finite_subsets_prop E F:=
  inc emptyset  F /\ forall x X, inc x E -> inc X F -> inc (X +s1 x) F.

Lemma finite_subsets_pr E:
  finite_subsets_prop E (finite_subsets E) /\
  (forall F, finite_subsets_prop E F -> sub (finite_subsets E) F).
Proof. 
split.
  rewrite /finite_subsets;split. 
    apply: Zo_i; first by apply /setP_P; fprops. 
    apply: emptyset_finite. 
  move=> x X xE => /Zo_P [] /setP_P XE fX; apply /Zo_i.
     by apply /setP_P; apply :setU1_sub.
  by apply:  setU1_finite. 
rewrite /finite_subsets=> F [eF fs] t.
move =>/Zo_P [] /setP_P tE fst.
apply: (@finite_set_induction1  (fun x=> sub x E)(fun x=> inc x F)) =>//.
move => a b h1 h2. 
apply: fs; first by apply: h2;fprops.
apply: h1; apply: (@sub_trans  (a +s1 b)) => //;fprops.
Qed.

Lemma finite_union2 x y: finite_set x -> finite_set y ->
  finite_set (x \cup y).
Proof.
move=> fsx fsy.
set (E:=x \cup y). 
set (t:= Zo (\Po E) (fun a=> finite_set (x \cup a))).
suff: (inc y t) by move /Zo_P; rewrite -/E; case.
have yf:inc y (finite_subsets E). 
  apply: Zo_i => //; apply /setP_P => s su; rewrite/E; fprops.
suff h: (finite_subsets_prop E t).
  by move: (finite_subsets_pr E) => [h1 h2];  apply: (h2 _ h).   
split.
    rewrite /t; apply: Zo_i; first by apply /setP_P; fprops. 
    by rewrite setU2_0. 
move=> z X zE => /Zo_P [] /setP_P XE fsu; apply: Zo_i.
  by apply /setP_P; apply : setU1_sub.
by rewrite setU2_A; apply: setU1_finite.
Qed. 

Lemma finite_powerset x:
  finite_set x -> finite_set (\Po x).
Proof. 
move=> fsx.
set (t:= Zo (\Po x) (fun a=> finite_set (\Po a))).
suff fspt: (finite_subsets_prop x t). 
  move: (finite_subsets_pr x)=> [p1 p2].  
  move: (p2 _ fspt) => aux. 
  have:(inc x t).
    apply: aux; apply: Zo_i =>//;apply: setP_Ti.
  by move /Zo_P; case.
split.
  rewrite /t; apply: Zo_i; first by apply /setP_P;fprops. 
  rewrite setP_0; apply: set1_finite. 
move=> z X zx =>/Zo_P [] /setP_P Xx fspX; apply: Zo_i.
   by apply /setP_P; apply setU1_sub.
case: (inc_or_not z X); first by  move => zX; rewrite setU1_eq.
move=> nzX.
set (w:= fun_image (\Po X) (fun t => t +s1 z)).
have eq: (equipotent (\Po X) w).
  set (f:= Lf  (fun t => t +s1 z) (\Po X) w).
  have ta: (lf_axiom  (fun t => t +s1 z) (\Po X) w). 
    move=> u => uX; apply /funI_P; exists u => //.
  have ff: (function f) by rewrite /f;apply: lf_function. 
  exists f; split.  
    split;rewrite /f.
      apply: lf_injective=>//; move => u v /setP_P uX /setP_P vX sv.
      set_extens x1 => xs.
        have: (inc x1 (u +s1 z)) by fprops. 
        rewrite sv; case /setU1_P=>//; move=> h; case: nzX; apply:  uX; ue. 
      have: (inc x1 (v +s1 z)) by fprops. 
      rewrite - sv; case /setU1_P=>//; move=> h; case: nzX; apply:  vX; ue. 
    apply: lf_surjective=>//. 
    by move=> y => /funI_P.
  by rewrite /f; aw. 
  by rewrite /f; aw. 
have ->: (\Po (X +s1 z)=  (\Po X) \cup w).
  set_extens u. 
    move /setP_P => sut; apply /setU2_P.
    case: (inc_or_not z u) => h.
      right;apply /funI_P; exists (X \cap u).
        apply /setP_P => //; apply: subsetI2l. 
      set_extens v.
        move => vu; move: (sut _ vu); case /setU1_P; last by move => ->; fprops.
        move => vx;apply /setU1_P; left; fprops.
      by case /setU1_P; [ move =>/setI2_P [] | move => -> ].
    left; apply /setP_P;move=> v vu; move: (sut _ vu); case /setU1_P => //.
    move=> vz; case: h; ue.
  case /setU2_P.
    move => /setP_P h; apply /setP_P => v vu; fprops.
  move => /funI_P [x1 wX ->]; apply /setP_P => v; case /setU1_P => h.
    by apply /setU1_P; left;  move/setP_P: wX; apply.
  rewrite h; fprops.
apply: finite_union2=>//.  
have aux: (cardinal (\Po X) = cardinal w) by apply /card_eqP.
by red; rewrite -aux. 
Qed.


(** ---- Exercise 4.3. *)
Lemma well_ordered_opposite r:
  worder r -> worder (opp_order r) -> finite_set (substrate r).
Proof.
move=> wor [ors wos].
move: (wor) => [or _].
set Z := Zo (substrate r) (fun x => (finite_set (segment r x))).
have sZ1: sub Z (substrate r) by apply: Zo_S.
move:(opp_osr or) => [pa pb].
have sZ: sub Z (substrate (opp_order r)) by rewrite pb.
case: (emptyset_dichot (substrate r)) => sre.
  rewrite sre; apply: emptyset_finite.
have neZ: nonempty Z.
   move: (worder_has_empty_seg wor sre) => [x xE sxe].
   exists x; apply: Zo_i =>//.
   rewrite sxe; apply: emptyset_finite.
move: (wos _ sZ neZ)=> [x []]; rewrite iorder_sr// =>xz.
move:(xz) => /Zo_P [x1 x2] x3.
set s:= segmentc r x.
have fs: finite_set s by rewrite /s - (segmentc_pr or x1); apply: setU1_finite.
case: (well_ordered_segment wor (segmentc_segment x  or)); first by move <-.
move=> [y ysr ss]. 
have yz: inc y Z by  apply: Zo_i =>//; ue.
move: (inc_bound_segmentc or x1); rewrite ss; move /segmentP => le1.
move: (iorder_gle1 (x3 _ yz)) => /opp_gleP => yx; order_tac.
Qed.

(** ---- Exercise 2.19: Ordinal powers as sets of functions. 

We consider two well-ordered sets [r] and [r'] on [E] and [F]. Let [olexp_g]
(in short [g]) be the constant functional graph that maps any element of [F] to 
[r]. This is a family of orders. We can consider the product [EF] of the 
substrates of these orders;  it is the set of functional graphs [F -> E]
We apply to [g] and the opposite ordering of [r'] the results of Exercise 2.13.
This gives an ordering [olexp'] on a subset of [EF].

If [F] is finite, this gives an ordering on [EF]; but if [F] is infinite and 
[E] has at least two elements, this is not a well-ordering, thus cannot be the
ordinal power of [r] and [r'].

If [f] is in [EF], we denote by [olexp_Ie] the set of indices [i] such that 
[f i] is not the least element of [E], and we consider the set [G] of
those [f] for which [olexp_Ie] is finite. Note that, if [F] is empty, there is 
no index [i], and otherwise, there is some [i], thus some [f i] so that [E] is 
non-empty, and has a least element. Restricting the ordering to [G] gives
an ordereing [olexp]. 
*)

Section OlexPowBasic.
Variables (r r': Set).
Hypotheses (wor: worder r) (wor':worder r').
Definition olexp_lE := the_least r.
Definition olexp_g := cst_graph (substrate r') r.
Definition olexp' := olex (opp_order r') olexp_g.

(** We start with some easy results. The most important one says that if 
[x] and [y] are in [G], then [x<y] if and only if there is an index [i] 
such that [x(i)<y(i)] and if [i<j] then [x(j)=y(j)].  This is because a finite 
subset of a well-ordered set is is well-ordered for the opposite ordering.
We deduce that  [x<y] is a total ordering on [G] *)

Lemma olexp_ax: olex_ax (opp_order r') olexp_g.
Proof.
have or': order r' by move: wor' => [ok _].
split => //.
    by apply total_order_opposite; apply worder_total.
  by rewrite (proj2 (opp_osr or'))  /olexp_g /cst_graph; aw.
by rewrite /olexp_g; hnf;aw;move => x xsr; rewrite LgV//; move: wor => [or _].
Qed.

Lemma olexp'_osr: 
  order_on olexp' (gfunctions (substrate r') (substrate r)).
Proof.
move:(olex_osr (olexp_ax)); congr (order_on _ _).
rewrite  /prod_of_substrates /fam_of_substrates.
rewrite - cst_graph_pr  /olexp_g /cst_graph; aw;apply: f_equal.
apply: Lg_exten => // i isr; rewrite LgV//.
Qed.

Lemma olexp_gleh x y:
 (induced_order (opp_order r') (olex_nsv r' x y)) =
  olex_io (opp_order r')  x y.
Proof.
have or': order r' by move: wor' => [ok _].
have pa: (olex_nsv (opp_order r') x y) = (olex_nsv r' x y).
  by rewrite /olex_nsv (proj2 (opp_osr or')).
rewrite /olex_io pa //.
Qed.

Lemma olexp'_gleP x y:
  gle olexp' x y <->
  [/\ inc x (gfunctions (substrate r') (substrate r)),
     inc y (gfunctions (substrate r') (substrate r)) &
     (x = y \/ 
     let T := olex_nsv r' x y in
     let r'' := induced_order (opp_order r') T in
       worder r'' /\
       let i := the_least r'' in glt r (Vg x i) (Vg y i))]. 
Proof.
set EF:= (prod_of_substrates olexp_g).
apply: (iff_trans (olex_gleP _ _ _ _)).
have ->: (gfunctions (substrate r') (substrate r)) = EF.
  by rewrite  - (proj2 (olexp'_osr )) olex_sr.
case: (equal_or_not x y) => exy.
  split;  move => [pa pb pc];split => //; by left. 
have or': order r' by move: wor' => [ok _].
rewrite /olex_comp2_r /olex_comp1_r olexp_gleh.
set q := (the_least (olex_io (opp_order r') x y)).
move: (opp_osr or') => [oro sro].
have aux: inc x EF -> inc y EF -> 
  worder (olex_io (opp_order r') x y) ->
   (Vg olexp_g q) = r.
  move => xe ye h; rewrite /olexp_g /cst_graph LgV//.
  move: (olex_nsve1 olexp_ax xe ye exy h); rewrite -/q; move => [pc _].
  move: pc; rewrite  iorder_sr //; last by apply: Zo_S.
  by move => /Zo_P []; rewrite sro.
split; move=> [xE yE]; case => haux; split => //; right; move: haux;
  move => [wo1]; rewrite aux //.
Qed.

Definition olexp_I x := Zo (substrate r') (fun i => (Vg x i <> olexp_lE)).
Definition olexp_G:= Zo (gfunctions (substrate r') (substrate r))
  (fun x => finite_set (olexp_I x)).

Lemma olexp_lEp: nonempty (substrate r) ->
  (inc olexp_lE (substrate r)  
  /\ (forall x, inc x (substrate r) -> gle r olexp_lE x)).
Proof.
have or: order r by move: wor => [or _].
move => ne; move: (the_least_pr or (worder_least wor ne)).
by rewrite -/olexp_lE; move=> [pa pb].
Qed.

Lemma olexp_Gs: sub olexp_G (substrate olexp').
Proof. by rewrite (proj2 olexp'_osr); apply: Zo_S. Qed.

Lemma olexp_Gxy x y: inc x olexp_G -> inc y olexp_G ->
  finite_set (olex_nsv (opp_order r') x y).
Proof.
move =>/Zo_P [pa pb]  /Zo_P [pd pe].
have or': order r' by move: wor' => [ok _].
have pc: sub (olex_nsv (opp_order r') x y) ((olexp_I x) \cup (olexp_I y)).
  rewrite /olex_nsv /olexp_I => t /Zo_P; rewrite (proj2 (opp_osr or'))//. 
  move => [pc h]; case: (equal_or_not (Vg y t) olexp_lE) => eq1;
  apply /setU2_P;[left | right]; apply : Zo_i => //; ue. 
by apply: (sub_finite_set pc); apply /finite_union2.
Qed.

Lemma olexp_Gxy1 x y: inc x olexp_G -> inc y olexp_G ->
  worder (olex_io (opp_order r') x y).
Proof.
move=> pa pb; move: (olexp_Gxy pa pb) => fs.
have h:sub (olex_nsv (opp_order r') x y) (substrate (opp_order r'))
  by apply: Zo_S.
apply: finite_set_torder_wor.
  apply: total_order_sub => //.
  by apply: total_order_opposite; apply worder_total.
rewrite iorder_sr //.
by move: wor' =>[or' _]; apply: (proj1 (opp_osr or')).
Qed.

Lemma olexp_gle1P x y: inc x olexp_G -> inc y olexp_G ->
  (gle olexp' x y <->
   ( x = y \/ 
     (exists j,  
        [/\ inc j (substrate r'),
            glt r (Vg x j) (Vg y j) &
            forall i, glt r' j i -> Vg x i = Vg y i]))).
Proof.
move: (wor')  => [or' _] xG yG.
move: (opp_osr or') => [or ssr].
move: (olexp_Gs xG) (olexp_Gs yG); set EF:= substrate olexp' => xE yE.
have xe: inc x (prod_of_substrates olexp_g).
  by move: xE; rewrite /EF olex_sr.
have ye: inc y (prod_of_substrates olexp_g).
  by move: yE; rewrite /EF olex_sr.
apply: (iff_trans (olexp'_gleP _ _)).
have ->: (gfunctions (substrate r') (substrate r)) = EF.
  by rewrite /EF (proj2 olexp'_osr).
simpl; rewrite olexp_gleh.
have hc:sub (olex_nsv (opp_order r') x y) (substrate (opp_order r'))
  by apply: Zo_S.
have hd: (substrate (olex_io (opp_order r') x y))
       = olex_nsv (opp_order r') x y.
     rewrite /olex_io iorder_sr //.
case: (equal_or_not x y) => xy; first by (split  => _; [| split => //]; left).
move: ( olexp_Gxy1 xG yG) => pa.
move: (olex_nsve1 olexp_ax xe ye xy pa).
set j := the_least _ => jp.
split.
  move => [_ _]; case; first (by left);  move => [ha hb]; right.
  move: jp => []; rewrite hd => ja jb; exists j.
  move: ja => /Zo_P; rewrite  ssr; move=> [jc jd].
  split => // => i ij; ex_middle nsv.
  have pc:  inc i (olex_nsv (opp_order r') x y).
      apply: Zo_i => //; rewrite ssr; order_tac.
  move: (jb _ pc)=> pc1; move:(iorder_gle1 pc1).
  move /opp_gleP =>  aux; order_tac.
case; first by move => aux; contradiction.
move=> [j0 [jsr jv ij]];split => //; right; split => //.
have oi: order  (olex_io (opp_order r') x y) by move: pa => [].
suff jl: least (olex_io (opp_order r') x y) j0.
  by rewrite - (unique_least oi jl jp).
have jsr1: inc j0 (olex_nsv (opp_order r') x y).
  by apply: Zo_i; rewrite ? ssr //; move: jv => [].
red; rewrite hd; split => //.
move=> k kp; move: (kp) => /Zo_P;rewrite  ssr; move => [ksr sk].
rewrite /olex_io;aw;move: (worder_total  wor') => tor.
case: (total_order_pr2 tor jsr ksr) => lt1.
   move: (ij _ lt1) => eq1; contradiction. 
by apply/iorder_gle0P => //; apply/opp_gleP.
Qed.

Definition olexp := induced_order olexp'  olexp_G.

Lemma olexp_osr: order_on  olexp olexp_G.
Proof. 
apply: iorder_osr; [apply: (proj1 olexp'_osr) | apply: olexp_Gs].
Qed.


Lemma olexp_gleP x y:
 gle olexp x y <-> [/\ inc x olexp_G, inc y olexp_G &  
     ( x = y \/ 
     (exists j,  
        [/\ inc j (substrate r'),
            glt r (Vg x j) (Vg y j) &
            forall i, glt r' j i -> Vg x i = Vg y i]))].
Proof.
split.
  by move => /iorder_gleP [pa pb pc];split => //; apply /olexp_gle1P.
by move => [pa pb pc]; apply  /iorder_gleP;split => //;apply /olexp_gle1P. 
Qed.

Lemma olexp_total: total_order olexp.
Proof.
move: olexp_osr => [oo so]; split => //.
have atg: (allf olexp_g total_order).
  by rewrite /olexp_g/cst_graph; red; aw => i isr; rewrite LgV//; apply: worder_total. 
move: (olex_cc_comparable1 olexp_ax atg) => pa.
rewrite -/olexp' in pa.
move=> x y xE yE.
have xe: inc x (prod_of_substrates olexp_g).
   move: xE; rewrite so  => xe; move: (olexp_Gs xe).
   rewrite - (olex_sr (opp_order r')) //.
have ye: inc y (prod_of_substrates olexp_g).
   move: yE; rewrite so  => ye; move: (olexp_Gs ye).
   rewrite - (olex_sr (opp_order r')) //.
move: xE yE; rewrite so  => xsr ysr.
move: (olexp_Gxy1 xsr ysr) => wor''.
have: (gle olexp' x y \/ gle olexp' y x).
  by move: (pa x y); rewrite /ocomparable; move => ->; rewrite /olexp' olex_sr.
by case => h; [left | right ]; apply /iorder_gleP.
Qed.


(** If [F] is empty, then [G] is a singleton; if [F] is non-empty and [E] is 
empty then [G] is empty; if [E] is non-empty, then [G] has a least element [m].
The connected component (for _to be comparable_) of [m] is [G]. Proof: 
if [g] is in [G] let [(x1, x2, ..., xn)] be the list of indices [i] for which 
[g(i)] is not the least element. Let [gk] be like [g], but it maps 
[(x1, x2, ..., xk)] to the least element. Then [g0] is [g], [gn] is [m] and each
[gk] is comparable to [gk+1]. 
*)

Lemma olex_Fe: (substrate r' = emptyset) ->  singletonp olexp_G.
Proof.
move => h; exists emptyset; apply: set1_pr.
  apply: Zo_i. 
     apply /gfunctions_P1;split;fprops.
   apply fgraph_set0. 
   by rewrite domain_set0.
  suff:  (olexp_I emptyset = emptyset) by move => ->; apply: emptyset_finite.
  by apply/set0_P => t /Zo_P; rewrite h; move=> [/in_set0].
by move => z /Zo_P [] /gfunctions_P1 [_]; rewrite h;move /domain_set0_P.
Qed.

Lemma olex_nFe_Ee: 
  (substrate r' <> emptyset) -> (substrate r = emptyset) ->  olexp_G = emptyset.
Proof.
move=> h1 h2; apply /set0_P => y /Zo_P []  /gfunctions_P1 [_ pa].
by rewrite h2 setX_0r => ye;case: h1;rewrite - pa; apply/domain_set0_P /sub_set0.
Qed.

Lemma olexp_G_least 
  (m:= cst_graph (substrate r') olexp_lE):
  nonempty (substrate r) -> least olexp m.
Proof.
move=> nsr.
have mp: inc m (substrate olexp).
  rewrite (proj2 olexp_osr); apply: Zo_i.
    move: (olexp_lEp nsr) => [pc _].
    apply /gfunctions_P2; rewrite /m /cst_graph; split;aww.
    by move=> u /Lg_range_P [b bsr ->].
  have ->: olexp_I m = emptyset. 
    apply /set0_P => t /Zo_P [pa pb]; case: pb.
    rewrite /m /cst_graph LgV//.
  apply: emptyset_finite.
split => // x xsr.
move: olexp_total => tor; case: (total_order_pr2 tor xsr mp) => cp //.
move: cp => [] /olexp_gleP [pa pb pc] xm.
case: pc; first by contradiction.
move=> [j [jsr cp1 _]]; move: cp1; rewrite /m /cst_graph LgV// => lt1.
have or: order r by move: wor => [].
have vsr: inc (Vg x j) (substrate r) by order_tac.
move: (olexp_lEp nsr) => [_ h]; move: (h _ vsr) => le1; order_tac.
Qed.

Lemma olex_G_cc
  (m:= cst_graph (substrate r') olexp_lE)
  (comp:= ocomparable olexp')
  (G := (connected_comp comp (substrate olexp') m)) :
  nonempty (substrate r) ->
  olexp_G = G.
Proof.
move=> nsr.
move: (olexp_G_least nsr) => []; rewrite -/m (proj2 olexp_osr) => qa qb.
set_extens t.
  move=> tG; move: (olexp_Gs tG) => ts.
  move: (qb _ tG) => le1; move: (iorder_gle1 le1) => le2.
  have cmt: comp m t by left.
  move: tG => /Zo_P [pa pb].
  rewrite /G; apply setI_i.
     exists (substrate olexp');  apply: Zo_i.
         apply: Zo_i; [ aw;fprops |by  move=> a b _  /setC_P []].
       apply :setP_Ti.
     by apply: olexp_Gs.
  move=> y => /Zo_P [] /Zo_P [pc pd] pe.
  case: (inc_or_not t y) => nty //.
  have pf: inc t  ((substrate olexp') -s  y) by apply /setC_P.
  move: (pd _ _ pe pf) => bad; contradiction.
have or': order olexp' by apply: (proj1 olexp'_osr).
set E :=(substrate olexp').
have pb: symmetric_r comp by move =>  a b /=; case;[right | left].
have pc: (forall x y : Set, comp x y -> inc x E).
  rewrite /comp /E; move => x y; case=> auxl; order_tac.
have pa: reflexive_re comp E.
   move => y; split; last by apply: pc.
   by move => yE; left; order_tac.
have mE:  inc m E by apply: (olexp_Gs qa).
rewrite /G - (connected_comp_class pa pb pc mE).
case: (chain_equivalence_eq pa pb pc).
set Sg := chain_equivalence comp E; move => es ss.
move /(class_P es) => /graph_on_P1 [_ _ [c [cc]]].
suff haux: forall a b, comp a b -> inc a olexp_G -> inc b olexp_G.
  move=> h; move <-; move: qa; rewrite -h; clear h.
  move: cc;elim: c => // b c /=.
  move => hrec [pd pe] bG; move: (haux _ _ pd bG); apply: (hrec  pe). 
move => a b cab.
case: (equal_or_not a b) => ab; first by rewrite ab.
set T := olex_nsv r' a b.
set S:= (gfunctions (substrate r') (substrate r)).
set  r'' := induced_order (opp_order r') T.
have [ais [bis wor'']]: inc a S /\ inc b S /\ worder r''.
  move: cab;case; move /olexp'_gleP; move=> [ra rb rc]; split => //.
    by case: rc => //=; case.
  case: rc; first  by move=> ba; case: ab.  
  by simpl;rewrite olex_nsvS -/r''; case.
move /Zo_P => [pe pf]; apply: Zo_i => //.
have pg: sub (olexp_I b)  ((olexp_I a) \cup T).
  move => z /Zo_P [ph h]; apply /setU2_P.
  case: (equal_or_not (Vg a z) olexp_lE) => eq1; last by left; apply /Zo_P.
  by right; apply: Zo_i => //; rewrite eq1; apply:nesym.
apply: (sub_finite_set pg); apply: finite_union2 => //.
move: (wor') => [or1 _].
have Ts: sub T (substrate r') by apply: Zo_S.
move: (wor'') => [sa _]; move: (opp_osr sa) => [xa xb].
move: (opp_osr or1) => [ya yb].
have o2: opp_order r'' = induced_order r' T.
   move: (iorder_osr or1 Ts) => [ob sob].
   apply (order_exten xa ob) => x y; split.
     move /opp_gleP /iorder_gleP => [ta tb] /opp_gleP tc.
     by apply /iorder_gleP.
   move /iorder_gleP =>[ta tb tc]; apply /opp_gleP /iorder_gleP.
   by split => //; apply /opp_gleP.
have wo2: worder (opp_order r''). 
  by rewrite o2; apply: induced_wor => //; apply: Zo_S.
move: (well_ordered_opposite wor'' wo2).
rewrite /r'' iorder_sr//; fprops; ue.
Qed. 

(** We have a well-ordering. Proof by contradiction. Consider a non-empty set [X]
that has no least element. We construct by induction a sequence [(Yn, An)], 
where [Yn] is a subset of [X] and [An] a subset of [F], 
and show that is leads to a contradiction. 

We assume that [Y] and [A] satisfy some conditions, and we construct [Y'] and 
[A']. Initially [Y] is [X] and [A] is empty. 

We assume [(Pa)]: that [Y] is a non-empty subset of [X] such that 
if [x] in [Y] and [y] is in [X-Y] then [x<y]. 
We assume [(Pb2)]: If [x] and [y] are in [Y], they take the same value on [A]
We assume [(Pb3)]; for any [x] in [Y], if [x(i)] is not the least element of [E]
then either [i] is in [A] or [i] is a strict lower bound of [A].

We construct the following objects. For [x] in [Y], 
let [Ja x] be the set of of indices [i] of [x] such that [x(i)] is not the 
least element of [E], and [i] is not in [A]; let [Ma x] be the greatest
element of this set; this is an element of [F].
Note: [(Pa)] says that [Y] cannot have a least element. It follows that 
[Ja x] is non-empty, thus it has a greatest element 
(since it is finite and [F] is well-ordered).

Let [ra] be the set of all [Ma x] for [x] in [Y], and  [Aa] its least element 
(this in in [F]).
Let [Ba] be the set of all [z] in [Y] such that [Ma z = Aa].
Let [Ca] be the set of all [z(Aa)] for [z] in [Ba], and [Da] its least element
(this is in [F]). 

We take [Y'] to be the set of all [z] in [Ba] such that [z(Aa) = Da], 
and [A'] is [tack_on A Aa]. *)
Lemma olexp_worder: worder olexp.
Proof.
move: olexp_osr => [qa sa]; split => //.
rewrite sa => X Xr neX.
ex_middle not_least.
have qb: sub X (substrate olexp) by rewrite sa.
pose Pa Y:= [/\ sub Y X, nonempty Y &
    (forall x y, inc x Y -> inc y (X -s Y) -> glt olexp x y)].
have pa1: forall Y, Pa Y -> forall z, ~least (induced_order olexp Y) z.
  move => Y [pa pb pc] z => pd; case: not_least; exists z.
  move: pd; rewrite /least iorder_sr// ; last by apply: (sub_trans pa qb).
  move => [pd pe]; have zX: inc z X by apply: pa.
  rewrite iorder_sr //.
  split => //;move=> x xX; apply/iorder_gle0P => //;case: (inc_or_not x Y) => xY.
    move: (pe _ xY) => pf; apply: (iorder_gle1 pf).
  have xc: inc x (X -s Y) by apply /setC_P.
  by move: (pc _ _ pd xc) => [ok _].
pose Ja x A := (olexp_I x) -s A.
pose Ma x A := the_greatest (induced_order r' (Ja x A)).
have or': order r' by move: wor' => [].
have or: order r by move: wor => [].
have pa2:  forall x A, inc x X ->  sub (Ja x A) (substrate r').
  move => x A xX.
  have s1: sub (Ja x A) (olexp_I x) by  rewrite /Ja; move=> t /setC_P []. 
  apply: (sub_trans s1); apply: Zo_S.
have pa3: forall x A, inc x X -> nonempty (Ja x A) ->
    greatest (induced_order r' (Ja x A)) (Ma x A).
  move => x A xX neA.
  have s1: sub (Ja x A) (olexp_I x) by  rewrite /Ja;  move=> t /setC_P []. 
  move: (Xr _ xX) => /Zo_P [_ fs2].
  have fs: finite_set (Ja x A) by apply (sub_finite_set s1 fs2).
  have j1: sub (Ja x A) (substrate r') by apply: (pa2 _ _ xX).
  move: (iorder_osr or' j1) => [or1 sr1].
  apply: the_greatest_pr => //.
  apply: finite_subset_torder_greatest => //.
    by apply : worder_total.
have pa3': forall x A, inc x X -> nonempty (Ja x A) ->
  (inc (Ma x A) (Ja x A) /\
   (forall k, inc k (Ja x A) -> gle r' k (Ma x A))).
  move => x A xX aux; move: (pa3 _ _ xX aux) => [].
  rewrite iorder_sr //; last by apply: pa2.
  move=> xx sb;split => // k ks; move: (sb _ ks) => sc;apply: (iorder_gle1 sc).
pose ra Y A := induced_order r' (fun_image Y (fun z => Ma z A)).
pose Aa Y A := the_least (ra Y A).
pose Pb1 Y A := forall x, inc x Y -> nonempty (Ja x A).
pose Pb2 Y A := forall x y i, inc x Y -> inc y Y -> inc i A -> Vg x i = Vg y i.
pose Pb3 Y A := forall x i, inc x Y -> inc i (olexp_I x) ->
       inc i A \/ (forall j, inc j A -> glt r' i j).
pose Ba Y A := Zo Y (fun z => Ma z A = Aa Y A).
pose Ca Y A :=  fun_image (Ba Y A) (fun z => Vg z (Aa Y A)).
pose Da Y A := the_least (induced_order r (Ca Y A)).
pose Za Y A := Zo (Ba Y A) (fun z => Vg z (Aa Y A) = Da Y A).
pose Ta Y A := A +s1 (Aa Y A).
pose Pc Y A := [/\ Pa Y, Pb2 Y A, sub A (substrate r') & Pb3 Y A].
pose Pb4 Y A := forall i, inc i A -> glt r' (Aa Y A) i.
have H0: Pc X emptyset.
  split => //.
  - by split => //; move=> x y _ /setC_P [].
  - by move=> x y i _ _ /in_set0.
  - fprops.
  - by move => x i _ _; right; move => j /in_set0.
set f := induction_term (fun n p => J (Za (P p) (Q p)) (Ta (P p) (Q p)))
  (J X emptyset).
have f0: f \0c  = J X emptyset by apply: induction_term0.
have fn: forall n, inc n Nat -> 
   let Y := P (f n) in let A := Q (f n) in 
     f (csucc n) = J (Za Y A) (Ta Y A).
  by move => n nB; simpl; rewrite /f induction_terms.
(** Assume that [(Pa), (Pb2), (Pb3)] at level [n] implies the same 
   at level [n+1] and moreover [(Pb4)] that [Aa] is a strict lower bound of [A].
  By induction [(Pb4)]  is true at any level, so that [Aa(n)] is a striclty 
  decreasing sequence. Contradiction.
*)
suff HP: forall Y A, Pc Y A -> ( Pc (Za Y A) (Ta Y A) /\ Pb4 Y A).
  have fp: forall n, inc n Nat -> Pc (P (f n)) (Q (f n)). 
     apply: Nat_induction; first by rewrite f0; aw.
    move=> n nB hrec; move: (fn _ nB); simpl; move => ->; aw. 
    by move: (HP _ _ hrec) => [].
  pose g n := Aa (P (f n)) (Q (f n)).
  move: Nat_order_wor => [].
  set r'':= Nat_order => wor'' wsr.
  have  Ai:forall i j, i <=N j -> sub (Q (f i)) (Q (f j)).
     move=> i j [iB jB ij].
     move:(NS_diff i jB) (cdiff_pr ij).
     set k:= j -c i; move=> kB <-; move: k kB.
     apply: Nat_induction; first by rewrite csum0r; fprops.
     move=> n nB => hrec; apply: (sub_trans hrec); rewrite csum_nS //.
       by rewrite fn /Ta; aww; apply:NS_sum.
  have gp: forall n, inc n Nat -> inc (g n) (Q (f (csucc n))).
    by move=> n nB; rewrite (fn _ nB); aw; apply /setU1_P; right.
  have gpr: forall i j, inc i Nat-> inc j Nat -> i<c j -> inc (g i) (Q (f j)).
   move => i j iB jB /(cleSltP iB)  sij.
   move: (gp _ iB) => h.
    have aux: (csucc i <=N j) by split;fprops.
   exact : ((Ai _ _ aux) _ h).
  have gnp: forall n, inc n (substrate r'') -> inc (g n) (substrate r').
     rewrite wsr; move => n nB; move: (gp _ nB).
     move: (fp _ (NS_succ nB))=> [p1 p2 p3 p4]; by move: p3;  apply.
  have gp1: forall i j, glt r'' i j -> glt r' (g j) (g i).
     move=> i j lij. 
     have [iB jB ij]: [/\ inc i Nat, inc j Nat & i <c j].
       move: lij => [] /Nat_order_leP [pa pb pc] pd; done.
    move: (gpr _ _ iB jB ij); move: (fp _ jB) => pci.
    move: (HP _ _ pci) => [_]; apply.
  move: (worder_decreasing_finite wor'' wor' gnp gp1); rewrite wsr.
  by move: infinite_Nat_alt.
(** A careful sudy of all conditions completes the proof  *)
have pa0: forall Y  y i, Pa Y -> inc y Y -> inc i (substrate r') ->
    inc (Vg y i) (substrate r).
  move => Y y i [pa _ _] yY isr.
  move: (Xr _ (pa _ yY)) => /Zo_P [] /gfunctions_P2 [sa' sb sc] _. 
  apply sc; apply /(range_gP sa'); rewrite sb; ex_tac.
move=> Y A [pa pb pra prb]; move: (pa) =>[sYX neY xynY].
have sy: sub Y (substrate olexp) by apply: (sub_trans sYX qb). 
have hp1: Pb1 Y A.
  move=> x xY; case: (emptyset_dichot (Ja x A)) => //.
  move=> je; case: (pa1 Y pa x); red; rewrite iorder_sr //.
  split => // y yY; apply /iorder_gleP => //.
  have aux: forall i, inc i (substrate r') -> gle r (Vg x i) (Vg y i).
    move => i isr; move: (pa0 Y y i pa yY isr) => vis.
    case: (inc_or_not i (olexp_I x)) => iI.
      have iA: inc i A. 
         ex_middle niA; empty_tac1 i; apply /setC_P;split => //.
      by rewrite (pb _ _ _ xY yY iA); order_tac. 
    move: iI => /Zo_P sa'.
    have ->: Vg x i = olexp_lE by ex_middle xx; case: sa';split => //.
    have xx: (nonempty (substrate r)) by exists (Vg y i).
    move: (olexp_lEp xx) => [_ sd]; apply: sd => //.
  move: olexp_total => to; case: (total_order_pr2 to(sy _ yY) (sy _ xY)) => //.
  move=> [lexy nxy]; move: lexy => /olexp_gleP [_ _ h].
  case: h => //;move=> [j [jsr vxy _]]; move: (aux _  jsr) => vyx; order_tac.
have pa4: least (ra Y A) (Aa Y A).
  rewrite /ra;  set T := fun_image _ _.
  have neT: nonempty T. 
    move: neY => [y yY]; exists (Ma y A); apply /funI_P; ex_tac.
  have sT: sub T (substrate r').
    move => t /funI_P [z zY ->].  
    move: (pa3' _ _ (sYX _ zY) (hp1 _ zY)) => [pg ph].
    by move: (pa2 z A  (sYX _ zY)); apply.
  apply the_least_pr.
    by apply: (proj1 (iorder_osr or' sT)).
  move: wor' => [_ ok]; apply: ok => //.
have pa5: sub (fun_image Y (Ma^~ A)) (substrate r').
  move=> t /funI_P [z zY ->].
  have zX: inc z X by apply: sYX.
  move: (pa2 z A zX) => sr2.
  by move: (pa3' _ _ zX (hp1 _ zY)) => [h1 _]; apply: sr2.
have pa6: inc (Aa Y A) (fun_image Y (Ma^~ A)).
  move: pa4 => []; rewrite /ra iorder_sr //.
have pa7: inc (Aa Y A) (substrate r') by move: pa5 pa6; apply.
have neC: nonempty (Ca Y A).
  move: pa6 => /funI_P [z z1 z2].
  by exists  (Vg z (Aa Y A)); apply /funI_P;exists z => //; apply: Zo_i.
have pa8: sub (Ca Y A) (substrate r).
  move=> t /funI_P [z z1 ->].
  move: pa7 z1 =>  ais /Zo_P [zy _]. 
  by apply: (pa0 Y z (Aa Y A)) => //; move: pa => [pa _].
have pa9: least (induced_order r (Ca Y A)) (Da Y A).
  apply: the_least_pr.
    apply: (proj1 (iorder_osr or pa8)) => // t; rewrite /Ca; aw.
  by move: wor => [_ wor1]; apply: wor1; [apply: pa8 | apply: neC ].  
have s1: (sub (Ba Y A) Y)  by apply: Zo_S.
have sZY: sub (Za Y A) Y by  apply: sub_trans s1; apply: Zo_S.
have neZ: nonempty (Za Y A).
  move: pa9 => []; rewrite iorder_sr //; move /funI_P.
  move=> [z zb vz] _; exists z; apply: Zo_i => //.
have pa10: forall x y,
  inc x (Za Y A) -> inc y (X -s (Za Y A)) -> glt olexp x y.
  move=> x y xZ => /setC_P [yX yc].
  have nxy : x <> y by dneg xy; ue.
  move: xZ => /Zo_P [] /Zo_P [xY se] sf.
  have xX: inc x X by exact (sYX _ xY).
  case: (inc_or_not y Y) => yY; last by apply:xynY => //;apply/setC_P. 
  split => //; apply /olexp_gleP; split;fprops; right.
  have sm: gle r' (Aa Y A) (Ma y A). 
    move: pa4 => []; rewrite /ra iorder_sr //.
    move => _ h.
    have mf: inc (Ma y A) (fun_image Y (Ma ^~ A)) by apply /funI_P; ex_tac.
    by move: (h _ mf) => le1; move: (iorder_gle1 le1).
  have sd : forall i : Set, glt r' (Ma y A) i -> Vg x i = Vg y i.
    move => k kp.
    case: (inc_or_not k A) => kA; first by apply: pb => //.
    case: (equal_or_not (Vg y k)  olexp_lE).
       move => ->;  ex_middle vx.
       have kJ: inc k (Ja x A). 
         apply: Zo_i => //; apply: Zo_i => //; order_tac.
       move: (pa3' _ _ xX (hp1 _ xY)) => [sg sh].
       move: (sh _ kJ) => si. 
       have lt1: glt r' (Ma y A) (Ma x A) by order_tac.
       have : glt r' (Aa Y A) (Ma x A) by order_tac.
       by rewrite se; move=> [_]. 
    move => aux3.
    have kJ: inc k (Ja y A). 
       apply: Zo_i => //; apply: Zo_i => //; order_tac.
    move: (pa3' _ _ yX (hp1 _ yY)) => [_ sh]; move: (sh _ kJ) => ?; order_tac.
  case: (inc_or_not y (Ba Y A)). 
     move=> yB; move: yc => /Zo_P bad1.
     case:(equal_or_not (Vg y (Aa Y A)) (Da Y A)) => eq1; first by case: bad1.
     move: pa9 => []; rewrite iorder_sr //.
     move=> sa' sb. 
     have vc: inc (Vg y (Aa Y A)) (Ca Y A) by apply /funI_P; ex_tac.
     move: (sb _ vc) => aux; move: (iorder_gle1 aux) => aux2.
     have lt1: glt r (Vg x (Aa Y A)) (Vg y (Aa Y A)).
       by rewrite sf;split => //; apply:nesym.
     exists (Aa Y A);split => //.
     move: yB => /Zo_P [_ sc]; rewrite - sc.
     apply: sd; rewrite sc; order_tac.
  rewrite /Ba => /Zo_P ny.
  case: (equal_or_not (Ma y A) (Aa Y A)) => sm1; first by case: ny.
  exists (Ma y A);split => //; first by order_tac.
  move: (pa3' _ _ xX (hp1 _ xY)) => [sa' sb].
  move: (pa3' _ _ yX (hp1 _ yY)) => [say sby].
  case: (inc_or_not (Ma y A) (Ja x A)) => le1.
     move: (sb _ le1); rewrite se => le2; case: sm1; order_tac.
  have nsv: (Vg x (Ma y A)) <> (Vg y (Ma y A)).
    move: say => /Zo_P [sg sh].
    move: le1 => /Zo_P si.
    case: (inc_or_not (Ma y A) (olexp_I x)) => h; first by case: si.
    move: h sg => /Zo_P sj /Zo_P [sk sl].
    move=> sn; case: sj; rewrite sn; split; exact.
  split => //.
  case: (equal_or_not (Vg x (Ma y A)) olexp_lE).
      move => ->.
      have isr: inc (Ma y A)  (substrate r') by order_tac.
      move: (pa0 Y y (Ma y A) pa yY isr) => vis.
      have xx: (nonempty (substrate r)) by exists (Vg y (Ma y A)).
      move: (olexp_lEp xx) => [_ sg]; apply: sg => //.
    case: (inc_or_not (Ma y A) A) => ma; first by case: nsv; apply: pb.
  move => nsve.
  have kJ: inc (Ma y A) (Ja x A). 
     apply: Zo_i => //; apply: Zo_i => //; order_tac.
  move: (sb _ kJ); rewrite se => lt1; case: sm1; order_tac.
have pa12:Pb2 (Za Y A) (Ta Y A).
  move=> x y i. 
  move /Zo_P => [xB sxV].
  move /Zo_P => [yB syV].
  case/setU1_P; last by move => ->; rewrite sxV syV.
  by apply: pb; apply: s1.
have pa11: sub (Ta Y A) (substrate r').
  move=> t; case /setU1_P; [by apply: pra | by move => ->].
have pay: Pa  (Za Y A). 
  split => //; first by apply: (sub_trans sZY). 
have pa13: Pb3 (Za Y A) (Ta Y A).
  move => x i xZ iI.
  move: xZ => /Zo_P [] /Zo_P [x1 x2] x3.
  case: (prb _ _ x1 iI) => h; first by  left; apply /setU1_P; left.
  case: (inc_or_not i A) => iA; first by left;  apply /setU1_P; left.
  case: (equal_or_not i (Aa Y A)) => ia; first by left;  apply /setU1_P;right.
  right => j; case /setU1_P; first by apply: h.
  move=> ->; split => //; rewrite -x2.
  move: (pa3' _ _ (sYX _ x1) (hp1 _ x1)) => [say sby]. 
  by apply: sby; apply Zo_i.
have//: Pb4 Y A.
move=> i iA.
move: pa4; move=> []; rewrite iorder_sr //.
move /funI_P=> [z zY zv].
move: (pa3' _ _ (sYX _ zY) (hp1 _ zY)) => [say sby]. 
move: say => /Zo_P [p1 p2].
case: (prb _ _ zY p1) => //.
by rewrite - zv; move=> h _; apply h.
Qed.

End OlexPowBasic.

(** Assume [r] and [R] order isomorphic, and well as [r'] and [R'].
Then [(olexp r r')] and [(olexp R R')] are order isomorphic.

The idea is to associate to each element of [(olexp r r')] a function; by
composition, we get a function [R' -> R], the graph of this function is in
[(olexp R R')]. A isomorphis sends the least element to the least element, and
a finite set to a finite set.
 *)


Lemma image_of_inf r r' f: worder r -> worder r' ->
  order_isomorphism f r r' -> nonempty (substrate r) ->
  (inc (the_least r) (source f) /\
  Vf f (the_least r) = the_least r').
Proof.
move=> wor wor' [o1 o2 [bf sf tf] oif] ne1.
have ne2: nonempty (substrate r').
   move: ne1 => [x xs]; exists (Vf f x); rewrite - tf. 
   apply: Vf_target; [fct_tac | ue].
move: (the_least_pr o1  (worder_least wor  ne1)). 
move: (the_least_pr o2  (worder_least wor' ne2)). 
set x := the_least r; set y := the_least r'; move => pc [pa pb].
split ; [ by ue | apply: (unique_least o2) => // ].
rewrite - sf in pa.
split; first by Wtac; fct_tac.
rewrite - tf => z zt; move: bf => [_ sjf].
move: ((proj2 sjf) _ zt) => [t tsf ->]; rewrite - oif //.
apply: pb; ue. 
Qed.

Lemma fct_co_simpl_right f1 f2 g:
  f1 \coP g -> f2 \coP g -> bijection g -> f1 \co g = f2 \co g -> f1 = f2.
Proof.
move=> h1 h2 h3 h4.
set g1:= inverse_fun g.
have aux1: g \coP g1 by apply: composable_f_inv. 
move : (f_equal (fun z => z \co g1) h4).
rewrite - (compfA h1 aux1) -(compfA h2 aux1) bij_right_inverse //.
move: h1 h2 => [pa pb pc] [pd pe pf].
rewrite - {1} pc  -pf  compf_id_r // compf_id_r //.
Qed.

Lemma fct_co_simpl_left f1 f2 g:
  g \coP f1 -> g \coP f2 -> bijection g ->g \co f1 = g \co f2 -> f1 = f2.
Proof.
move=> h1 h2 h3 h4.
set g1:= inverse_fun g.
have aux1: g1 \coP g by apply: composable_inv_f. 
move : (f_equal (fun z => g1 \co z) h4).
rewrite (compfA  aux1 h1)  (compfA aux1 h2) bij_left_inverse //.
move: h1 h2 => [pa pb pc] [pd pe pf].
rewrite {1} pc pf  compf_id_l // compf_id_l //.
Qed.

Lemma opowa_invariant r1 r2 r3 r4:
   worder r1 -> worder r2 -> worder r3 -> worder r4 ->
   r1 \Is r2 -> r3 \Is r4 ->
   (olexp r1 r3) \Is (olexp r2 r4).
Proof.
move: r1 r2 r3 r4.
pose H13 r1 r3 :=  worder r1 /\ worder r3.
pose C3 r1 r3 := triple (substrate r3) (substrate r1).
pose s13 r1 r3 := substrate (olexp r1 r3).
have s1p: forall r1 r3 x, H13 r1 r3 -> inc x (s13 r1 r3) ->
   let C := C3 r1 r3 x in
    [/\ function C, source C = (substrate r3),
    target C = substrate r1 & graph C = x].
  move=> r1 r3 x [wor1 wor3]. 
  rewrite /s13 (proj2 (olexp_osr wor1 wor3)) => /Zo_P; move=> [pa _].
  rewrite /C3; aw;split => //; move /(gfunctions_P2): pa => [p1 p2 p3].
  apply: function_pr => //.
have cpp: forall r1 r2 r3 r4 f g1, H13 r1 r3 ->
  order_isomorphism f r1 r2 -> order_isomorphism g1 r4 r3 ->
  forall x, inc x (s13 r1 r3)  ->
  let C := C3 r1 r3 x in 
  [/\ f \coP C, function (f \co C),  ((f \co C) \coP g1), 
  function ((f \co C) \co g1) &
  source ((f \co C) \co g1) = (substrate r4) /\
   target ((f \co C) \co g1) = (substrate r2)].
  move =>  r1 r2 r3 r4 f g h13 isf isg x xsr C; aw.
  move: isf => [o1 o2 [bf sf tf] orf].
  move: isg => [o3 o4 [bg sg tg] org].
  move; move: (s1p _ _ _ h13 xsr) => [fc sc tc gc].
  have p1: f \coP C  by split => //;[ fct_tac| ue].
  have p2: function (f \co C) by fct_tac.
  have p3: ((f \co C) \coP g) by split => //; aw;try fct_tac; rewrite/C /C3; aw.
  split => //;fct_tac. 
pose h3 r1 r3 f g x := graph (f \co (C3 r1 r3 x) \co g).
have ax3: forall r1 r2 r3 r4 f g x, H13  r1 r3 -> H13 r2 r4 ->
  order_isomorphism f r1 r2 -> order_isomorphism g r4 r3 ->
  inc x (s13 r1 r3) -> inc (h3 r1 r3 f g x) (s13 r2 r4).
   move => r1 r2 r3 r4 f g x h13 [wo2 wo4] isf isg.
   move: (h13) => [wo1 wo3].
   move: (isf) => [o1 o2 [bf sf tf] orf].
   move: (isg) => [o3 o4 [bg sg tg] org].
   move=> xs; move: (s1p _ _ _ h13 xs) ; set C := C3 r1 r3 x.
   move => [fc sc tc gc].
   have sctg: (source C = target g) by rewrite /C /C3; aw.
   have o12g:  sub (olexp_I r1 r3 x) (target g).
      by move=> t; rewrite tg;  apply: Zo_S.
   move: (cpp _ _ _ _ _ _  h13 isf isg _ xs) => [p1 p2 p3 p4 [p5 p6]].
   rewrite /s13 (proj2 (olexp_osr wo2 wo4)); apply: Zo_i.
      by rewrite -p5 -p6; apply: gfunctions_i.
   set s:= olexp_I _ _ _.
   have qz: forall t, inc t (substrate r4) -> inc (Vf g t) (source C). 
     move => t ts4.
     have s3: inc t (source g) by aw;ue.
     rewrite sctg; aw; apply Vf_target =>//; fct_tac.
    set l2 := olexp_lE r2; set l1 := olexp_lE r1.
   have fg: function g by fct_tac.
   have qa: s = Zo (substrate r4) (fun i => Vf f (Vf C (Vf g i))  <> l2). 
     set_extens t => /Zo_P [q1 q2]; apply /Zo_P;split => //; move: q2;
     rewrite /h3 -/(Vf (f \co C \co g) t) => //; rewrite - sg in q1;
     rewrite ! compfV //; Wtac.
   have qb: s = Zo (substrate r4) (fun i => (Vf C (Vf g i)) <> l1). 
     rewrite qa; set_extens t => /Zo_P [q1 q2]; apply/Zo_P;split => //;move: q2.
       set u := Vf C (Vf g t).
       case: (equal_or_not u l1) => // h1; case.
       have ur1: inc u (substrate r1).
         by rewrite -tc; apply: Vf_target => //; apply: qz.
       have ne1: nonempty (substrate r1) by ex_tac.
       rewrite /l2/olexp_lE; move:(image_of_inf wo1 wo2 isf ne1) => [qc <-]; ue.
     set u := Vf C (Vf g t) => h; dneg h1.
      have ur1: inc u (substrate r1).
         by rewrite - tc; apply: Vf_target => //; apply: qz.
       have ne1: nonempty (substrate r1) by ex_tac.
       rewrite /l2/olexp_lE; move: (image_of_inf wo1 wo2 isf ne1) => [qc].
       have <-: l2 = the_least r2 by done.
       rewrite -h1 => sv.
       move: bf => [[ff fi] _]; apply: fi => //; ue.
  set g1:= inverse_fun g.
  have ss1: sub (olexp_I r1 r3 x) (source g1) by rewrite /g1; aw.
  have p0: bijection g1 by apply: inverse_bij_fb.
  have fg1: function g1 by fct_tac.
  have -> : s = Vfs g1 (olexp_I r1 r3 x).
   rewrite qb; set_extens t.
     move => /Zo_P; rewrite {1} /Vf corresp_g ;move=> [ts4 tv]. 
     apply /(Vf_image_P fg1 ss1); exists (Vf g t) => //. 
        apply /Zo_P;split => //; Wtac.
     by rewrite inverse_V2 //; ue.
   move => /(Vf_image_P fg1 ss1) [u /Zo_P].
   have ->:  substrate r4 = target g1 by rewrite /g1; aw.
   move => [pa pb] ->; apply /Zo_P; split. 
      Wtac;rewrite /g1; aw; ue.
   by rewrite - tg in pa; rewrite (inverse_V bg); rewrite /C /C3 /Vf; aw.
  apply: finite_image_by => //.
  by move: xs; rewrite /s13 (proj2 (olexp_osr wo1 wo3)) // => /Zo_P  [_].
move=> r1 r2 r3 r4 wo1 wo2 wo3 wo4 [f isf] [g isg].
move: (inverse_order_is isg) => isg1.
move: (inverse_order_is isf) => isf1.
have h13a: H13 r1 r3 by split.
have h24a: H13 r2 r4 by split.
set g1 := inverse_fun g; set f1 := inverse_fun f.
pose h := h3 r1 r3 f g1.
pose hi := h3 r2 r4 f1 g.
set srs := substrate (olexp r1 r3); set srt:= substrate (olexp r2 r4). 
have ax: forall x, inc x srs -> inc (h x) srt.
  move => x srx.
  by move: (ax3 r1 r2 r3 r4 f g1 x h13a h24a isf isg1 srx).
have ax': forall x, inc x srt -> inc (hi x) srs.
  move => x srx.
  by move: (ax3 r2 r1 r4 r3 f1 g x h24a h13a isf1 isg srx).
move: (isf) => [o1 o2 [bf sf tf] orf].
move: (isg) => [o3 o4 [bg sg tg] org].
have sg1: source g1 = substrate r4 by rewrite /g1 ; aw.
have tg1: target g1 = substrate r3 by rewrite /g1 ; aw.
have sf1: source f1 = substrate r2 by rewrite /f1 ; aw.
have tf1: target f1 = substrate r1 by rewrite /f1 ; aw.
have p0: bijection g1 by apply: inverse_bij_fb.
have hin: forall x y, inc x srs -> inc y srs -> h x = h y  -> x = y.
  rewrite /h;move=> x y xs ys sh.
  move: (cpp _ _ _ _ _ _ h13a isf isg1 _ xs) => [p1 p2 p3 p4 [p5 p6]].
  move: (cpp _ _ _ _ _ _ h13a isf isg1 _ ys) => [q1 q2 q3 q4 [q5 q6]].
  have pa: ((f \co C3 r1 r3 x) \co g1) = ((f \co C3 r1 r3 y) \co g1).
     by apply: function_exten1 => //; rewrite p6 q6 //.
  move: (fct_co_simpl_right p3 q3 p0 pa) => pb.
  move: (fct_co_simpl_left p1 q1 bf pb); rewrite /C3 => pc.
  by move: (f_equal graph pc); aw.
have hs: forall y, inc y srt -> exists2 x, inc x srs & y = h x.
  move=> y ysr.
  move: (ax' _ ysr) => aux.
  move: (s1p r2 r4 y h24a ysr); set z:= C3 r2 r4 y; move => [s1 s2 s3 s4]. 
  move: (s1p r1 r3 _ h13a aux);set w:= C3 _ _ _; move=> [s1' s2' s3' s4']. 
  exists (hi y) => //; rewrite /h  /h3; rewrite -/w.
  rewrite - s4; apply f_equal.
  move: (cpp _ _ _ _ _ _ h13a isf isg1 _ aux).
    rewrite -/w -/g1; move => [p1 p2 p3 p4 [p5 p6]].
  move: (cpp _ _ _ _ _ _ h24a isf1 isg _ ysr).
    rewrite -/f1 -/z; move => [q1 q2 q3 q4 [q5 q6]].
  have: w = f1 \co z \co g.
    rewrite /w /hi /h3 -/z.
    move: q4 => [q4 _ _]; rewrite - {2} (corresp_recov1 q4) /C3.
    by rewrite -q5 - q6; aw.
  move => ->.
  set a := (f1 \co z).
  have c1: f \coP a. rewrite /a /f1;red; aw; split => //; fct_tac.
  rewrite  (compfA c1 q3).
  have c2: f \coP f1 by apply: composable_f_inv.
  have c3: g \coP g1 by apply: composable_f_inv.
  have c4: z \coP g by split => // ; [fct_tac | rewrite s2; ue].
  have ->: f \co a = z.
      rewrite /a  compfA // bij_right_inverse //.
      have ->: target f = target z by rewrite s3; ue.
      rewrite compf_id_l //.
   rewrite  - compfA // bij_right_inverse //.
      have ->: target g = source z by rewrite s2; ue.
      rewrite compf_id_r //.
move: (olexp_osr wo1 wo3) => [oa os13].
move: (olexp_osr wo2 wo4) => [ob os24].
exists (Lf h srs srt); saw; rewrite ? os13 ? os24.
   saw; apply: lf_bijective => //.
have hp: forall z i, inc z srs -> inc i (substrate r4) ->
   Vg (h z) i =  Vf f (Vg z (Vf g1 i)).
  move => z i zrs isr.
  move: (cpp _ _ _ _ _ _ h13a isf isg1 _ zrs) => [q1 q2 q3 q4 [q5 q6]].
  rewrite - sg1 in isr. 
  have w1:  inc (Vf g1 i) (source (C3 r1 r3 z)).
  rewrite /C3; aw; rewrite - tg1; Wtac; fct_tac.
  by rewrite /h /h3 -/(Vf _ i) ! compfV//; rewrite {2} /Vf  /C3; aw.
have p1: olexp_G r1 r3 = srs  by  ue.
have p2: olexp_G r2 r4 = srt  by ue.
red; aw. move => x y xsr ysr; rewrite !LfV//;split.
   move => /(olexp_gleP wo1 wo3); rewrite p1; move =>  [xi yi cxy]. 
   apply /(olexp_gleP wo2 wo4); rewrite p2;split => //; try (apply: ax => //).
  case: cxy => cxy; first (by rewrite cxy; left); right.
  move: cxy => [j [js3 ltj eqj]].
  have wj4: inc (Vf g j) (substrate r4) by rewrite - tg; Wtac; fct_tac. 
  have jv: Vf g1 (Vf g j) = j by rewrite inverse_V2 //; ue.
  exists (Vf g j); split => //.
     by rewrite hp // hp // jv; apply :(order_isomorphism_sincr isf).
   move => i ip.
   have i4:inc i (substrate r4) by order_tac.
   rewrite hp // hp //; congr (Vf f _); apply: eqj.
   by rewrite - jv; apply : (order_isomorphism_sincr isg1).
move => /(olexp_gleP wo2 wo4); rewrite p2; move =>  [xi yi cxy]. 
   apply /(olexp_gleP wo1 wo3); rewrite p1;split => //.
case: cxy => cxy; first (by left; apply hin); right.
move: cxy => [j [js4 ltj eqj]].
have wj4: inc (Vf g1 j) (substrate r3) by rewrite - tg1;Wtac;fct_tac. 
have jv: Vf g (Vf g1 j) = j by rewrite inverse_V //; ue.
have xyi: forall i, inc i (substrate r3) ->
    (inc (Vg x i) (substrate r1) /\ inc (Vg y i) (substrate r1)).
  move=> i isr; split.
    move: xsr; rewrite -p1 => /Zo_P [] /gfunctions_P2 [q1 q2 q3] _.
    apply: q3; apply /(range_gP q1); rewrite q2; ex_tac.
  move: ysr; rewrite -p1  => /Zo_P [] /gfunctions_P2 [q1 q2 q3] _.
  apply: q3;  apply /(range_gP q1); rewrite q2; ex_tac.
exists (Vf g1 j); split => //.
   move: (ltj); move: (xyi _ wj4); rewrite - sf; move => [s1 s2].
   by rewrite hp // hp //; move /(order_isomorphism_siso isf s1 s2).
move => i ip.
have i4:inc i (substrate r3) by order_tac.
have wi: inc (Vf g i) (substrate r4) by rewrite - tg; Wtac; fct_tac. 
have i5: glt r4 j (Vf g i) by rewrite -jv; apply (order_isomorphism_sincr isg).
move: (eqj _ i5).
move: (xyi _ i4); rewrite - sf; move => [s1 s2].
move: bf => [[_ isf2] _].
have iv: Vf g1 (Vf g i) = i by rewrite inverse_V2 //; ue. 
by rewrite hp // hp // iv; apply: isf2.
Qed.

(** Let [X] and [Y] be any two well-ordered sets,  [x] and [y] their
ordinals. The ordinal of [olexp X Y] depends only on [x] and [y]; we shall
denote it by  [x ^O y]. 

We have [x ^o y = x ^O y] in case [x=0], [x=1], [y=0] and [y=1]. 
*)

Definition ord_powa x y := ordinal (olexp (ordinal_o x) (ordinal_o y)).

Notation "x ^O y" := (ord_powa x y) (at level 30).

Lemma OS_ord_powa a b: ordinalp a -> ordinalp b ->
  ordinalp (a ^O b).
Proof.
by move=> oa ob; apply: OS_ordinal; apply: olexp_worder; apply: ordinal_o_wor.
Qed.

Lemma ord_powa_pr0 r r': worder r -> worder r' ->
   ordinal (olexp r r') = (ordinal r) ^O (ordinal r').
Proof.
move => wor wor'.
move: (OS_ordinal wor)(OS_ordinal wor') => o1 o2.
apply: ordinal_o_isu2.
- by  apply olexp_worder.
- by apply: OS_ord_powa.
move: (ordinal_o_is wor) (ordinal_o_is wor') => is1 is2.
move: (ordinal_o_wor o1) => wor1.
move: (ordinal_o_wor o2) => wor2.
move: (opowa_invariant wor wor1 wor' wor2 is1 is2).
move: (ordinal_o_is (olexp_worder wor1 wor2)) => t1 t2.
by move: (orderIT t2 t1).
Qed.

Lemma ord_powa_pr1 x : ordinalp x ->  x ^O \0o = x ^o \0o.
Proof.
move: OS0=> oz ox; rewrite opowx0.
have w1: worder (ordinal_o x) by  apply:ordinal_o_wor.
have w2: worder (ordinal_o \0o) by  apply:ordinal_o_wor.
move:(olexp_osr w1 w2) => [pa pb].
apply: set1_ordinal => //; rewrite pb.
by apply: olex_Fe; rewrite ordinal_o_sr.
Qed.

Lemma ord_powa_pr2 y : ordinalp y -> y <> \0o ->  \0o ^O y = \0o ^o y.
Proof.
move: OS0=> oz oy ynz; rewrite opow0x //.
have w1: worder (ordinal_o y) by  apply:ordinal_o_wor.
have w2: worder (ordinal_o \0o) by  apply:ordinal_o_wor.
move:(olexp_osr w2 w1) => [pa pb].
apply: ordinal0_pr1 => //;rewrite pb.
by apply: olex_nFe_Ee;rewrite ordinal_o_sr.
Qed.

Lemma ord_powa_pr3 y : ordinalp y ->  \0o ^O y = \0o ^o y.
Proof.
move =>  oy; case: (equal_or_not y \0o) => ynz.
   rewrite ynz; apply:ord_powa_pr1; fprops.
by apply:ord_powa_pr2.
Qed.

Lemma ord_powa_pr4 y : ordinalp y ->  \1o ^O  y = \1o ^o y.
Proof.
move: OS1=> oz ox; rewrite opow1x.
have w1: worder (ordinal_o y) by  apply:ordinal_o_wor.
have w2: worder (ordinal_o \1o) by  apply:ordinal_o_wor.
move:(olexp_osr w2 w1) => [pra prb].
apply: set1_ordinal => //.
apply /singletonP; split.
  have ne1: nonempty (substrate (ordinal_o \1o)).
     exists emptyset; rewrite /ord_one /card_one ordinal_o_sr;fprops.
  move:(olexp_G_least w2 w1  ne1) => [h _]; ex_tac.
rewrite prb /olexp_G /olexp_I ! ordinal_o_sr.
move=> a b => /Zo_P [pa _] /Zo_P [pb _].
move: (gfunctions_hi pa)=> [f [ff sf tf <-]].
move: (gfunctions_hi pb)=> [g [fg sg tg <-]].
suff: f = g by move => ->.
apply: function_exten => //; (try ue) => x xsf.
have : inc (Vf f x) \1o by Wtac.
rewrite sf in xsf; have : inc (Vf g x) \1o by Wtac.
by move => /set1_P -> /set1_P ->.
Qed.

Lemma ord_powa_pr5 x : ordinalp x ->  x ^O \1c = x ^o \1c.
Proof.
move: OS1 => oo ox; rewrite (opowx1 ox).
have ese: inc emptyset (singleton emptyset) by fprops.
have w1: worder (ordinal_o x) by  apply:ordinal_o_wor.
have w2: worder (ordinal_o \1o) by  apply:ordinal_o_wor.
have w3: worder (olexp (ordinal_o x) (ordinal_o \1c)) by apply olexp_worder.
apply: ordinal_o_isu2 => //; apply: orderIS.
move: w1 w2; set r :=  (ordinal_o x);  set r':= (ordinal_o \1c).
move => w1 w2.
move: (olexp_osr w1 w2) => [ooo sr].
move: (ordinal_o_sr \1o); rewrite -/r' /ord_one /card_one => sr'.
have oG: olexp_G r r'= (gfunctions (substrate r') (substrate r)).
   apply extensionality; first by apply: Zo_S.
   move => t tf; apply: Zo_i => //.
   have : finite_set (substrate r') by rewrite sr';apply: set1_finite.
  rewrite /olexp_I sr'; apply: sub_finite_set; apply: Zo_S.
rewrite sr' in oG.
set f := cst_graph (singleton emptyset).
have ta: forall t, inc t (substrate r) -> inc (f t) (substrate (olexp r r')).
  move => t tsr; rewrite sr oG; apply /gfunctions_P2. 
  rewrite /f/cst_graph;split => //;aw; fprops.
  by move => z /Lg_range_P [_ _ ->].
set F := Lf f (substrate r)  (substrate (olexp r r')).
have bf: bijection F. 
  apply: lf_bijective => //.
    move => u v usr vsr sf; move: (f_equal (Vg ^~emptyset) sf).
     rewrite /f/cst_graph; rewrite  !LgV//.
  move => y; rewrite sr oG =>ys;move:(gfunctions_hi ys)=> [k [fk sk tk gk]].
  set z := Vf k emptyset.
  have zr: inc z (substrate r) by rewrite /z; Wtac ; rewrite sk; fprops.
  ex_tac;symmetry;rewrite /f /cst_graph - gk; apply: fgraph_exten; aww.
    by rewrite (domain_fg fk) sk.
  move => t ts /=; rewrite LgV//; move: ts => /set1_P -> //.
exists F.
apply: total_order_isomorphism; rewrite /F; aww.
  by apply: worder_total.
move => a b asr bsr rab; rewrite !LfV //.
apply /(olexp_gleP w1 w2); rewrite - sr;split;fprops.
case: (equal_or_not a b) => eab; first by rewrite eab; left.
right; exists emptyset; rewrite /f sr'; aw; split;fprops.
    by rewrite /cst_graph !LgV.
move => i [pa] [].
have: inc i (substrate r') by order_tac.
by rewrite sr' => /set1_P.
Qed.

Lemma inclusion_morphism_a a b (f:= Lf id a b) : a <=o b ->
   (  segmentp (ordinal_o b) (Imf f)
    /\  order_morphism f  (ordinal_o a) (ordinal_o b)).
Proof.
move => [oa ob ab].
have s1: segmentp (ordinal_o b) a.
     rewrite /segmentp (ordinal_o_sr b).
     split; [exact | move => s t; aw ].
     move /(oltP oa) => su /ordo_leP [tv sv ts]. 
     have ot:= (Os_ordinal ob tv).
     have os:= (Os_ordinal ob sv).
     apply /(oltP oa);  apply: ole_ltT su; split => //. 
split; first by rewrite (ci_range ab).
rewrite /f; split; fprops.
  rewrite !ordinal_o_sr;hnf;aw; split => //; fprops.
red; aw;move => x y xa ya; rewrite ! LfV//; split. 
   move => /ordo_leP [tv sv ts]; apply /ordo_leP;split;fprops.
   move => /ordo_leP [tv sv ts]; apply /ordo_leP;split;fprops.
Qed.

Lemma inclusion_morphism_b a b f : a <o b ->
  segmentp (ordinal_o b) (Imf f) ->
  order_morphism f (ordinal_o a) (ordinal_o b) ->
  (forall x, inc x a -> Vf f x = x).
Proof.
move => hlt s1 m1.
move:(hlt) => [[oa ob sab] _].
move: (inclusion_morphism_a (proj1 hlt)) => [s2 m2].
rewrite (isomorphism_worder_unique (ordinal_o_wor oa)(ordinal_o_wor ob)
      s1 s2 m1 m2) => x xa; rewrite LfV//.
Qed.

(** We have [(a ^O (b +o c)) = (a ^O b) *o (a ^O c)] 

Let [f] be a functional graph on [B+C] with values in [A]; we associate the two 
restrictions to [B] and [C]. If [f] is almost everywhere [e], then the same
holds for both restrictions, and conversely. The mapping [f -> (f1,f2)] is
obviously order-preserving; this gives an order isomorphism.
*)

Lemma power_of_suma a b c: ordinalp a -> ordinalp b -> ordinalp c ->
  (a ^O (b +o c)) = (a ^O b) *o (a ^O c). 
Proof.
move => oa ob oc.
move: (ordinal_o_wor oa) => woa.
move: (ordinal_o_wor ob) => wob.
move: (ordinal_o_wor oc) => woc.
move: (ordinal_o_wor (OS_sum2 ob oc)) => wo_bc.
move: (OS_ord_powa oa ob) => o_ab.
move: (OS_ord_powa oa oc) => o_ac.
move: (ordinal_o_wor o_ab) => wo_ab.
move: (ordinal_o_wor o_ac) => wo_ac.
apply: ordinal_o_isu1; [ by apply: olexp_worder |  by apply: orprod2_wor | ].
rewrite /ord_powa.
move: (orprod_invariant4 (ordinal_o_is (olexp_worder woa wob))
  (ordinal_o_is (olexp_worder woa woc))).
apply: orderIT.
rewrite /osum2.
move: (orsum2_wor wob woc) => pa.
move: (ordinal_o_is (orsum2_wor wob woc)) => pb.
move: (worder_invariance pb pa) => pc.
move: (orderIR (proj1 woa)) => pd.
move: (orderIS(opowa_invariant woa woa pa pc pd pb)) => h.
apply: (orderIT h).
move: woa wob woc.
set A := ordinal_o a; set B := ordinal_o b; set C:= ordinal_o c => woa wob woc.
clear wo_ab wo_ac pa pb pc pd h wo_bc o_ab o_ac.
set Gab:= (olexp_G A B).
set Gac := (olexp_G A C).
set Gabc := olexp_G A (order_sum2 B C).
set gab:= (gfunctions b a).
set gac:= (gfunctions c a).
set gabc:= (gfunctions (canonical_du2 b c) a).
pose fOI u v := fun x => finite_set (olexp_I u v x).
move: (olexp_worder woa woc)  (olexp_worder woa wob) => woac woab.
move: (orsum2_wor wob woc) => wobc.
move: (woab)(woac) => [oab _] [oac _].
move:(ordinal_o_sr a) (ordinal_o_sr b) (ordinal_o_sr c)  => sa sb sc.
move:(olexp_osr woa wob) (olexp_osr woa woc) => [_ sab][_ sac].
have sr0: product2 (substrate (olexp A C)) (substrate (olexp A B)) =
   product2 Gac Gab.
   by rewrite sab sac.
have sr1: substrate (order_prod2 (olexp A B) (olexp A C)) = product2 Gac Gab.
   by rewrite (proj2 (orprod2_osr oab oac)).
have sr2: substrate (olexp A (order_sum2 B C)) = Gabc.
  by rewrite (proj2 (olexp_osr woa wobc)).
have sr3: (substrate (order_sum2 B C)) = canonical_du2 b c.
  by rewrite (orsum2_sr (proj1 wob) (proj1 woc)) sb sc. 
have Gab1: Gab = Zo gab (fOI A B)  by rewrite /Gab /olexp_G sa sb.
have Gac1: Gac = Zo gac (fOI A C)  by rewrite /Gac /olexp_G sa sc.
have Gabc1: Gabc = Zo gabc (fOI A (order_sum2 B C)). 
  by rewrite /Gabc  /olexp_G sr3 sa.
pose pr1f f := Lg b (fun z => Vg f (J z C0)).
pose pr2f f := Lg c (fun z => Vg f (J z C1)).
pose pr3f f := variantLc (pr2f f) (pr1f f).
have pr1f1: forall f, inc f gabc -> inc (pr1f f) gab.
  move => f; rewrite /gabc /gab.
  move /gfunctions_P2; move => [fgf df rf].
  apply /gfunctions_P2; rewrite /pr1f; split; [ fprops| by aw | ].
  move => t /Lg_range_P [x xb ->]; apply: rf; apply /(range_gP fgf).
  by exists (J x C0) => //;rewrite df; apply candu2_pra.
have pr2f1: forall f, inc f gabc -> inc (pr2f f) gac.
  move => f; rewrite /gabc /gac.
  move /gfunctions_P2; move => [fgf df rf].
  apply /gfunctions_P2; rewrite /pr2f; split; [ fprops| by aw | ].
  move => t /Lg_range_P [x xb ->]; apply: rf; apply /(range_gP fgf).
  by exists (J x C1) => //;rewrite df; apply candu2_prb.
have pr1f2: forall f, inc f Gabc -> inc (pr1f f) Gab.
   move => f; rewrite Gab1 Gabc1 => /Zo_P [pa pb]; apply /Zo_P; split;fprops.
   move: pb; rewrite /fOI /olexp_I sr3 sb.
   set e1:= Zo _ _; set e2 := Zo _ _ => fe1.
   have hp: forall x, inc x e2 -> inc (J x C0) e1.
      move => x => /Zo_P [xb xx]; apply: Zo_i; first by apply candu2_pra.
      move: xx;rewrite /pr1f LgV//.
   apply: (sub_image_finite_set fe1 hp) => u v _ _ sv; apply: (pr1_def sv).
have pr2f2: forall f, inc f Gabc -> inc (pr2f f) Gac.
   move => f; rewrite Gac1 Gabc1; move /Zo_P => [pa pb]; apply Zo_i; fprops.
   move: pb; rewrite /fOI /olexp_I sr3 sc.
   set e1:= Zo _ _; set e2 := Zo _ _ => fe1.
   have hp: forall x, inc x e2 -> inc (J x C1) e1.
      move => x => /Zo_P [xb xx]; apply: Zo_i; first by apply candu2_prb.
      move: xx;rewrite /pr2f LgV//.
  apply: (sub_image_finite_set fe1 hp) => u v _ _ sv; apply: (pr1_def sv).
have pr2f3: forall f, inc f Gabc -> inc (pr3f f) (product2 Gac Gab).
  move => f fi; move: (pr1f2 _ fi)(pr2f2 _ fi) => pa pb.
  apply /setX2_P; rewrite /pr3f !LgV//; aw; fprops; split;fprops.
pose g := Lf pr3f Gabc  (product2 Gac Gab).
have bg: bijection g.
  apply: lf_bijective => //.
    rewrite Gabc1;move => u v /Zo_S ug /Zo_S vg  sv.
    move: (f_equal (Vg ^~ C0) sv) (f_equal (Vg ^~ C1) sv).
    rewrite /pr3f; aw; rewrite /pr1f /pr2f => eq1 eq2.
    move: ug vg => /gfunctions_P1  [fgu du _] /gfunctions_P1 [fgv dv _].
    apply: fgraph_exten => //; rewrite du // => x /candu2P. 
    move => [px]; case; move => [Px Qx]; move: px; rewrite /pairp Qx => px.
      move: (f_equal (Vg ^~ (P x)) eq2); rewrite !LgV//; ue.
    move: (f_equal (Vg ^~ (P x)) eq1); rewrite !LgV//; ue.
  move => y /setX2_P  [fgy dy vy1 vy2].
  set z := Lg (canonical_du2 b c) 
      (fun t => (Yo (Q t = C0) (Vg (Vg y C1) (P t))(Vg (Vg y C0) (P t)))).
  have fgz: fgraph z by rewrite /z;fprops.
  have dz:  domain z = canonical_du2 b c by rewrite /z; aw.
  move: (vy1) => /Zo_P  [] /gfunctions_P2 [pa1 pb1 pc1] pd1.
  move: (vy2) => /Zo_P [] /gfunctions_P2 [pa2 pb2 pc2] pd2.
  move: C1_ne_C0 => td.
  have eqa: pr3f z = y.
    rewrite /pr3f; apply:fgraph_exten.
    - fprops.
    - done.
    - by aw.
    - aw => x xtp; rewrite /pr1f /pr2f.
      try_lvariant xtp;apply:fgraph_exten; fprops; aw.
      + by rewrite pb1.
      + move => t tc;  move: (candu2_prb b tc) => h.
        by  rewrite (LgV tc) (LgV h) pr1_pair pr2_pair; Ytac0.
      + by rewrite pb2.
   - move => t tc; move: (candu2_pra c tc) => h.
     by rewrite (LgV tc) (LgV h) pr1_pair pr2_pair; Ytac0.
  exists z; last by exact.
  have zg: inc z gabc. 
    apply /gfunctions_P2; split => // t /(range_gP fgz). 
    rewrite dz;move => [x xdz ->].
    move: (xdz) => /candu2P.
    move => [px]; case; move => [Px Qx]; rewrite /z LgV//; rewrite Qx; Ytac0.
      move: vy2 =>/Zo_P [] /gfunctions_P2 [pa pb pc] _.
      rewrite - sa; apply:pc; apply /(range_gP pa). 
      rewrite pb;exists (P x) => //; ue.
    move: vy1 =>/Zo_P [] /gfunctions_P2 [pa pb pc] _.
    rewrite - sa; apply:pc; apply /(range_gP pa).
    rewrite pb;exists (P x) => //; ue.
  apply: Zo_i; first by rewrite sr3 sa.
  move: pd1 pd2;rewrite /olexp_I.
  set e1 := Zo _ _; set e2 := Zo _ _; set e3 := Zo _ _ => fe1 fe2.
  move: (finite_fun_image  (fun z => (J z C1)) fe1).
  move: (finite_fun_image  (fun z => (J z C0)) fe2) => fe1' fe2'.
  move: (finite_union2 fe1' fe2') => fe3'.
  apply: sub_finite_set fe3'.
  move => t /Zo_P; rewrite sr3;  move => [tdi vt]; apply /setU2_P.
  move: (tdi) => /candu2P [pt]; case=> [][Pt Qt]; [left | right ]; move: vt; 
    rewrite (LgV tdi) Qt; Ytac0 => tnl; apply /funI_P; rewrite  -Qt;
     exists (P t) => //; apply: Zo_i => //; ue.
exists g; apply: total_order_isomorphism.
- apply: worder_total; apply: olexp_worder => //.
- by apply: orprod2_or; apply: (proj1 (olexp_osr _ _)).
- done.
- by rewrite /g; aw.
- by rewrite /g; aw.
- rewrite /g lf_source; move => x y xsg ysg /=.
rewrite (LfV  pr2f3 xsg)(LfV  pr2f3 ysg).
move /(olexp_gleP woa wobc) => [_ _ cxy].
apply / (orprod2_gleP (proj1 woab) (proj1 woac)); rewrite sr0.
move: (pr2f3 _ xsg) (pr2f3 _ ysg) => ip1 ip2.
split; [by done | by done |  case: cxy].
  move => <-; left; split; [reflexivity | order_tac].
  by move: ip1; rewrite - sr0 ; move /setX2_P=> [_ _ _].
rewrite sr3; move => [j [jc jv ajv]].
rewrite /pr3f; aw.
move: jc => /candu2P [pj]; case; move => [Pj Qj].
  left; split.
    have xg: inc x gabc by  move: xsg =>/Zo_P []; rewrite sr3 sa.
    have yg: inc y gabc by move: ysg  =>/Zo_P []; rewrite sr3 sa.
    move: (pr2f1 _ xg)  =>/gfunctions_P1 [fg1 d1 v1].
    move: (pr2f1 _ yg) =>/gfunctions_P1 [fg2 d2 v2].
    apply: fgraph_exten => //; rewrite d1 // => t tc.
    have lt1: glt (order_sum2 B C) j (J t C1).
    rewrite - pj Qj; apply:orsum2_gle_spec.
        by rewrite sb.
      by rewrite sc.
    move: (ajv _ lt1); rewrite /pr2f!LgV//.
    apply /(olexp_gleP woa wob). 
    split; [ by apply: pr1f2 | by apply: pr1f2 | right ].
  exists (P j); rewrite sb /pr1f !LgV//; rewrite -Qj pj; split => //.
  move => i [iv niv].
  have ib: inc i b by rewrite - sb; order_tac.
  rewrite ! LgV//; apply: ajv; split; last by rewrite -{1} pj; dneg uu; exact (pr1_def uu).
  apply /orsum2_gleP; rewrite  -{1} pj Qj pr1_pair pr2_pair.
  split; first by apply: candu2_pra; rewrite sb.
    by apply: candu2_pra; rewrite sb.
  by constructor 1. 
right; move: (jv) => [_ jvb].
split; last first.
  move => sv; case: jvb;move: (f_equal (Vg ^~(P j)) sv); rewrite /pr2f !LgV//.
  by rewrite -Qj pj.
apply /(olexp_gleP woa woc). 
split; [ by apply: pr2f2 | by apply: pr2f2 | right].
exists (P j); rewrite sc /pr2f !LgV//; rewrite -Qj pj; split => //.
move => i [iv niv].
have ic: inc i c by rewrite - (ordinal_o_sr c); order_tac.
rewrite !LgV//; apply: ajv; split; last by rewrite -{1} pj; dneg uu; exact (pr1_def uu).
apply /orsum2_gleP; rewrite -{1} pj Qj pr1_pair pr2_pair.
split; first by apply: candu2_prb; rewrite sc.
  by apply: candu2_prb; rewrite sc.
by constructor 2; split; fprops.
Qed.

Lemma ord_powa_M_eqle a b c: ordinalp a -> b <=o c -> a <> \0o ->
   a ^O b <=o a ^O c.
Proof.
move => oa bc anz.
move: (odiff_pr bc); set d := c -o b; move => [od ->].
rewrite (power_of_suma oa (proj31 bc) od).
apply: oprod_Mle1; first by exact (OS_ord_powa oa (proj31 bc)).
suff h: a ^O d <> \0o.
  exact (ord_ne0_pos (OS_ord_powa oa od) h).
move => h.
move:  (ordinal_o_wor oa)(ordinal_o_wor od) => woa wod.
move: (ordinal0_pr2 (olexp_worder woa wod) h).
have ne: nonempty (substrate (ordinal_o a)).  
   rewrite  (ordinal_o_sr a); case: (emptyset_dichot a) => //.
move: (olexp_G_least woa wod ne).
set m := cst_graph _ _; move => [ms _] bad; empty_tac1 m.
Qed.


Lemma ord_powa_succ a b: ordinalp a -> ordinalp b ->
   a ^O (osucc b) = (a ^O b) *o a.
Proof.
move => oa ob; rewrite -(osucc_pr ob) (power_of_suma oa ob OS1).
by rewrite (ord_powa_pr5 oa) opowx1.
Qed.

(** We have [x ^O y = x ^o y] in any case, by induction on [y].*)

Lemma ord_powa_same a b: ordinalp a -> ordinalp b ->
   a ^O b = a ^o b.
Proof.
move => oa ob.
case: (ord2_trichotomy oa); first by move => ->; apply: ord_powa_pr3.
  by move => ->; apply: ord_powa_pr4.
move => a2.
ex_middle bad0. 
pose p y := a ^O y = a ^o y.
have pb: ~ (p b) by [].
move:  (least_ordinal3 ob pb);
set y :=least_ordinal _ _; move => [oy py lpy]; case: py; rewrite /p.
case: (ordinal_limA oy) => ly.
    by rewrite ly; apply:  ord_powa_pr1.
  move: ly  => [t ot tx]; rewrite tx.
  have lty: t <o y by rewrite tx; apply: oltS.
  by rewrite (ord_powa_succ oa ot) (opow_succ oa ot) (lpy _ lty).
(** Let's show [a ^O y = a ^o y] when [y] is limit. By normality of the power
function the RHS is [C], the supremum of all [a ^o t] for [t < y].
Since [a ^o t = a ^O t], we have [C <= a ^O y] *)

rewrite (proj2 (opow_normal a2) _ ly).
have pa: forall t, inc t y ->  a ^O t = a ^o t.
  by move => t ty; apply lpy; apply/(oltP oy).
rewrite - (ord_sup_2funI pa).
have: union (fun_image y (ord_powa a)) <=o a ^O y.
  apply: ord_ub_sup.
    by apply: OS_ord_powa.
  move => i /funI_P [z zy ->]; apply: ord_powa_M_eqle => //.
  have [zy1 _] //: z <o y by  apply/(oltP oy).
  move => az; case: (oleNgt a2); rewrite az; exact: olt_02.
set C := \osup _.
move => le1; ex_middle ne1.
(** We assume, by contradiction [C < a ^O y]. Let [Gay] denote the set of 
graphs associated to [a ^O y], and let [f] be the order isomorphism.
Then [C = f(x)] for some [x]. This graph [x] takes almost everywehere the
minimal value [zz]; since [y] is limit, there is [c] with [c<y] and [t <= c]
implies [x(t) = zz]. *)
move: (proj32 le1) => op.
have lt1: inc C (a ^O y) by  apply /(oltP op); split => //; apply:nesym.
move: (ordinal_o_wor oa) (ordinal_o_wor oy)=> wora wory.
move: (ordinal_o_sr a) (ordinal_o_sr y) => sra sry.
move: (ordinal_o_is (olexp_worder wora wory)); rewrite -/(a ^O y).
move => [f isf]; move: (order_isomorphism_w isf) => morf.
move: isf => [or1 or2 [bf sf tf] sif].
move: tf; rewrite (ordinal_o_sr (a ^O y)) => tf.
move: sf;  rewrite(proj2 (olexp_osr wora wory)) => sf.
rewrite-  tf in lt1; move: ((bij_surj bf) _ lt1) => [x xsf fx].
move: (xsf); rewrite sf /olexp_G; move /Zo_P; rewrite sra sry.
move =>[xg fsx]; move: (xg) => /gfunctions_P2 [fgx dx rx].
set zz:= olexp_lE (ordinal_o a).
have[c cy cp]:
  exists2 c, inc c y & forall t, inc t (domain x) -> c <=o t -> Vg x t = zz.
  set ol := (olexp_I (ordinal_o a) (ordinal_o y) x).
  case: (emptyset_dichot ol) => ole.
     exists \0o;first by exact (proj32 ly).
     move => t tdx _; ex_middle bad.
     by empty_tac1 t; apply: Zo_i => //; rewrite sry - dx.
  have sol: sub ol (substrate (ordinal_o y)) by apply: Zo_S.
  move: (finite_subset_torder_greatest (worder_total wory) fsx ole sol).
  move => [c []]; rewrite (iorder_sr (proj1 wory) sol).
  move => col cleast.
  move: (sol _ col); rewrite sry => cy; move: ((proj33 ly) _ cy) => scy.
  ex_tac; move => t tdx st.
  have ct: c <o t by  apply /oleSltP.
  case: (inc_or_not t ol) => tol.
    move: (iorder_gle1 (cleast _ tol)) => /ordo_leP [_ _ tc].
    by move: ct => [[_ _ ca] cb]; case: cb; apply: extensionality.
  by ex_middle nv; case: tol; apply: Zo_i => //; rewrite sry -dx.
(** Let [Gac] denote the set of graphs associated to [a ^O c], and let [g] be 
the order isomorphism, from  [a ^O c] to [Gac]. Let [h] be the function  that 
extens a graph by assigning [zz]. It maps the target of [g] to the source of
[f]. It is clearly injective; it is an order morphism. Any functional graph that
is zero above [c] is in the range of [h]. *)
move: (Os_ordinal oy cy) => oc.
move: (ordinal_o_wor oc) => worc.
move: (orderIS (ordinal_o_is (olexp_worder wora worc))); rewrite -/(a ^O c).
move => [g isg]; move: (order_isomorphism_w isg) => morg.
move: isg => [or3 or4 [bg sg tg] sig].
move: tg;  rewrite (proj2(olexp_osr wora worc)) => tg.
move: (OS_ord_powa oa oc) => op'.
move: (ordinal_o_sr c) => src.
move: sg; rewrite (ordinal_o_sr (a ^O c)) => sg.
pose h t := Lg y (fun u => (Yo (inc u c) (Vg t u) zz)).
have ne2: nonempty (substrate (ordinal_o a)). 
 move: (olt_leT olt_02 a2) => /(oltP oa);rewrite sra => he;ex_tac.
move: (olexp_lEp wora ne2); rewrite -/zz sra;  move => [zza zzp].
have scy: sub c y.
  move => t tc;  apply: (ordinal_transitive oy cy tc).
have hp1: forall t, inc t (target g) -> inc (h t) (source f).
  move => t; rewrite sf tg =>/Zo_P; rewrite sra src; move => [t1 t2].
  apply /Zo_P; rewrite sra sry; move: t1 => /gfunctions_P2 [ft dt rt].
  split.
     apply /gfunctions_P2; rewrite /h; aw; split;fprops =>s.
     move => /Lg_range_P [b0 b0y ->]; Ytac bc => //; apply: rt. 
     apply /(range_gP ft); rewrite dt; ex_tac.
  move: t2; rewrite /olexp_I src sry; set e1 := Zo _ _ ; set e2 := Zo _ _.
  have -> //: e1 = e2.
    set_extens u => /Zo_P [uc sv]; apply /Zo_P.
      by move: (scy _ uc) => uy; split => //; rewrite /h LgV//; Ytac0.
    move: sv; rewrite /h LgV//; Ytac uu => //.
set hf:= Lf h (target g) (source f).
have injh: injection hf.
   apply: lf_injective => // u v usg vsg sv.
   move: usg vsg; rewrite tg /olexp_G src sra => /Zo_P [] /gfunctions_P2. 
   move => [gru du _] _  /Zo_P [] /gfunctions_P2 [grv dv _] _.
   apply: fgraph_exten => //; first (by ue); rewrite du => s sc.
   move: (scy _ sc) => sy.
   by move: (f_equal (Vg ^~s) sv); rewrite /h ! LgV//; Ytac0; Ytac0.
have monh: order_morphism hf (olexp (ordinal_o a) (ordinal_o c)) 
   (olexp (ordinal_o a) (ordinal_o y)).
  apply: total_order_morphism; try exact.
        by apply: worder_total; apply: olexp_worder.
      by rewrite /hf; aw; rewrite tg (proj2 (olexp_osr _ _)).
    by rewrite /hf; aw; rewrite sf (proj2 (olexp_osr _ _)).
  rewrite /hf; aw => u v  ush vsh; rewrite !LfV//.
  move/(olexp_gleP wora worc) => [us1 vs1 cuv]; apply/(olexp_gleP wora wory).
  move: (hp1 _ ush) (hp1 _ vsh); rewrite - sf => us2 vs2.
  split; [exact | exact | case: cuv ; first by move => ->; left].
  rewrite src sry; move => [j [jc ja jb]]; right;exists j.
  move: (scy _ jc) => jy.
  split; [exact | by rewrite /h !LgV//; Ytac0; Ytac0 |].
  move => i []/sub_gleP [_ iy ji] nji.
  rewrite /h !LgV//; Ytac ic; Ytac0; last by exact.
  by apply: jb; split => //; apply  /sub_gleP.
have hbounded: 
    forall x', inc x' (source f) -> 
       (forall t : Set, inc t (domain x') -> c <=o t -> Vg x' t = zz) ->
      (inc (restr x' c) (target g) /\ (Vf hf (restr x' c) = x')).
  move => w.
  rewrite  sf /olexp_G => /Zo_P; rewrite sra sry.
  move =>[wg fsw] cp'; move: (wg) => /gfunctions_P2 [fgw dw rw].
  have scdx: sub c (domain w) by ue.
  have fgr: fgraph (restr w c) by fprops.
  have rg: inc (restr w c) (target g). 
    rewrite tg; apply Zo_i. 
    rewrite src sra; apply /gfunctions_P2; saw.
    move => t /(range_gP fgr); aw; move => [u uc ->]; rewrite LgV//; apply: rw. 
    apply /(range_gP fgw); exists u;fprops.
    move: fsw; rewrite /olexp_I sry src; apply: sub_finite_set.
    move => s /Zo_P [sc vnz]; apply: Zo_i; first by apply: scy.
    move: vnz; rewrite LgV//.
  split; [by exact | rewrite /hf /h LfV //; apply: fgraph_exten; aww].
  move => s sy /=; rewrite(LgV sy); Ytac sc; first by rewrite LgV//; ue. 
  symmetry; apply: cp'; [ue |case: (oleT_el oc (Os_ordinal oy sy))=>//].
  by move /oltP0 => [_ _].
(** Let's compose these three morphisms. We get a morphism. Since the image of 
[h] is segment, so is the image of the composition *)
move:  (compose_order_morphism morg monh) => morgh.
move:  (compose_order_morphism morgh morf).
set oac:= (ordinal_o (a ^O c)).
set oay:= (ordinal_o (a ^O y)).
set fgh:= f \co (hf \co g) => morfhg.
have chg: hf \coP g by split => //; try fct_tac; rewrite /hf; aw.
have cfhg: f \coP (hf \co g) by split => //; try fct_tac; rewrite /hf; aw.
have srh: segmentp oay (Imf fgh).
  red; move: morfhg => [_ _ [ffgh _ _] _]; rewrite (ordinal_o_sr ((a ^O y))).
  split; first by move:(Imf_Starget ffgh); rewrite {2} /fgh -tf; aw.
  move => u v; case: (equal_or_not u v); [by move => -> | move => unv].
   rewrite /fgh; move /(Imf_P ffgh); rewrite /fgh; aw.
   move=> [u3 usg3 uv] lvu; apply /(Imf_P ffgh).
  have vtf: inc v (target f).
     move: lvu => /sub_gleP [ok _]; ue.
  move: (bij_surj bf vtf) => [v1 v1df v1f].
  set u2 := (Vf g u3); set u1 := Vf hf u2.
  have u2tag: inc u2 (target g) by rewrite /u2; Wtac; fct_tac.
  have u1sf: inc u1 (source f). 
    have ->: source f = target hf by rewrite /hf; aw.
    rewrite /u1; Wtac; [fct_tac | by rewrite /hf; aw ].
  have aux: inc u3 (source (hf \co g)) by aw.
  have hh: gle (olexp (ordinal_o a) (ordinal_o y)) v1 u1 <-> gle oay v u.
    rewrite /oay v1f uv (compfV cfhg aux) (compfV chg usg3). 
    exact:(sif _ _ v1df u1sf).
  have unv1: u1 <> v1. 
    dneg u1v1; rewrite v1f -u1v1 uv ! compfV //.
  move /hh: lvu => /(olexp_gleP wora wory).
  move => [v1g u1g]; case; first by move => hh1; case: unv1.
  move => [j [jsy cuvj cuvgj]].
  have cp': (forall t, inc t (domain v1) -> c <=o t -> Vg v1 t = zz).
    move: v1g =>/Zo_P []; rewrite sra sry => /gfunctions_P2 [fgv dv rv] fsv.
    move: u1g =>/Zo_P []; rewrite sra sry => /gfunctions_P2 [fgu du ru] fsu.
    move => t td1 ct.
    have sa: forall s, inc s y -> c <=o s -> Vg u1 s = zz.
      move => s sd sv; rewrite /u1 /hf /h LfV// LgV//; Ytac sc; last by exact.
      by move/(oltP oc): sc => /(oleNgt sv).
    move: jsy;  rewrite sry => jy.
    case: (oleT_el oc (Os_ordinal oy jy)) => ccj.
      move : cuvj; rewrite (sa _ jy ccj).
      have va: inc (Vg v1 j) a. 
        apply: rv; apply /(range_gP fgv); rewrite dv; ex_tac.
      move: wora (zzp _ va) => [ora _ ] la lb; order_tac.
    have : inc j t by apply/  (oltP  (proj32 ct)); exact (olt_leT ccj ct).
    rewrite dv in  td1; move /(ordo_ltP oy jy td1) => h1.
    by rewrite (cuvgj _ h1); apply: sa.
  move: (hbounded _ v1df cp') => [vtg v1v].
  move: (bij_surj bg vtg) => [w wdg wv]. 
  exists w; rewrite /fgh ? compfV//; aww.
  by rewrite -wv v1v v1f.
(** We have [ a ^O c <= C] by definition of [C]. 
It follows [ a ^O c <o a ^O y] and [f (h (g (s))) = s] for any [s].
We have [C = f (h (g (s)))] for some [s] in [a ^O c]. Thus [C < a ^O c]. absurd.
*)
move: (hbounded _ xsf cp) => [rsx1 hfz].
move: (bij_surj bg rsx1); rewrite  sg.
move => [s sa sv].
have sg1: inc s (source g) by rewrite  sg.
have ltc: a ^O c <=o C.
   have os1: ordinal_set (fun_image y (ord_powa a)).
     move => t /funI_P [z zy ->]; apply: OS_ord_powa => //. 
       exact: (Os_ordinal oy zy).
   apply: ord_sup_ub => //; apply /funI_P;ex_tac.
have ltaC: C <o a ^O y by split => //; apply:nesym.
have ltacay := ole_ltT ltc ltaC.
move: (inclusion_morphism_b ltacay srh morfhg sa) ltc.
rewrite /fgh ! compfV//; aw; trivial;rewrite - sv hfz fx => ->.
by move: sa => /(oltP op') ta /(oltNge ta).
Qed.


(** remaining exercises of the section in main text *)


(** Bourbaki says in exercise 14d: _it is the greatest element of the union of 
[singleton alpha] and the set of the [xi(iota)]_, where _it_ denotes [alpha],
the supremum of the family  [xi(iota)]. 
Note that this property holds for any upper bound, thus does not 
   characterize the supremum *)
Lemma ord_sup_pr6  E: ordinal_set E ->
  greatest (ole_on (E +s1 (\osup E))) (\osup E).
Proof.
move=> Ep; move: (OS_sup Ep) => os. 
have ee: ordinal_set (E +s1 (union E)). 
  move => y; case/setU1_P;[apply: Ep | move=> ->; exact].
move: (wordering_ole_pr ee) => [p0 p1].
red; aw. rewrite p1;split; first by fprops.
move => x xt; apply /graph_on_P1;split;fprops.
move: xt; case /setU1_P; first by apply: ord_sup_ub =>//.
by move => ->; fprops.
Qed.


(** ** Section 3 *)

(**  Exercise 3.1 This is Cantor-Bernstein *)

Lemma Exercise3_1 E F f g:
  function_prop f E F -> function_prop g F E -> injection f -> 
  exists A A', 
    [/\ sub A E, sub A' F, Vfs f A = A' & Vfs g (F -s A') = E -s A].
Proof.
move=>  [ff sf tf] [fg sg tg] [_ injf].
rewrite - sg -tg.
set R := (source g) -s (Vfs f (target g)).
pose p M:= [/\ sub M (source g), sub R M &
   forall x, inc x M -> inc (Vf f (Vf g x)) M].
have pE: p (source g). 
  split => //; first by  rewrite /R; apply: sub_setC.
  move => x xE; rewrite sg -tf; Wtac.
  rewrite sf -tg; apply: Vf_target => //.
set Z:= Zo (\Po (source g)) p.
have EZ: inc (source g) Z by apply: Zo_i; aw;trivial;apply: setP_Ti.
have neZ: nonempty Z by exists (source g).
set B':= intersection Z; set B := Vfs g B'.
have p1: sub R B'.
  by move=> t tR; apply: setI_i => // y  /Zo_hi  [_ p1 _]; apply: p1.
have p2: forall x, inc x B' -> inc (Vf f (Vf g x)) B'.
  move => x xB'; apply: setI_i => // y yZ; move: (yZ) => /Zo_P.
  by move => [ _ [_ _]]; apply; apply: setI_hi yZ.
have sBF: sub B' (source g) by apply: (setI_s1 EZ).
have aux:sub (target g) (source f) by rewrite sf -tg; fprops.
have p3:forall x, inc x B' -> 
  inc x R \/ exists2 y, inc y B' & x= (Vf f (Vf g y)).
  move=> x xB'; case: (inc_or_not x R) => xR; first by left.
  have xsg: inc x (source g) by apply: sBF.
  case: (inc_or_not x (Vfs f (target g))); last first.
    move => h; case: xR; apply /setC_P;split => //.
  move=> /(Vf_image_P ff aux) [u [utg Wu]].
  set C := B' -s1 x; case: (inc_or_not C Z) => CZ.
    by move: (setI_hi xB' CZ)=> /setC_P [_] /set1_P.
  have pA: sub C (source g).
    by apply: (@sub_trans B') =>//; apply: sub_setC.
  have pB: inc C (\Po (source g)) by apply /setP_P.
  have pC:sub R C by move => t tR; apply/setC1_P;split;fprops=> tx;case: xR; ue.
  right; ex_middle hyp.
  case: CZ; apply /Zo_P;split => //; split => //; move => v /setC1_P [vB' vx].
  apply /setC1_P;split; [by apply: p2 | move=> aux2; case: hyp; ex_tac].
have sBE: sub B (target g).
  move =>  t /(Vf_image_P fg sBF) [u uA ->]; Wtac.
set A':= (source g) -s B'.
have AF: sub A' (source g) by apply: sub_setC.
set A := (target g) -s B.
have AE: sub A (target g) by apply: sub_setC.
exists A; exists A'; split => //; last by rewrite /A' /A  !setC_K //.
rewrite /A/A'.
rewrite tg - sf in AE.
set_extens t.
  move /(Vf_image_P ff AE)=> [u] /setC_P [utf hh] ->; apply /setC_P;split => //.
     rewrite sg -tf; Wtac.
  dneg Wa; case: (p3 _ Wa). 
    move => /setC_P [_] /(Vf_image_P ff aux); case; ex_tac.
  move=> [y yB' ww]. 
  have wF: inc (Vf g y) (target g) by apply: Vf_target => //; apply: sBF.
  rewrite tg - sf in utf wF;rewrite (injf _ _ utf wF ww).
  apply /(Vf_image_P fg sBF); ex_tac.
move => /setC_P[tsf ntA]. 
case: (inc_or_not t R) => tR; first by case: ntA; apply: p1.
have dn: forall (P Q: Prop), P -> ~ (P /\ ~ Q) -> Q.
  move=> P Q nP npq; case: (p_or_not_p Q) => nQ //;case: npq;split => //.
move: tR => /setC_P => aux2; move: (dn _ _ tsf aux2).
move=> /(Vf_image_P ff aux)  [u usg Wu]; case: (inc_or_not u B) => uB.
   move: uB => /(Vf_image_P fg sBF) [v vA Wv]; case: ntA.
  by rewrite Wu Wv; apply: p2.
apply  /(Vf_image_P ff AE); exists u => //; apply /setC_P;split => //.
Qed.

Lemma Exercise3_1b E F f g:
  function_prop f E F -> function_prop g F E -> injection g -> 
  exists A A', 
    [/\ sub A E, sub A' F, Vfs f A = A' &  Vfs g (F -s A') = E -s A].
Proof.
move=>  fp1 fp2 ig; move: (Exercise3_1 fp2 fp1 ig). 
move=> [A0 [A1 [pa pb pc pd]]].
exists (E -s A1); exists (F -s A0).
split => //; try apply: sub_setC; rewrite  !setC_K //.
Qed.

(** ---- Exercise 3.2. 
Let [EF] denote the set of functional graphs [E->F] and [EF'] the cardinal
of this set. We show that [EF = FE] implies [E=F]. We give a non-trivial example
where [EF'=FE'];  this shows that one of [EF] and [FE] is not a cardinal. 
Bourbaki deduces: using the same notation for [EF] and [EF'] is an abuse of 
notations. 

Using von Neumann ordinals gives a stronger result:
[EF] is an ordinal (and a fortiori a cardinal) only if one
of the two arguments is empty.
 *)

Lemma Exercise3_2a E F:
 gfunctions E F = gfunctions F E -> E = F.
Proof.
move=> sEF.
have pe: forall x E F, inc x F -> inc (cst_graph E x) (gfunctions E F).
  move => x a b xb; rewrite /gfunctions; aw.
  apply: Zo_i.
    by apply /setP_P; move => t /funI_P  [z za ->]; apply:setXp_i.
   rewrite /cst_graph; split;aww.
case: (emptyset_dichot E) => eE.
  case: (emptyset_dichot F) => eF; first by ue.
  move: eF => [x xE]; move: (pe x E F xE); rewrite sEF.
  by move => /Zo_P [_]; aw; move => [_ <-].
move: eE => [x xE]; move: (pe x F E xE); rewrite - sEF.
by move => /Zo_P [_]; aw; move => [].
Qed.
  
Lemma Exercise3_2b: 
  let E := \2c in let F := \4c in 
  let s1 := gfunctions E F in let s2 :=gfunctions F E in
  ~ (cardinalp s1) \/ ~ (cardinalp s2).
Proof.
move=> E F s1 s2.
case: (p_or_not_p (cardinalp s1)) => cs1; last by left.
case: (p_or_not_p (cardinalp s2)) => cs2; last by right.
move: (Eq_fun_set E F) (Eq_fun_set F E).
move /card_eqP; rewrite -/s1 (card_card cs1) -/(F ^c E) => pa.
move /card_eqP; rewrite -/s2 (card_card cs2) -/(E ^c F) => pb.
move: pa pb; rewrite /E /F cpow_24 => -> /Exercise3_2a rq.
by case: (proj2 clt_24).
Qed.

Lemma Exercise3_2c E F:
  ordinalp (gfunctions E F) -> E = emptyset \/ F = emptyset.
Proof.
move=>  bo; set T:= gfunctions E F.
case: (emptyset_dichot F) => Fe; [ by right | left].
case: (equal_or_not emptyset T) => Te.
  move: Fe => [y yF];empty_tac1 (cst_graph E y).
  apply: Zo_i.
    by apply /setP_P => t /funI_P [z za ->]; apply:setXp_i.
  rewrite /cst_graph; split;aww.
have: emptyset <o T by split => //; apply: (ole0x bo). 
by move /oltP0 => [_ _] /Zo_hi  [_];rewrite domain_set0.
Qed.

(** Exercise 3.3 is Koenig's Theorem  *)

(** ---- Exercise 3.4. Let [E] be a set, [f: P(E)-> E] be a choice function.
We must show two statements. We proove the first in some trivial cases.
The two remain TODO.
*)

Section Exercise34.
Variable E: Set.
Variable f: Set -> Set.
Hypothesis choice: forall X, sub X E -> nonempty X -> inc (f X) X.
Definition finv x := Zo (\Po E) (fun z => f z = x).

Lemma Exercise34a b: cardinalp b -> 
  let A := Zo E (fun x => (cardinal (finv x)) <=c b) in
  let a := cardinal A in 
  (\2c ^c a) <=c (csucc (a *c b)).
Proof.
move=> cb A a.
move: (csucc_pr2 (setP_0i A)); rewrite card_setP - cpowcr =>->.
set A' := \Po A -s1 emptyset; apply: cleSS.
pose Ap x := Zo A' (fun z => f z = x). 
pose Af := Lg A Ap.
have md: mutually_disjoint Af.
  rewrite /Af; apply: mutually_disjoint_prop; aw => i j t iA jA.
  by rewrite !LgV//;move => /Zo_P [_ <-] /Zo_P [_ <-].
have daf: domain Af = A by rewrite /Af; aw.
have AE: sub A E by apply: Zo_S.
move:(csum_pr4 md).
have ->: unionb Af  = A'.
  set_extens t;first by  move/setUb_P =>[y]; rewrite daf /Af => yA; rewrite LgV// => /Zo_S.
  move => ta; move: (ta) => /Zo_P [/setP_P sY].
  case: (emptyset_dichot t); first by move ->; case; fprops.
  move => net _; move: (choice (sub_trans sY AE) net) => ftt.
  apply/setUb_P; rewrite daf; move: (sY _ ftt) => h; ex_tac.
  by rewrite /Af LgV//; apply/Zo_P.
move ->.
rewrite  /a cprod2cl  cprodC -(csum_of_same) daf /Af. 
apply: csum_increasing; aw;  trivial  => y yA; rewrite !LgV//.
move /Zo_P: yA => [_]. apply: cleT; apply: sub_smaller.
move => t /Zo_P [/setC1_P [/setP_P ta _] ft]; apply/Zo_P; split => //.
by apply/setP_P; apply: (sub_trans ta AE).
Qed.

Lemma Exercise34b b: cardinalp b -> 
  let B := Zo E (fun x => forall X, inc X (finv x) -> nonempty X ->
        cardinal X <=c b) in
  cardinal B <=c b.
Proof.
set B := Zo _ _ => cp /=.
case: (emptyset_dichot B).
  by move ->; rewrite cardinal_set0; apply: cle0x.
move => neb.
have BE: sub B E by apply: Zo_S.
move: (choice BE neb) => /Zo_P [ha hb]; apply: hb => //.
by apply /Zo_P; split => //; apply/setP_P.
Qed.


End Exercise34.

(** ---- Exercise 3.5. Cardinal of an ordinal sum and product *)

Definition fam_card_sub f := 
  (Lg (domain f) (fun z => cardinal (substrate (Vg f z)))).

Lemma Exercise3_5a r f: orsum_ax r f ->
  cardinal (substrate (order_sum r f)) = csum (fam_card_sub f).
Proof.
move=> osa.
rewrite orsum_sr // /sum_of_substrates  /fam_card_sub .
by apply:csum_pr3; aw; trivial => i idf; rewrite !LgV//; aw.
Qed.

Lemma Exercise3_5b r f: orprod_ax  r f ->
  cardinal (substrate (order_prod r f)) = cprod (fam_card_sub f).
Proof.
move=> rosa.
rewrite orprod_sr // /prod_of_substrates /fam_card_sub -/(cprod _).
rewrite 2! cprod_pr; aw;apply: cprodb_exten =>  i idf /=.
by rewrite !LgV//; aw.
Qed.

Lemma Exercise3_5c r f h: orsum_ax r f -> 
  h \Is (order_sum r f) ->
  cardinal (substrate h) =  csum (fam_card_sub f).
Proof.
move=> oa [g [o1 o2 [bg sg tg] _]].
by rewrite - (Exercise3_5a oa) - sg - tg; apply /card_eqP; exists g.
Qed.

Lemma Exercise3_5d r f h: orprod_ax  r f -> 
  h \Is (order_prod r f) ->
  cardinal (substrate h) =  cprod (fam_card_sub f).
Proof.
move=> oa [g [o1 o2 [bg sg tg] _]].
by rewrite - (Exercise3_5b oa) - sg - tg; apply /card_eqP; exists g.
Qed.

Lemma Exercise3_5e r g:
  worder_on r (domain g) -> ordinal_fam g ->
  cardinal (osum r g) = 
    csumb (domain g) (fun z => cardinal (Vg g z)).
Proof.
move=> [wo sr] ofg;move: (ofg) => alo.
rewrite /osum; set h := Lgcomp _ _.
have hp1: forall i,  inc i (domain g) -> worder (Vg h i).
  rewrite /h=> i idg; rewrite LgV//; apply: ordinal_o_wor; apply: (alo _ idg).
have wos: worder (order_sum r h).
   rewrite /h;apply: orsum_wor => //; aww. 
     by split.
   by hnf; aw.
move: (ordinal_o_is wos) => xx.
have or: order r by fprops.
have oa:(orsum_ax r h).
  rewrite /h;split => //;aw; hnf; aw; trivial.
  move=> i idg; move: (hp1 _ idg). 
  by rewrite /h; aw; move=> [ok _].
move: (orderIS xx)=> xx1;move: (Exercise3_5c oa xx1).
move: (OS_sum (conj wo sr) ofg) => r1.
rewrite ordinal_o_sr  /osum /fam_card_sub; move => ->. 
rewrite /h; aw; apply: f_equal; apply: Lg_exten; move=> i idg /=.
by rewrite LgV// ordinal_o_sr //; apply: (alo _ idg).
Qed.

Lemma Exercise3_5f r g:
  worder_on r (domain g) -> ordinal_fam g ->
  finite_set (substrate r) ->
  cardinal (oprod r g) = 
    cprodb (domain g) (fun z => cardinal (Vg g z)).
Proof.
move=> wosr ofg fsr; move: (ofg) => alo; move: (wosr) => [wo sr].
rewrite /oprod; set h := Lgcomp _ _.
have hp1: forall i,  inc i (domain g) -> worder (Vg h i).
  rewrite /h=> i idg;rewrite LgV//; apply: ordinal_o_wor; apply: (alo _ idg).
have wos: worder (order_prod r h).
  by rewrite /h;apply: orprod_wor => //=;aw; fprops; hnf; aw.
move: (ordinal_o_is wos) => xx.
have oa:(orprod_ax r h).
  rewrite /h;split => //; hnf; aw; trivial; move=> i idg.
  by move: (hp1 _ idg); rewrite /h; aw;  move=> [ok _].
move: (orderIS xx)=> xx1;move: (Exercise3_5d oa xx1).
move: (OS_prod wosr ofg fsr) => r1.
rewrite (ordinal_o_sr (oprod r g));rewrite /oprod /fam_card_sub => ->.
rewrite /h; aw; apply: f_equal; apply: Lg_exten; move=> i idg /=; rewrite LgV//.
by rewrite ordinal_o_sr //; apply: (alo _ idg).
Qed.


(** Exercise 3.6. Every set contains a subset that is not an element. 
Proof 1: by Cantor. Proof 2: the set of elements of [E] that are not elements
of itself is not an element of [E].  
 *)
Lemma Exercise3_6 E: exists X, sub X E /\ ~ (inc X E).
Proof.
ex_middle bad.
have  bad1: sub (\Po E) E.
  by move=> t /setP_P tE; ex_middle te1; case: bad; exists  t.
have eq1: \2c ^c  (cardinal E) = cardinal (\Po E).
  by rewrite card_setP; apply: cpow_pr; aw.
move: (cantor (CS_cardinal E)); rewrite eq1=> le1.
by move: (cltNge le1 (sub_smaller bad1)).
Qed.

Lemma Exercise3_6b E: let X:=  Zo E (fun t => ~(inc t t)) in
  sub X E /\ ~ (inc X E).
Proof.
move=> U; split;first by apply: Zo_S.
move=> UE.
have nUU: ~ inc U U by move => h;case: (Zo_hi h).
by case: (nUU); apply: Zo_i.
Qed.


Lemma Exercise3_6c E:   {X | sub X E /\ ~ (inc X E) }.
Proof.
exists (Zo E (fun t => ~(inc t t))).
apply: Exercise3_6b. 
Qed.

End Exercise3.
Export Exercise3.

