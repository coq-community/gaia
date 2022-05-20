(** * Theory of Sets : Ordinals
  Copyright INRIA (2018) Marelle Team (Jose Grimm).
*)

(* $Id: sset16c.v,v 1.5 2018/09/04 07:58:00 grimm Exp $ *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From gaia Require Export sset15.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Infinite sums of ordinals *)

Module InfiniteOsum.

  
(* a small lemma about indecomposable ordinals *)
  
Lemma indecomp_sier a b c: ordinalp a -> indecomposable c -> b <o c ->
   b +o a +o c = a +o c.                             
Proof.
move => oa ic lbc.
have ob := proj31_1 lbc.
have oc := (proj32_1 (proj1 ic)).
case: (ozero_dichot ob)=> bp; first by rewrite bp (osum0l oa).
move: (oquoremP oa bp); set q := oquo _ _; set r := orem _ _.
move=>[oq or dv rs].
case: (oleT_el OS_omega oq) => lt1.
  move: (oleT (oprod_Meqle lt1 ob) (osum_Mle0 (OS_prod2 ob oq) or)).
  by rewrite - dv; move/(ord_negl_alt ob oa) => ->.
have H := (OS_prod2 ob oq).
rewrite - (osumA ob oa oc) dv - (osumA H  or oc).
rewrite (indecomp_prop1 ic (olt_ltT rs lbc))(osumA ob H oc)(oprod2_nsucc ob oq).
have ->: \1o +o q = osucc q.
  move/(oltP OS_omega): lt1 => qN. rewrite - (succ_of_nat qN) (Nsucc_rw qN).
  by rewrite (osum2_2int NS1 qN) csumC.
by rewrite (oprod2_succ ob oq) - (osumA H ob oc) (indecomp_prop1 ic lbc).
Qed.

Definition is_rem_of x b := 
  (\0o <o b /\ exists2 a, ordinalp a & x = a +o b).
Definition least_rem x :=  least_ordinal (is_rem_of x) x.


Lemma least_rem_p0 x: ~(\0o <o x) -> (least_rem x) = \0o. 
Proof.
move => bad; rewrite /least_rem /least_ordinal; set E := Zo _ _. 
case: (emptyset_dichot E);first by  move ->; rewrite setI_0.
move=>[c] /Zo_P [qa [[[_ oc _] /nesym cnz] [b ob xv]]]; case: bad; rewrite xv.
case: (ozero_dichot (OS_sum2 ob oc)) => // /(osum2_zero ob oc); case => //.
Qed.

Lemma least_rem_prop x (b:= least_rem x): \0o <o x ->
   [/\ ordinalp b, is_rem_of x b &
     forall z, ordinalp z -> is_rem_of x z -> b <=o z].
Proof.
move => h; move: (proj32_1 h) => ox.
have px: is_rem_of x x.
  by  split => //; exists \0o; [ apply: OS0 | rewrite osum0l].
exact: (least_ordinal4 ox px). 
Qed.

Lemma OS_least_rem x: ordinalp (least_rem x).
Proof.
case: (p_or_not_p (\0o <o x)) => h.
 by case (least_rem_prop h).
rewrite (least_rem_p0 h); apply: OS0.
Qed.
  
Lemma least_rem_p1 x (b:= least_rem x): \0o <o x ->
  \0o <o b /\ exists2 a, ordinalp a & x =   a +o b.
Proof. by move /least_rem_prop; case. Qed.


Lemma least_rem_p2 x a b: \0o <o x -> x = a +o b -> 
  ordinalp a -> ordinalp b ->
  b = \0o \/ least_rem x <=o b.
Proof. 
move => /least_rem_prop [ha hb hc] xv oa ob.
case: (ozero_dichot ob); [by left | move => bp; right; apply: (hc _ ob)].
by split => //; exists a.
Qed.

Lemma least_rem_p3 x: \0o <o x ->  indecomposable (least_rem x).
Proof.
move => xp; move: (least_rem_p1 xp) => [lp [a oa av]].
split => // u v lub lvb eq.
move: (proj31_1 lub) (proj31_1 lvb) => ou ov.
move: av; rewrite - eq (osumA oa ou ov)=> eq1.
case:(least_rem_p2 xp eq1 (OS_sum2 oa ou) ov) => dv.
  by case: (proj2 lub); rewrite - eq dv (osum0r ou).
by case: (oltNge lvb).
Qed.

Lemma least_rem_p4 x b : indecomposable x -> is_rem_of x b -> b = x.
Proof.
move => ix [lp [a oa xv]].
case: (indecomp_pr  oa (proj32_1 lp) ix (esym xv)) => // eax.
by move: (osum_Meqlt lp oa); rewrite (osum0r oa) - xv  eax; case.
Qed.

Lemma least_rem_p5 x: indecomposable x -> least_rem x = x.
Proof.
move => ix; exact: (least_rem_p4 ix (least_rem_p1 (proj1 ix))). 
Qed.

Lemma least_rem_p6 x c: \0o <o x ->  is_rem_of x c -> indecomposable c ->
  c = (least_rem x).
Proof.
move => cp; move: c.
pose p y :=  \0o <o y -> 
 forall c, is_rem_of y c -> indecomposable c -> c = least_rem y.
move: (proj32_1 cp) => ox; move: cp. 
case:(least_ordinal6 p ox) => //; set y := least_ordinal _ _.
move => [oy yleast]; case => yp.
move:(CNFr_exists_aux yp) =>[n [r [on lry _ yv2]]].
have oon := (OS_oopow on).
have or := (proj31_1 lry).
move: (indecomp_prop4 on) => iT.
case: (ozero_dichot or) => rz.
  move: yv2 iT; rewrite rz (osum0r oon) => <- iy.
  move => c cp ic. 
  by rewrite (least_rem_p4 iy cp) (least_rem_p5 iy).
have nyi: ~ indecomposable y.
  move: (osum_Meqlt rz oon); rewrite (osum0r oon) - yv2 => la.
  by move =>[_ h];move: (h _ _ la lry); rewrite - yv2; case.
have H c :is_rem_of y c -> indecomposable c -> c = least_rem r.
  move => [cp [a oa yv1]] ic; move: (proj32_1 cp) => oc.
  case: (oleT_el oon oa) => coa.
    move:(odiff_pr coa); set a' := _ -o _; move => [oa' eq2].
    have eq3: oopow n +o (a' +o c) = oopow n +o r.
      by rewrite (osumA oon oa' oc) - eq2 - yv2 - yv1.
    move:(osum2_simpl (OS_sum2 oa' oc) or oon eq3) => eq4.
    have rc: is_rem_of r c by split => //; exists a'.
    have: inc r y by apply/oltP.
    move/yleast => pr; exact: (pr rz c rc ic). 
  case: nyi.
  move:(ord_negl_opow coa on) => na.
  move:(ord_negl_sum oa oon or na).  
  rewrite - yv2 yv1 => /(ord_neg_sum4 oa (proj32_1 cp)).
  by rewrite/ord_negl - yv1 => ->.
move => c ca cb; rewrite (H c ca cb).
by rewrite (H _ (least_rem_p1 yp) (least_rem_p3 yp)).
Qed.

Lemma least_rem_p7  a b: ordinalp a -> \0o <o b ->
  least_rem (a+o b) = least_rem b.
Proof.
move => oa bp.
move:(least_rem_p1 bp)(least_rem_p3 bp); set c := least_rem b.
move =>[cp [u ou bv]] ic.
have oc := proj32_1 cp.
have ha: is_rem_of (a +o b) c. 
  by split => //; exists (a +o u); fprops; rewrite - (osumA oa ou oc) - bv.
by move:(least_rem_p6 (ord_gt_pos (osum_Meqlt bp oa)) ha ic).
Qed.



Lemma osup_U1 E x: ordinal_set E -> ordinalp x  ->
  \osup (E +s1 x) = omax (\osup E) x.
Proof.
move => ose ox.
have osu: ordinal_set (E+s1 x).
   by move => t /setU1_P; case; [ move/ose | move ->].
have os:= (OS_sup ose).
move: (omax_p1 os ox) => [qa qb].
apply: oleA.
  apply: (ord_ub_sup (proj32 qb)) => t /setU1_P; case => h; last by ue.
  by apply: oleT qa; apply:ord_sup_ub.
apply: (omax_p0); last by apply: (ord_sup_ub osu); fprops.
by apply: ord_sup_M osu; apply:sub_setU1.  
Qed.


Lemma osup_Un E F p: ordinal_set E -> sub F E -> finite_set F ->
  (forall x, inc x E -> x <o p) ->
  p = \osup E -> p = \osup (E -s F).
Proof.
move => ose sfe fse Ep -ea.
move: F fse sfe; apply: finite_set_induction.
  by rewrite setC_0.
move => F x Hr.
case: (inc_or_not x F) => xF; first by rewrite (setU1_eq xF). 
move => h.
have xE:= (h x (setU1_1 F x)).
have /Hr: sub F E by move => t tt; exact: (h _ (setU1_r x tt)).
set G := (E -s (F +s1 x)).
have ->: (E -s F) = G +s1 x.
  set_extens t.
    move => /setC_P  [te tf]; case: (equal_or_not t x) => tx.
       rewrite tx; fprops.
    by apply: setU1_r; apply/setC_P; split => // /setU1_P; case.
  case/setU1_P.    
    move => /setC_P [tE /setU1_P h1]; apply /setC_P; split => // yf.
    by case: h1; left.
  by move ->; apply/setC_P.
have osg: (ordinal_set G) by move => t /setC_P/proj1/ose.
have ox: ordinalp x by apply:ose.
rewrite (osup_U1 osg ox) /omax/Gmax; Ytac aux => // px.
by case: (nesym (proj2(Ep _ xE))).
Qed.

Lemma funU_setC A B f (C := (fun_image A f) -s (fun_image (A -s B) f)):
  fun_image (A -s B) f = (fun_image A f) -s C /\
  (finite_set B -> finite_set C).
Proof.
have ha: sub (fun_image (A -s B) f) (fun_image A f).
  by move => t /funI_P[x /setC_P[xoi _]-> ]; apply: funI_i.
split; first  by rewrite /C setC_K.
move => h.
have hb: sub C (fun_image B f).
  move => t /setC_P- [/funI_P [i iA ->] ic].
  case: (inc_or_not i B); first by apply: funI_i.
  by move => ntb; case: ic; apply: funI_i; apply/setC_P.
by apply: (sub_finite_set hb); apply: finite_fun_image.
Qed.


Lemma sub_nat_isomorphism A (r := induced_order Nat_order A) : sub A Nat ->
  (finite_set A -> exists2 n, natp n &  r \Is induced_order Nat_order n) /\
  (~ finite_set A -> r \Is Nat_order).
Proof.
move => sub1.
move:Nat_order_wor => [wor sr].
have or := proj1 wor.
have sub3: sub A (substrate Nat_order) by ue.
have  sub2: sub r Nat_order by apply: setI2_1.
move: (induced_wor wor sub3) (iorder_sr or sub3) => wor1 sr1.
move: (ordinal_o_is wor1).
move: (order_cp2 wor1 wor sub2);  rewrite ord_omega_pr.
case/ole_eqVlt.
   move => ->  eq1; split.
    move:eq1 =>[f [_ _ [bf sf tf] _ ]].
    move/card_finite_setP.
    move: (card_bijection bf); rewrite sf tf sr1  ordinal_o_sr => ->.
    by rewrite cardinal_Nat => h; move/(NltP h):h => /proj2.
  move => _.
  move: (ordinal_o_is wor); rewrite ord_omega_pr => is2.
  exact: (orderIT eq1 (orderIS is2)).
move/(oltP OS_omega); rewrite -/r => h1 h2; split.
  move => _; exists (ordinal r) => //.
  have -> //:induced_order Nat_order (ordinal r) = ordinal_o (ordinal r).
  have ha: sub (ordinal r) omega0 by move/(oltP OS_omega): h1; case; case.
  move:(ha); rewrite -/Nat - sr => hb.
  move: (iorder_osr or hb) (ordinal_o_or (ordinal r)) =>[or2 sr2] or3.
  apply: order_exten => // x y; split.
     move/iorder_gleP=>[xa ya /Nat_order_leP[xn yn le]].
     by apply/ordo_leP; split => //; case: le.
  move => /ordo_leP[xa ya etc].
  apply/(iorder_gle0P) => //.
  move: (ha _ xa) (ha _ ya) => xN yN; apply/Nat_order_leP.
  by split => //; split => //; apply: CS_nat.
case;move: h2 =>[f [_ _ [bf sf tf] _]].
apply/card_finite_setP.
move: (card_bijection bf); rewrite sf tf sr1 ordinal_o_sr; move ->.
by rewrite  (card_card (CS_nat h1)).
Qed.



(** continuity *)


Definition ord_below_b (f: fterm) b :=
  forall i, i <o b -> ordinalp (f i).

Definition olimit_up (f: fterm) x l :=
  exists2 y, y <o x & forall i, y <=o i -> i <o x -> f i <=o l.
Definition olimit_down (f: fterm) x l :=
  forall l', l' <o l -> 
   exists2 y, y <o x & forall i, y <=o i -> i <o x -> l' <o f i.
Definition olimit f x l :=
 olimit_up f x l /\ olimit_down f x l.


Definition ocontinuous_at (f: fterm) x :=
  olimit f x (f x).  

Definition ocontinuous (f: fterm) := 
   forall x, limit_ordinal x -> ocontinuous_at f x.
Definition ocontinuous_below (f: fterm) b := 
   forall x, limit_ordinal x -> x <o b ->  ocontinuous_at f x.


Definition econst (f: fterm) x v :=
  exists2 y, y <o x & forall i, y <=o i -> i <o x -> (f i) = v.

Lemma olimit_econst f x l: ordinalp l -> econst f x l ->
  olimit f x l.                     
Proof.
move => ol [y lyx fv].
split; first by  exists y => // i la lb;rewrite (fv i la lb); apply: oleR.
by move => m lm; exists y => // i la lb; rewrite (fv i la lb).
Qed.

Lemma olimit_zero f x: 
  olimit f x \0o <->  econst f x \0o. 
Proof.
split; last by apply: olimit_econst; apply: OS0.
move => [[y yl yp] hb]; exists y => // i i1 i2; move: (yp i i1 i2).
by move/ole0.
Qed.

Lemma olimit_succ f x l: ordinalp l -> 
  (olimit f x (osucc l) <->  econst f x (osucc l)).
Proof.
move => ol.
split; last by apply: olimit_econst; apply: OS_succ.
move =>[ [y ya yb] etc].
move: (etc _ (oltS ol)) => [z za zb].
exists (omax y z); first by  rewrite/omax/Gmax; Ytac h.
move => i la lb.
move: (omax_p1 (proj31_1 ya) (proj31_1 za)) => [lc ld].
apply: oleA; first exact: (yb _ (oleT lc la) lb).
apply/oleSltP; exact (zb _ (oleT ld la) lb).
Qed.

Lemma olimit_example (f := fun i => i %%c \2c) (x := omega0):
  ord_below_b f x /\ forall l, olimit f x l -> False.
Proof.
split.
  by move => i /(oltP OS_omega) ilo; apply: OS_nat; apply: NS_rem.
move => l [[y /(oltP OS_omega) yN yq] lb].
have fe i:  natp i ->  f (cdouble i) = \0o by case/even_double.
have fo i:  natp i ->  f (csucc(cdouble i)) = \1o.
  by move => /odd_succ_double/oddp_alt [].
move:(NS_succ (NS_double yN)); set z := (csucc _) => zN.
have zx: z <o x by  apply /(oltP OS_omega).
move: (oclt (cle_ltT (cle_n_doublen yN) (cltS (NS_double yN)))) => ylz.
move: (yq z (proj1 ylz) zx); rewrite (fo _ yN) => /oge1P lp.
move:(lb \0o lp) => [y1 /(oltP OS_omega) y1N yr].
have y2N := NS_succ y1N.
move: (proj1 (oclt (clt_leT (cltS y1N) (cle_n_doublen y2N)))) => la.
move/(oltP OS_omega): (NS_double y2N) => lc.
by move: (yr _ la lc); rewrite (fe _ y2N); case.
Qed.

Lemma OS_olim f x l: olimit f x l -> ordinalp l.
Proof.
move => [[y  ya yb] _].
exact: (proj32 (yb y (oleR (proj31_1 ya)) ya)).
Qed.

Lemma olimit_unique f x a b:
  limit_ordinal x ->  
  olimit f x a  -> olimit f x b -> a = b. 
Proof.
move => lx ha hb.
move: (OS_olim ha) (OS_olim hb) =>  oa ob.
move: ha hb => [[y ya yb] yc] [[z za zb] zc].
case: (oleT_ell oa ob) => // cab.
  move: (zc a cab) => [t ta tb].
  move: (omax_p1 (proj31_1 ya) (proj31_1 ta)) =>[la lb].
  have lc:  omax y t <o x by rewrite /omax/Gmax; Ytac h.
  by move:(yb _ la lc) (oltNge (tb _ lb lc)).
move: (yc b cab) => [t ta tb].
move: (omax_p1 (proj31_1 za) (proj31_1 ta)) =>[la lb].
have lc:  omax z t <o x by rewrite /omax/Gmax; Ytac h.
by move:(zb _ la lc) (oltNge (tb _ lb lc)).
Qed.


Definition olimsup (f: fterm) b :=
  \oinf (fun_image b (fun k => \osup (fun_image (ordinal_interval k b) f))).
Definition oliminf (f: fterm) b :=
  \osup (fun_image b (fun k => \oinf (fun_image (ordinal_interval k b) f))).


Lemma olim_supinf_prop f b: \0o <o b -> ord_below_b f b ->
  oliminf f b <=o olimsup f b.
Proof.
move => lob ofs.
have ob:= proj32_1 lob.
have H :=  ointvP ob.
rewrite /olimsup; set E := fun_image _ _.
have neE: nonempty E by  apply: funI_setne; move/(oltP ob): lob => h; ex_tac.
have osE: ordinal_set E.
  move => v /funI_P [j jb ->].
  by apply: OS_sup => u /funI_P[ i /H/proj2 /ofs xx  ->].
move:(ordinal_setI neE osE) => /funI_P  [k /(oltP ob) lkb ->].
set U := fun_image _ _; set a := \osup _.
have osU: ordinal_set U. 
  by move => x /funI_P [i /H /proj2 /ofs h ->]. 
have oa: ordinalp a by apply: OS_sup.
apply: (ord_ub_sup oa) => v /funI_P [j /(oltP ob) ljb ->].
set F := fun_image _ _.
have neF: nonempty F. 
  apply: funI_setne; exists j; apply /H; split => //.
  exact: (oleR (proj31_1 ljb)).
have osF: ordinal_set F.
 by move => x /funI_P [i /H /proj2 /ofs h ->]. 
move: (least_ordinal0 osF neF); set c := intersection F; move => [oc cf cp].
move: (omax_p1 (proj31_1 ljb) (proj31_1 lkb)).
set n := omax j k; move => [nj nk].
have nb : n <o b by rewrite /n/omax/Gmax; Ytac h.
have /cp le1: inc (f n) F by apply: funI_i; apply/H.
by apply(oleT le1); apply: (ord_sup_ub osU); apply: funI_i; apply/H.
Qed.


Lemma olim_supinf_prop2 f b: \0o <o b -> ord_below_b f b ->
  oliminf f b =  olimsup f b -> olimit f b (oliminf f b).
Proof.
move => bp ofs eq1.
have ob:= proj32_1 bp.
have H :=  ointvP ob.
split.
  rewrite eq1; rewrite /olimsup; set E := fun_image _ _.
  have neE: nonempty E by  apply: funI_setne; move/(oltP ob): bp => h; ex_tac.
  have osE: ordinal_set E.
    move => v /funI_P [j jb ->].
    by apply: OS_sup => u /funI_P[ i /H/proj2 /ofs xx  ->].
  move:(ordinal_setI neE osE) => /funI_P  [k /(oltP ob) lkb ->].
  set U := fun_image _ _; set a := \osup _.
  have osU: ordinal_set U. 
    by move => x /funI_P [i /H /proj2 /ofs h ->]. 
  have oa: ordinalp a by apply: OS_sup.
  exists k => // i i1 i2. 
  by apply:  (ord_sup_ub osU); apply: funI_i; apply /H.
rewrite /oliminf; set E := fun_image _ _.
pose Fj j := (fun_image (ordinal_interval j b) f).
have ha j: j <o b -> nonempty (Fj j). 
  move => ljb; apply: funI_setne; exists j; apply/H; split => //.
  exact: (oleR (proj31_1 ljb)).
have hb j: j <o b -> ordinal_set (Fj j).
  by move => ljb t /funI_P [i /H/proj2/ofs ox ->].
have osE: ordinal_set E.
  move => t /funI_P [i /(oltP ob) ilb ->].
  by case :(least_ordinal0 (hb _ ilb) (ha _ ilb)).
move => l /(olt_sup osE) [z /funI_P[j  /(oltP ob) ilb -> ]] h.
exists j => // k k1 K2; apply:(olt_leT h).
case :(least_ordinal0 (hb _ ilb) (ha _ ilb)) =>[ua ub uc].
by apply: uc; apply: funI_i; apply/H.
Qed.
  

Lemma olim_supinf_prop3 f b l: \0o <o b -> ord_below_b f b ->
  olimit f b l ->
  oliminf f b =  olimsup f b /\ l = oliminf f b.
Proof.
move => bp ofs h.
move: (OS_olim h) => ol; move: h => [lfu lfl].
have ob:= proj32_1 bp.
have H :=  ointvP ob.
move: (olim_supinf_prop bp ofs) => le1.
have le2: olimsup f b <=o l.
  move: lfu => [k kb etc].
  rewrite /olimsup; set E := fun_image _ _.
  have neE: nonempty E by  apply: funI_setne; move/(oltP ob): bp => h; ex_tac.
  have osE: ordinal_set E.
    move => v /funI_P [j jb ->].
    by apply: OS_sup => u /funI_P[ i /H/proj2 /ofs xx  ->].
  move:(least_ordinal0 osE neE); set a := intersection _.
  move =>[oa ap1 ap2].
  set u := \osup  (fun_image (ordinal_interval k b) f).
  have: inc u E by apply: funI_i; apply/(oltP ob).
  move /ap2 => au; apply:(oleT au).
  by apply (ord_ub_sup ol) => t /funI_P [i /H [ia ib] ->]; apply: etc.
case: (ole_eqVlt  (oleT le1 le2)) => h.
  by split => //; apply: oleA => //; rewrite h.
move/lfl:h => [i ltib etc].
pose Fj j := (fun_image (ordinal_interval j b) f).
have ha j: j <o b -> nonempty (Fj j). 
  move => ljb; apply: funI_setne; exists j; apply/H; split => //.
  exact: (oleR (proj31_1 ljb)).
have hb j: j <o b -> ordinal_set (Fj j).
  by move => ljb t /funI_P [k /H/proj2/ofs ox ->].
move :(ordinal_setI  (ha _ ltib) (hb _ ltib)) => /funI_P [j /H [ja jb] jc].
move: (etc j ja jb); rewrite - jc { etc j ja jb jc} => lt1.
pose E :=  (fun_image b  (fun k => intersection (Fj k))).
have osE: ordinal_set E.
  move => t /funI_P [j /(oltP ob) jb ->].
  by case:(least_ordinal0  (hb _ jb) (ha _ jb)).
have fi: inc (intersection (Fj i)) E by apply: funI_i; apply/(oltP ob).
case: (oltNge lt1 (ord_sup_ub osE fi)).
Qed.

Definition esame_below (f g: fterm) x :=
  exists2 y, y <o x & forall i, y <=o i -> i <o x -> f i = g i.

Lemma olim_exten f g x l: esame_below f g x ->
  (olimit f x l  <-> olimit g x l).
Proof.
move => [b lbx bp]; split.
  move =>[[y ya yb] yc]; split.
    move: (omax_p1 (proj31_1 ya) (proj31_1 lbx)) =>[la lb].
    have lc:  omax y b <o x by rewrite /omax/Gmax; Ytac h.
    exists (omax y b) => // i ia ib; move: (oleT la ia)(oleT lb ia) => qa qb.
    by rewrite -  bp //; apply: yb.  
  move => m lm; move: (yc _ lm) => [z za zb].
  move: (omax_p1 (proj31_1 za) (proj31_1 lbx)) =>[la lb].
  have lc:  omax z b <o x by rewrite /omax/Gmax; Ytac h.
  exists (omax z b) => // i ia ib; move: (oleT la ia)(oleT lb ia) => qa qb.
  by rewrite -  bp //; apply: zb.  
move =>[[y ya yb] yc]; split.
  move: (omax_p1 (proj31_1 ya) (proj31_1 lbx)) =>[la lb].
  have lc:  omax y b <o x by rewrite /omax/Gmax; Ytac h.
  exists (omax y b) => // i ia ib; move: (oleT la ia)(oleT lb ia) => qa qb.
  by rewrite bp //; apply: yb.  
move => m lm; move: (yc _ lm) => [z za zb].
move: (omax_p1 (proj31_1 za) (proj31_1 lbx)) =>[la lb].
have lc:  omax z b <o x by rewrite /omax/Gmax; Ytac h.
exists (omax z b) => // i ia ib; move: (oleT la ia)(oleT lb ia) => qa qb.
by rewrite bp //; apply: zb.  
Qed.

Lemma olim_sup_spec f x y:
  limit_ordinal x -> y <o x -> 
  (forall i j, y <=o i -> i <=o j -> j <o x -> f i <=o f j) ->
  olimit f x (\osup (fun_image (ordinal_interval y x) f)).
Proof.
move => /limit_ordinal_P [xp lx] lyx fincr.
have ox: ordinalp x by move: (proj32_1 lyx). 
set A := (ordinal_interval y x).
have H i: inc i A <->  y <=o i /\ i <o x by exact:(ointvP ox y i).
have osA: ordinal_set (fun_image A f).
  move => a /funI_P [i /H [lyi lix] ->].
  exact: (proj31 (fincr i (osucc i) lyi (oleS (proj32 lyi)) (lx i lix))).
split.
  by exists y => // i lti liy; apply: (ord_sup_ub osA);apply: funI_i; apply/H.
move => l /(olt_sup osA) [t /funI_P [ z /H [za zb] ->] ll].
exists z => // i ia ib; exact:(olt_leT ll (fincr z i za ia ib)).
Qed.

Lemma olim_sup f x:
  limit_ordinal x ->
  (forall i j, i <=o j -> j <o x -> f i <=o f j) ->
  olimit f x (\osup (fun_image x f)).
Proof.
move => lx ha.
move/limit_ordinal_P: (lx) => [xp _].
have hb: (forall i j, \0o <=o i -> i <=o j -> j <o x -> f i <=o f j). 
  move => i j _; apply: ha.
by move:(olim_sup_spec lx xp hb); rewrite (ointv_pr1 (proj32_1 xp)).
Qed.

Lemma normal_continuous f: normal_ofs f -> ocontinuous f.
Proof.
move =>[ha hb]x xl; rewrite /ocontinuous_at (hb x xl).
by apply:(olim_sup xl) => i j la lb; apply: sincr_incr.
Qed.

Lemma normal_continuous_rev f: sincr_ofs f -> ocontinuous f ->
  normal_ofs f.
Proof.
move => ha hb; split => // x xl.
have h: (forall i j, i <=o j -> j <o x -> f i <=o f j).
  by move => i j la lb; apply: sincr_incr.
exact:(olimit_unique xl (hb x xl) (olim_sup xl h)).
Qed.



Lemma const_continuous v: ordinalp v -> ocontinuous (fun i => v).
Proof.
move =>  ov x xl; move: (limit_pos xl) => xp; move: (proj31 xl) => ox.
by apply: olimit_econst => //; exists \0o.
Qed.


Lemma id_continuoius: ocontinuous  id.
Proof.
move => x /limit_ordinal_P [xp xl].
split; first by exists \0o => // i _ /proj1.
by move => y lyx; exists (osucc y); [ apply: xl | move => i /oleSltP].
Qed.

Lemma non_cont_ex1 x: limit_ordinal x -> 
   ~ ocontinuous_at osucc x.
Proof.
move => xl.
move/(olimit_succ _ _ (proj31 xl)) =>[y lyx yp].
move:(lyx) => [[oy ox _]]; case.
exact:(osucc_inj oy ox (yp y (oleR oy) lyx)).
Qed.

Lemma non_cont_ex2: ~ ocontinuous_at (fun t => t +o t) omega0.
Proof.
move: OS_omega => oo hyp.
move:(osum_Meqlt olt_0omega oo); rewrite (osum0r oo) => ll.
move:(proj2 hyp _ ll) => [y ys yp].
by case:(olt_ltT (yp y (oleR (proj31_1 ys)) ys) (osum2_lt_omega ys ys)).
Qed.


Lemma non_cont_ex3: ~ ocontinuous_at (fun t => t *o t) omega0.
Proof.
move: OS_omega => oo hyp.
move:(oprod_Meq1lt olt_1omega olt_0omega) => ll.
move:(proj2 hyp _ ll) => [y ys yp].
by case:(olt_ltT (yp y (oleR (proj31_1 ys)) ys) (oprod2_lt_omega ys ys)).
Qed.


Lemma non_cont_ex4 (x := omega0 ^o \2o +o omega0):
  limit_ordinal x /\  ocontinuous_at (fun t => t +o t) x.
Proof.
move:(opow_Mo_lt olt_12)(indecomp_prop4 OS2); rewrite oopow1.
set a := oopow \2o => ha hb.
move: omega_limit OS_omega (proj32_1 ha) => lo oo oa.
move: (osum_limit oa lo) => lx; split => //.
pose f t := t +o t. 
have h i j: i <=o j -> j <o x -> f i <=o f j.
  move => sa _; apply: (osum_Mlele sa sa).
move:(olim_sup lx h).
set A := fun_image _ _; set b := \osup _.
suff : b = x +o x  by move ->.
have ox := (proj31 lx).
have osA: ordinal_set A.
  by move => y /funI_P [i /(oltP ox ) /proj31_1 la ->]; apply: OS_sum2.
have: b <=o x +o x.
  apply: (ord_ub_sup (OS_sum2 ox ox)) => z /funI_P [i /(oltP ox) ll -->].
  exact: (osum_Mlele (proj1 ll)(proj1 ll)).
case /ole_eqVlt => //.
have fs t: t <o a -> f (a +o t) =  (a +o a) +o t.
  move => ta; move: (proj31_1 ta) => ot; move:(OS_sum2 oa ot) => oat.
  by rewrite /f (osumA oat oa ot) -(osumA oa ot oa) (indecomp_prop1 hb ta).  
rewrite -/(f x) (fs omega0 ha) => bs.
have aA: inc (a +o a) A.
  apply: funI_i; apply/(oltP ox).
  by move: (osum_Meqlt olt_0omega oa); rewrite (osum0r oa).
move: (ord_sup_ub osA aA) => leb.
move: (odiff_pr leb); set c := _ -o _; move =>[oc cv].
case: (oleT_el oo oc) => cs.
  by case (oltNge bs); move:(osum_Meqle cs (OS_sum2 oa oa)); rewrite - cv.
suff bA: inc (osucc b) A by move: (ord_sup_ub osA bA) => /oleSltP; case.
move/limit_ordinal_P:omega_limit =>[ _ ho]; move: (ho _ cs) => scs.
apply/funI_P; exists (a +o osucc c).
  by apply/(oltP ox); apply: osum_Meqlt. 
by rewrite (fs _ (olt_ltT scs ha)) - (osum2_succ (OS_sum2 oa oa) oc) - cv.
Qed.


Lemma cont_fun_th1 (f: fterm) b:
  b <o aleph1 -> ord_below_b f b -> 
  exists (F: fterm2),
   [/\ forall i x, i <o omega0 -> x <o b -> ordinalp (F i x),
    forall i, i <o omega0 -> ocontinuous_below (fun x => F i x) b &
   forall x, x <o b -> olimit (fun i => (F i x)) omega0 (f x)].
Proof.
move: OS_omega => oo ha hb.
have ob :=  (proj31_1 ha).
case: (ozero_dichot ob) => bp.
  rewrite bp;exists (fun i j =>  \0o); split.
  - by move => i j iN /olt0.
  - by move => i io j _ /olt0.
  - by move => i /olt0. 
have neb: nonempty b by move/(oltP ob): bp => h; ex_tac.
have [_ /countableP ]: countable_ordinal b.
  by apply /aleph_oneP; rewrite - Cantor_omega_pr3; apply/(oltP (proj32_1 ha)).
rewrite aleph0_pr1 => la.
move:(card_le_surj la neb) => [g [bg sg tg]].
have fg: function g by fct_tac.
pose Ei i := fun_image (csucc i) (Vf g).
have Ei_lim x: x <o b -> exists2 n, natp n & forall i, natp i -> n <=c i ->  
  inc x (Ei i).
  move/(oltP ob); rewrite -tg => /(proj2 bg); rewrite sg. 
  by move => [n nN ->]; exists n => // i iN lin; apply: funI_i; apply/NleP.
pose Bi i x := Zo (Ei i) (fun v => x <=o v). 
pose F i x := f (intersection (Bi i x)).
have ra i x: Bi i x = emptyset -> F i x  = f \0o. 
  by rewrite /F; move ->; rewrite setI_0.
have rb i x: Bi i x = emptyset -> ordinalp (F i x).
  by move => /ra ->; apply: hb. 
have rc i x: natp i -> ordinal_set (Bi i x).
  by move => iN z /Zo_hi/proj32.
have rd i x: i <o omega0  -> ordinalp (F i x).
  move => /(oltP oo) iN; case: (emptyset_dichot (Bi i x)); first by apply: rb.
  move => ne; move: (ordinal_setI ne (rc _ _ iN)) => /Zo_S /funI_P[j ja jb].
  rewrite /F jb; apply: hb; apply/(oltP ob); Wtac; rewrite sg.
  move/(NleP iN): ja => lji; apply: (NS_le_nat lji  iN).
have rdbis  i x: i <o omega0 -> x <o b -> ordinalp (F i x) by fprops.
have rf x:  x <o b -> olimit (fun i => F i x) omega0 (f x).
  move => lxb.
  move/(oltP ob): (lxb) => ixb.
  apply: olimit_econst; first by apply: hb.
  move:(Ei_lim x lxb) =>[n nN np].
  exists n; first by apply/(oltP oo).
  move => i lni lio.
  have iN: natp i by apply/(oltP oo).
  have clni: n <=c i by apply:(ocle3 (CS_nat nN) (CS_nat iN) lni).
  move:(np _ iN clni) => xE.
  have xB: inc x (Bi i x) by apply:(Zo_i  xE); apply: (oleR (proj31_1 lxb)).
  have ne: nonempty (Bi i x) by ex_tac.
  move:(least_ordinal0 (rc i x iN) ne) =>[sa /Zo_hi sb sc].
  by rewrite /F (oleA (sc _ xB) sb).
exists F; split => // i lio  x lx lxb.
move/(oltP ob): (lxb) => ixb; move/(oltP oo): (lio) => iN.
rewrite /ocontinuous_at /F; apply: olimit_econst; first by  apply:rd.
pose Ci :=  (Ei i) -s (Bi i x).
case: (emptyset_dichot Ci) => Cie.
  exists \0o;[ by apply: limit_pos |  move => y _ lyx].
  have eq1: (Bi i x) = Ei i.
    apply: extensionality; [apply:Zo_S | apply: (empty_setC Cie)].
  have eq2: (Bi i y)= (Bi i x).
    rewrite eq1; apply: extensionality; first by apply: Zo_S.
    move => v ve; apply: (Zo_i ve).
    by move: ve; rewrite - eq1 => /Zo_hi => lxv; apply:(oleT (proj1 lyx) lxv).
  by rewrite  eq2.
have cip a: inc a Ci -> inc a (Ei i) /\ a <o x.
  move => /setC_P [ae etc]; split => //.
  move/funI_P: (ae) => [z /(NleP iN) lzi eq1].
  have lab : a <o b.
   by apply/(oltP ob); rewrite eq1; Wtac; rewrite sg; apply: (NS_le_nat lzi iN).
  case: (oleT_el (proj31_1 lxb) (proj31_1  lab)) => // lxa.
  by case: etc; apply:Zo_i.
have [a aCi amaxCi]: exists2 a, inc a Ci & forall z, inc z Ci -> z <=o a.
  have: ordinal_set Ci by move => t /cip/proj2/proj31_1.
  have: sub Ci (fun_image  (csucc i) (Vf g)).
    by move => t /setC_P [].
  clear cip;move: iN Ci Cie; clear; move: i; apply: Nat_induction.
    move => A [t tA] ap osA; exists t => // z zA.
    rewrite succ_zero in ap.
    move:(oleR (osA _ tA)).        
    move: (ap _ tA) => /funI_P [u /set1_P -> ->].
    by move: (ap _ zA) => /funI_P [uu /set1_P -> ->].
  move => n nN Hrec C neC sC osc.
  set w := (Vf g (csucc n)).
  have sN :=  (NS_succ nN).
  have: sub (C -s1 w) (fun_image (csucc n) (Vf g)).
    move => t /setC1_P [/sC  /funI_P [z /(NleP sN) lt ->] tw].
    case:(cle_eqVlt lt); [ by move => h; case: tw; ue | move/(NltP sN) => le ].
    by apply: funI_i.
  case: (inc_or_not w C) => wC; last first.
    by rewrite (setC1_eq wC) => ssC; apply: Hrec.
  have ow: ordinalp w by  apply: osc.
  move => ss1; case: (emptyset_dichot (C -s1 w)) => c1E.
    exists w => // z zC; case: (equal_or_not z w) => ezw. 
      by rewrite ezw; apply: oleR.
    by empty_tac1 z; apply/setC1_P.
  have os1: ordinal_set (C -s1 w) by move => t/setC1_P/proj1/osc.
  move: (Hrec _ c1E ss1 os1) => [a ac ap].
  exists (omax a w).
     by rewrite/omax /Gmax;Ytac h => //; case/ setC1_P: ac.
  move: (omax_p1 (os1 _ ac) ow) => [qa qb].
  move => z zc; case: (equal_or_not z w) => ezw; first by rewrite ezw. 
  by apply: oleT qa; apply: ap; apply/setC1_P.
move:(cip _ aCi) => [aE lax]; exists (osucc a).
  by move/limit_ordinal_P: lx =>[ _ h]; apply: h.
move => y /oleSltP lay lyx.
suff eq2: (Bi i x) = (Bi i y) by rewrite  - eq2.
set_extens t => /Zo_P [yEi cp]; apply:(Zo_i yEi).
   exact:(oleT (proj1 lyx) cp).
case: (inc_or_not t (Bi i x)); first by  move/Zo_hi.
move => tnbi.
have: inc t Ci by apply/setC_P.
by move/amaxCi => ta; case:(oleNgt (oleT cp ta)).
Qed.


Lemma uncountable_sub_Omega_prop E:
  sub E aleph1 -> ~ countable_set E ->
  exists x, [/\ x <o aleph1, limit_ordinal x &
   forall y, y <o x -> exists z, [/\ inc z E, y <o z & z <o x]].
Proof.
move => seO ucE. 
move: (aleph_lt_ltc olt_01); rewrite -/aleph1 aleph0E => clt01.
move: (oclt clt01) => lto0o1.
have oo1:= proj32_1 lto0o1.
have ha: ordinal_ub E aleph1 by move => t /seO /(oltP oo1) /proj1.
have hb: ordinal_set E by move => t /ha/proj31.
move: (ord_ub_sup oo1 ha) => le1.
have H x: x <o aleph1 <-> countable_ordinal x.
  apply: (iff_trans (oltP oo1 x)); rewrite Cantor_omega_pr3. 
  exact:aleph_oneP.
case: (equal_or_not (\osup E) aleph1) => eq1; last first.
  move/H: (conj le1 eq1) => /countable_succ /proj2 cs.
  have os := (proj31 le1).
  have hc: sub E (osucc (\osup E)).
    by move => t tE; apply/(oleP os); apply: (ord_sup_ub).
  by case: ucE; apply: (countable_sub hc).
pose B x := Zo E (fun z => x <o z).
have hc x: x <o aleph1 -> nonempty (B x).
  rewrite - eq1 => la; move: (olt_sup hb la) => [z za zb]; exists z.
  by apply: Zo_i => //; apply: seO.
have hd x: ordinal_set (B x) by  move => t /Zo_S/ hb.
pose N x := intersection (B x).
have Np x: x <o aleph1 -> inc (N x) E  /\ x <o N x. 
  by move => xa; move /Zo_P: (ordinal_setI (hc _ xa)  (hd x)).
have za: \0o <o aleph1 by move:(olt_ltT olt_0omega lto0o1). 
move: (induction_defined_pr N (N \0o)); set f:= induction_defined _ _.
move =>[sf srjf f0 fs]; set A := target f.
case:(srjf); rewrite sf => ff sjf.
have sAE: sub A E.
  move => t /sjf [n nN ->]; move: n nN. 
  apply: Nat_induction; first by rewrite f0; exact: (proj1 (Np _ za)).
  by move => n nN /seO /(oltP oo1) / Np/proj1; rewrite (fs _  nN). 
have osA: ordinal_set A by move => t /sAE/hb.
have AP x: inc x A -> inc (N x) A /\ x <o N x. 
  move => xA.
  move /(oltP oo1): (seO _ (sAE _ xA)) => /Np/proj2 lt1; split => //.
  move: (sjf _ xA) =>[n nN av].
  by move:(fs _ nN); rewrite - av /A => <-; Wtac; rewrite sf; apply: NS_succ.
have neA: nonempty A.
  by exists (Vf f \0c); rewrite /A; Wtac; rewrite sf; apply: NS0.
have sas: ~ inc (union A) A.
  move => lsA; move: (AP _ lsA) => [qa qb].
  case:(oleNgt (ord_sup_ub osA qa) qb).  
case: (ord_sup_inVlimit osA neA) => // lsA.
have he: countable_set A.
  move: (image_smaller ff); rewrite (surjective_pr0 srjf); rewrite sf.
  by rewrite - aleph0_pr1; move/ countableP.
have hf:  alls A countable_ordinal.
  by move => t /sAE /seO /(oltP oo1) /H.
move /H: (countable_ordinal_sup he hf) => lt2.
exists (\osup A); split => // y ya.
move:(olt_sup osA ya) =>[z zA ub]; exists z; split => //; first by apply: sAE.
by split; [ apply:(ord_sup_ub osA zA) | move => bad; case: sas; rewrite - bad].
Qed.

  
Lemma cont_fun_th2 (F: fterm2) b:
  ordinalp b ->
  (forall i x, i <o b -> x <o aleph1 -> ordinalp (F i x)) ->
  (forall i, i <o b -> ocontinuous_below (fun x => F i x) aleph1) ->
  (forall x, x <o aleph1 -> olimit (fun i => (F i x)) b (osucc x)) ->
  False.
Proof.
move => ob ha hb hc.
pose B x := Zo b (fun y => forall i, y <=o i -> i <o b ->
   (F i x) = osucc x).
pose Y x := intersection (B x).
have hd x: x <o aleph1 -> nonempty (B x).
  move => xo; move:(hc x xo) => hcx.
  have ox := (proj31_1 xo).
  move/ (olimit_succ _ _ ox):  hcx => [y ya yb]; exists y; apply: Zo_i => //.
  by apply/(oltP ob).
have he x: ordinal_set (B x) by move => t /Zo_S; apply: Os_ordinal.
have hf x: x <o aleph1 ->
   Y x <o b /\ (forall i, Y x <=o i -> i <o b -> F i x = osucc x). 
   move => xo; move /Zo_P:(ordinal_setI (hd x xo) (he  x)) => [ra rb].
   by split => //; apply /(oltP ob).
have hf1 x:  x <o aleph1 -> Y x <o b by move /hf/proj1.
move: (aleph_lt_ltc olt_01); rewrite -/aleph1 aleph0E => clt01.
move: (oclt clt01) => lto0o1.
pose E := fun_image (osucc omega0) Y.
have ra1 t: inc t E ->  t <o b.
  move => /funI_P [x /(oleP OS_omega) xa ->].
  exact:(hf1 _ (ole_ltT xa lto0o1)).
have ra:  ordinal_ub E b by move => t /ra1/proj1.
have osE: ordinal_set E by move => t /ra/proj31.
set c := \osup E.
have rb: c <=o b by apply: (ord_ub_sup ob ra). 
case: (equal_or_not c b) => sEb; last first.
  have hg x: x <=o omega0 -> F c x = osucc x.
    move => h; move: (ole_ltT h lto0o1) => h1.
    move: (hf _ h1) =>[qa qb]; apply: qb => //.
    by apply: (ord_sup_ub osE); apply: funI_i; apply /(oleP OS_omega).
  have loo:= omega_limit.
  move: (hb _ (conj rb sEb) _ loo lto0o1) => ct1.
  case:(non_cont_ex1 loo).  
  have osb: (esame_below (F c) osucc omega0).
    exists \0o; first by  apply: olt_0omega.
    by move => i ia /proj1 ib; apply: hg. 
  move/(olim_exten _ osb): ct1; rewrite hg //; apply:(oleR OS_omega).
have Eu i: i <o b -> exists2 j, inc j E & i <o j. 
  rewrite - sEb => lt1; exact: (olt_sup osE lt1).
pose Bb x := (Zo E (fun j => Y x <o j)).
pose C x := intersection (Bb x).
have hdb x: x <o aleph1 -> nonempty (Bb x).
  by move => /hf/proj1/Eu [j ja jb];exists j; apply:Zo_i.
have heb x: ordinal_set (Bb x) by move => t /Zo_S; apply: osE. 
have hg x: x <o aleph1 ->
   [/\  C x <o b, inc (C x) E & 
    forall i, C x <=o i -> i <o b -> F i x = osucc x].
  move => xo; move /Zo_P:(ordinal_setI (hdb x xo) (heb  x)) => [sa sb].
  split; [  by apply: ra1 | done | move => u ua ub].
  apply: (proj2(hf _ xo) _ (oleT (proj1 sb) ua) ub).
pose Ii i := Zo aleph1 (fun x => C x = i).
pose If := (Lg E Ii).
have csdif: countable_set (domain If).
  rewrite Lgd; apply: countable_fun_image.
  exact: (proj2 (countable_succ (countable_leomega (oleR  OS_omega)))).
have  fgf: fgraph If by rewrite /If; fprops. 
case: (all_exists_dichot1 countable_set (range If)) => q.
  have ac: (allf If countable_set).
    by move => t tf; apply: q; apply: inc_V_range.
  move: (countable_union csdif ac).
  have ->: unionb If = aleph1.
    rewrite - setU_bf;set_extens t; first by move => /setUf_P [i iE /Zo_S].
    move => ta; move/(oltP (proj32_1 lto0o1)): (ta).
    by move => /hg [_ cr _]; union_tac; apply:Zo_i.
  move/countableP. rewrite (card_card (proj32_1 clt01)); exact: (cltNge clt01).
move: q => [Zi /(range_gP fgf)]; rewrite Lgd; move =>[p pE]; rewrite LgV//.
move => Eiv icEi; clear If fgf csdif.
have zia: sub Zi aleph1 by rewrite Eiv; apply: Zo_S.
move:(uncountable_sub_Omega_prop zia  icEi) => [x [xo lx xp]].
move: (hf x xo) =>[qa qb].
have pb: p <o b by apply: ra1.
move: (omax_p1 (proj31_1 qa) (proj31_1 pb)); set n := omax _ _; move =>[qc qd].
have nb: n <o b by rewrite /n/omax/Gmax; Ytac h.
move: (qb n qc nb) => Fnx.
move: (hb n nb x lx xo); rewrite /ocontinuous_at Fnx.
move/(olimit_succ _ _ (proj31_1 xo)) => [y lyx yp].
move: (xp _ lyx) =>[z [za zb zc]].
move:za; rewrite Eiv => /Zo_hi Cz.
have ll: C z <=o n by ue.
move: (proj33 (hg _ (olt_ltT zc xo)) n ll nb).
rewrite (yp z (proj1 zb) zc); move: zc => [[oz ox _] /nesym ezx].
by move/(osucc_inj ox oz).
Qed.

Definition cont_fun_th3_prop f b F := 
  [/\ fgraph F, domain F = omega0 \times aleph1, 
   (allf F ordinalp /\
     forall i x, i <o omega0 -> b <o x -> x <o aleph1 -> Vg F (J i x) = \0o),
  forall i, i <o omega0 -> ocontinuous_below (fun x => (Vg F (J i x))) aleph1 &
  forall x, x <=o b -> olimit (fun i => (Vg F (J i x))) omega0 (f x)].
  
Lemma cont_fun_th1_bis (f: fterm) b:
  b <o aleph1 -> ord_below_b f aleph1 -> 
  exists F, cont_fun_th3_prop f b F.
Proof.
move => ba ha.
move: OS_omega (proj32_1 ba) => oo oo1. 
move: (aleph_limit OS1) ; rewrite -/aleph1.
move/limit_ordinal_P => /proj2 h; move:(h _ ba) => sba; clear h.
have hb:ord_below_b f (osucc b). 
  by move => t lt; apply: ha; apply: (olt_ltT lt sba).
move: (cont_fun_th1 sba hb) => [F [fa fb fc]].
pose g i x := Yo (x <=o b) (F i x) \0o.
pose G := Lg (omega0 \times aleph1) (fun p => g (P p) (Q p)).
have ra:  fgraph G by rewrite/G; fprops.
have rb: domain G = omega0 \times aleph1 by rewrite Lgd.
have pd i x: i <o omega0 -> x <o aleph1 -> inc (J i x) (omega0 \times aleph1).
  by move => /(oltP oo) qa /(oltP oo1) qb; apply: setXp_i.
have rc1: allf G ordinalp.
  move => t; rewrite rb /G/g => tp; rewrite LgV//; Ytac h; last by apply: OS0.
  move/setX_P: tp => [qa /(oltP oo) qb qc]. apply: fa => //.
  by apply/oltSleP.
have rc2 i x: i <o omega0 -> b <o x -> x <o aleph1 -> Vg G (J i x) = \0o.
  move => ua /oleNgt ub uc; move: (pd _ _ ua uc) => pp.
  rewrite /G/g LgV//; aw; rewrite Y_false => //.
have rd x: x <=o b -> olimit (fun i => Vg G (J i x)) omega0 (f x).
  move => lxb.
  have lesb: x <o osucc b by  apply/oltSleP.
  move: (fc _ lesb).
  have sb:  (esame_below  (F^~ x) (fun i => Vg G (J i x)) omega0).
    exists \0o; first by apply: olt_0omega.
    move => t tplto to /=.
    move: (pd _ _ to (ole_ltT lxb ba)) => aux.
    by rewrite /G/g LgV//; aw; Ytac0.
  by move/ (olim_exten _  sb).
exists G; split => //.
move => i lio x limx lxa.
move:(pd _ _ lio lxa) => dp9.
rewrite /ocontinuous_at {2}/G /g LgV//; aw; Ytac h.
  have lxb: x <o (osucc b) by apply/oltSleP.
  move: (fb _ lio _ limx lxb).
  have sb: (esame_below [eta F i] (fun x0 : Set => Vg G (J i x0)) x).
    exists \0o; first by apply: limit_pos.
    move => t _ ltx; move:(pd _ _ lio (olt_ltT ltx lxa)) => dp.
    by rewrite /G/g  LgV//; aw; rewrite (Y_true (oleT (proj1 ltx) h)).
  by move/ (olim_exten _  sb).
case:(oleT_el (proj31_1 lxa) (proj31_1 ba)) => // lbx.
move/limit_ordinal_P: limx => /proj2 q; move:(q _ lbx) => sbx; clear q.
apply/olimit_zero; exists (osucc b) => // j ja jb.
move: (pd _ _  lio (olt_ltT jb lxa)) => pp.
by rewrite /G/g LgV //;aw; rewrite Y_false //; apply:oltNge; apply/oleSltP.
Qed.


Lemma cont_fun_th3 (f: fterm)
  (tf := fun a x => Yo (x <=o a) (f x) \0o):
  ord_below_b f aleph1 -> 
  exists (F:  Set -> Set -> Set -> Set), 
  [/\ forall a i x, a <o aleph1 -> i <o omega0 -> x <o aleph1 ->
         ordinalp (F a i x),
    forall a i, a <o aleph1 -> i <o omega0 -> 
         ocontinuous_below (fun x => F a i x) aleph1,
    forall a x, a <o aleph1 -> x <o aleph1 ->
      olimit (fun i => (F a i x)) omega0 (tf a x) &
    forall x, x <o aleph1 -> olimit (fun i => (tf i x)) aleph1 (f x)].
Proof.
move => ha.
move: (aleph_lt_lto olt_01); rewrite -/aleph1 aleph0E => olt01.
move: (olt01) => [[oo oo1 _] _].
have H i x: i <o omega0 ->  x <o aleph1 -> inc (J i x) (omega0 \times aleph1).
  by move => /(oltP oo) qa /(oltP oo1) qb; apply: setXp_i.
pose Ga a := choose (fun z  => cont_fun_th3_prop f a z).
have Gap a: a <o aleph1 -> cont_fun_th3_prop f a (Ga a).
  move =>h; apply: (choose_pr (cont_fun_th1_bis h ha)).
pose F := (fun a i x => (Vg (Ga a) (J i x))).
have ra a i x: a <o aleph1 -> i <o omega0 -> x <o aleph1 -> ordinalp (F a i x).
  move => pa pi px; move: (Gap a pa) => [sa sb [sc _] _ _ ].
  by apply: sc; rewrite sb; apply:H.
have rd x: x <o aleph1 -> olimit (tf^~ x) aleph1 (f x).
  move => xp; apply: (olimit_econst (ha _ xp)).
  by exists x => // t xt ta; rewrite /tf; Ytac0.
have rb a i: a <o aleph1 -> i <o omega0 -> ocontinuous_below [eta F a i] aleph1.
  move => pa io x lx xa.
  move: (Gap a pa) => [_ _ _  se _ ]; exact: (se _ io x lx xa). 
exists F; split => //.
move => a x pa px.
move: (Gap a pa) => [ _ sb [sc sd] _ se ].
rewrite /tf; Ytac h; first exact: (se _ h).
case: (oleT_el (proj31_1 px) (proj31_1 pa)) => // ax.
apply/ olimit_zero; exists \0o; first by apply: olt_0omega.
by move => i _ ib; rewrite /F sd.
Qed.


Lemma cont_fun_th4_aux (f: fterm2) bi bx
      (g := fun x => \osup (fun_image bi (fun i => f i x))):
  limit_ordinal bi -> ordinalp bx ->
  (forall i j x, i <=o j -> j <o bi -> x <o bx -> f i x <=o f j x) ->
  (forall i x y, i <o bi -> x <=o y -> y <o bx -> f i x <=o f i y) ->
  [/\ forall x, x <o bx -> ordinal_set (fun_image bi (f^~ x)),
      forall x, x <o bx -> olimit (fun i => f i x) bi (g x),
     (forall x y, x <=o y -> y <o bx -> g x <=o g y) &
     forall i x, i <o bi -> x <o  bx -> f i x <=o g x].                         Proof.
move => lbi obx inc1 inc2.
move /limit_ordinal_P: (lbi) => [bip blim].
move: (proj32_1 bip) => obi.
have osa x: x <o bx -> ordinal_set (fun_image bi (f^~ x)).
  move => xo v /funI_P [i li ->].
  move/(oltP obi):li => la; move: (proj31_1 la) =>  oi.
  exact: (proj31 (inc1 _ _ _ (oleS oi) (blim _  la) xo)).
have ha i x: i <o bi -> x <o  bx -> f i x <=o g x.
  by move => li lx; apply: (ord_sup_ub (osa _ lx)); apply: funI_i; apply/oltP.
have og x: x <o  bx -> ordinalp (g x).
  move => h; exact: (proj32 (ha _ _ bip h)).
have hb x: x <o bx -> olimit (f^~ x) bi (g x).
  by move => xl;apply: (olim_sup lbi) => i j qa qb; apply: inc1.
split => // x y lxy lyb .
apply: (ord_ub_sup (og _ lyb)) => tv /funI_P [i /(oltP obi) si ->].
exact: (oleT (inc2 _ _ _ si lxy lyb) (ha _ _ si lyb)).
Qed.
  

Lemma cont_fun_th4 (f: fterm2) bi bx
      (g := fun x => \osup (fun_image bi (fun i => f i x))):
  limit_ordinal bi -> ordinalp bx ->
  (forall i j x, i <=o j -> j <o bi -> x <o bx -> f i x <=o f j x) ->
  (forall i x y, i <o bi -> x <=o y -> y <o bx -> f i x <=o f i y) ->
  (forall i, i <o bi -> ocontinuous_below (f i) bx) -> 
  ocontinuous_below g bx.
Proof.
move => lbi obx ha hb hc.
move:(cont_fun_th4_aux lbi obx ha hb) =>[he hf hg hh].
move => x xlim lxb; split.
  by exists \0o; [ apply: limit_pos | move => u _ /proj1 ux; apply: hg].
move => l llg.
move:(olt_sup (he _ lxb)llg) => [v /funI_P [z /(oltP (proj31 lbi)) zl ->]] lt2.
move:(proj2 (hc _ zl x xlim lxb) _ lt2) =>[y ya yb]; exists y => // t ta tb.
exact: (olt_leT  (yb t ta tb) (hh _ _ zl (olt_ltT tb lxb))). 
Qed.


Lemma cont_fun_th4_ex1 a b
   (f := fun i x => Yo (x <=o i) a b) 
   (g := fun x => Yo (x <o omega0) a b):
    a <o b -> 
   [/\  
      forall i x y, ordinalp i -> x <=o y -> f i x <=o f i y,
      forall i x, ordinalp i -> limit_ordinal x -> ocontinuous_at (f i) x,
      forall x, ordinalp  x -> olimit (fun i => f i x) omega0 (g x) &
      ~ocontinuous_at g omega0].
Proof.
move => lab.
move: (lab) => [[oa ob _] _].
split.
- move: (proj1 lab) => leab; move: (leab) => [/oleR oea /oleR oeb  _].
  move => i x y oi lxy; rewrite /f; Ytac h1; Ytac h2 => //.
  by case:  h1; apply: (oleT lxy h2).
- move => i x oi limx; rewrite /ocontinuous_at /f.
  Ytac lxi.
  apply: (olimit_econst oa). 
    exists  \0o; first by apply: limit_pos. 
    by move => j _ jx; rewrite (Y_true (oleT  (proj1 jx) lxi)).
  case: (oleT_el (proj31 limx) oi) => // lt. 
  apply: (olimit_econst ob); exists (osucc i).
    by move/limit_ordinal_P: limx => [_]; apply.
   by move => j /oleSltP /oltNge ja jb; Ytac0.
- move => x ox; rewrite /g; Ytac h.
    apply: (olimit_econst oa); exists x => //. 
    by move => i ia ib; rewrite /f; Ytac0.
  apply: (olimit_econst ob); exists \0o; first by  apply: olt_0omega.
  move => i _ ia; rewrite /f; Ytac hh => //; case: h; exact:(ole_ltT hh ia).    - move => [qa qb].
  move: qb; rewrite /g Y_false; last by case.
  move => h1; move: (h1 a lab) => [y lyo h2].
  by move: (h2 y  (oleR (proj31_1 lyo)) lyo); Ytac0; case.
Qed.


Lemma cont_fun_th4_ex2 a b
   (f := fun i x => Yo (i <o x /\ x <=o omega0) a b) 
   (g := fun x => Yo (x = omega0) a b):
   a <o b -> 
   [/\  
      forall i j x, i <=o j -> ordinalp x  -> f i x <=o f j x,
      forall i x, ordinalp i -> limit_ordinal x -> ocontinuous_at (f i) x,
      forall x, ordinalp  x -> olimit (fun i => f i x) omega0 (g x) &
      ~ocontinuous_at g omega0].
Proof.
move => lab; move: (proj1 lab) => leab.
move: (leab) => [oa ob _]; move: (oleR oa) (oleR ob) => laa lbb.
split.
- move => i j x lij ox; rewrite /f.
  case: (oleT_el ox OS_omega) => ll; last first.
    by move:(oltNge ll) => ngr; rewrite ! Y_false => //; case.
  case: (p_or_not_p (j <o x)) => ljx.
    by rewrite (Y_true (conj ljx ll)) (Y_true (conj (ole_ltT lij ljx) ll)).
  have  aux: ~ (j <o x /\ x <=o omega0)  by case.
  by Ytac0; Ytac h2.
- move => i x oi lx; rewrite /f/ocontinuous_at.
  case: (oleT_el (proj31 lx) oi) => lix.
    rewrite Y_false;last by case =>q; case:(oleNgt lix).
    apply: (olimit_econst ob).
    exists \0o; first by apply: limit_pos. 
    move => j ja jb; rewrite Y_false //; case =>  ji _.
    by move:(oleNgt (oleT (proj1 jb) lix) ji).
  case: (oleT_el (proj31 lx) OS_omega) => lxo.
    rewrite (Y_true (conj lix lxo)).
    apply: (olimit_econst oa).
    exists (osucc i).
        by move/limit_ordinal_P: lx => [_ h]; move: (h _ lix).
      move => k /oleSltP ka kb; rewrite Y_true => //;split => //.
    apply: (oleT (proj1 kb) lxo).  
  move: (oltNge lxo) => nlxo.
  rewrite Y_false; last by case.
  apply: (olimit_econst ob); exists (osucc omega0).
    by move/limit_ordinal_P: lx => [_ h]; move: (h _ lxo).
  by move => k /oleSltP /oltNge ka kb;rewrite Y_false => //; case.
- move => x ox; rewrite /g. 
  case: (oleT_ell ox OS_omega) => cxo.
  + Ytac0; apply:(olimit_econst oa).
    exists \0o; first by  apply: olt_0omega.
    move => i ia ib; rewrite /f cxo Y_true => //; split => //.
    apply: (oleR OS_omega). 
  + rewrite (Y_false (proj2 cxo)); apply:(olimit_econst ob).
    exists x =>  //.
    by move => k /oleNgt ka kb; rewrite /f Y_false => //; case.  
  + rewrite (Y_false (nesym (proj2 cxo))); apply:(olimit_econst ob).
    exists \0o; first by  apply: olt_0omega.
    move => i ia ib; rewrite /f Y_false => //; case => _.
    exact:(oltNge cxo).
- rewrite /ocontinuous_at /g; Ytac0; move => [ha hb].
  move:ha =>[y yo yp]; move: (yp y (oleR (proj31_1 yo)) yo).
  by rewrite (Y_false (proj2 yo)); apply: (oltNge lab).
Qed.
 

(* ------------- *)

Lemma sum_monotony (a1 := \1o)(b1:= omega0)
      (a2 := omega0 *o \2o)(b2:= omega0 *o (osucc \2o))
      (a3 := omega0)(b3:= omega0 +o \1o):
  [/\ a1 <o b1 /\ a1 +o b1 <o b1 +o a1,
   a2 <o b2 /\ a2 +o b2 = b2 +o a2 &
   a3 <o b3 /\ b3 +o a3 <o a3 +o b3 ].
Proof.
have ha := olt_1omega.
have hb := OS_omega.
have hc := olt_0omega.
have hd := (OS_succ OS2).
have he := (OS_sum2 hb hb).
split; split.
- done.
- by rewrite (osum_int_omega ha) (osucc_pr hb); apply: oltS.
- apply: (oprod_Meqlt (oltS OS2) hc).
- rewrite - (oprodD  OS2 hd hb) - (oprodD hd OS2 hb) - (succ_of_nat NS2).
  by rewrite (osum2_2int NS2 NS3) (osum2_2int NS3 NS2) csumC.
- by rewrite /a3/b3  (osucc_pr hb); apply: oltS.
- rewrite /a3/b3 (osumA hb hb OS1) (osucc_pr he).
  by rewrite - (osumA hb OS1 hb) (osum_int_omega ha); apply: (oltS he).
Qed.

Lemma oprod_comm_deg a b: \0o <o a -> \0o <o b -> odegree a = odegree b ->
   oprod_comm a b -> a +o b = b +o a.
Proof.
move =>  ap bp dab c.
have Q u v: natp u -> natp v ->  u +o v = v +o u.
  by move => aN bN;rewrite (osum2_2int aN bN) csumC (osum2_2int bN aN).
case/(oprod2_comm (proj32_1 ap) (proj32_1 bp)):c.
  by move => az; case: (nesym (proj2 ap)).
case; first  by move => bz; case: (nesym (proj2 bp)).
case.
  wlog: a b ap bp dab / (oprod2_comm_P4 a b).
    move => H; case => //.
     by move => h; apply: (H a b) => //; left.
    by move => h; symmetry;apply: (H b a ) => //; left.
  move => [c [e [n [m [cc cl oe [nN mN xv dd yv]]]]]] _.
  have oem := (OS_prod2 oe (OS_nat mN)).
  have oen := (OS_prod2 oe (OS_nat nN)).
  have fp:  \0o <o oopow (e *o m) by  apply: oopow_pos.
  move: dab; rewrite yv (odegree_prod fp ap) (odegree_opow oem).
  have ->: odegree a =  e *o n.
    rewrite /odegree (Y_false (nesym (proj2 ap))) xv.
    by rewrite (proj43  (cnf_and_val_pb (proj1 cc))).
  rewrite - (oprodD (OS_nat mN) (OS_nat nN) oe) (Q m n mN nN).
  rewrite (oprodD (OS_nat nN)  (OS_nat mN) oe). 
  rewrite -{1} (osum0r oen); move / (osum2_simpl OS0 oem oen) => <-.
  by rewrite oopow0 (oprod1l (proj32_1 ap)).
case.
  by move => [ /(oltP OS_omega)  aN /(oltP OS_omega) bN]; rewrite Q.
move => [e [n [m [oe nN mN]]]] => av bv.
case: (oleT_el OS_omega oe) => ef; last first.
  by rewrite av bv;apply:Q; apply/(oltP OS_omega); apply: opow_2int1 => //;
    apply/(oltP OS_omega).
move: (odegree_infinite ef)  => enz.
have np := (olt_leT olt_0omega ef).
have H: forall k, natp k -> odegree (e ^o k) = (odegree e) *o k.
  apply: Nat_induction.
    by rewrite opowx0 oprod0r odegree_one.
  move => k kN Hrec.
  rewrite (succ_of_nat kN) (opow_succ oe (OS_nat kN)).
  rewrite  (odegree_prod (opow_pos np (OS_nat kN)) np).
  by rewrite Hrec (oprod2_succ (OS_degree oe) (OS_nat kN)).
move: dab; rewrite  av bv (H _ nN) (H _ mN).
by move/(oprod2_simpl (OS_nat nN) (OS_nat mN) enz) => ->.
Qed.

Section InfiniteSum.

Variables (f r: Set). 
Let E := substrate r.
Let io := induced_order r.
                       
Hypothesis wor: worder r.
Hypothesis fprop: [/\ fgraph f, domain f = E & allf f ordinalp].

Definition ipartial_order I := 
  order_sum (io I) (Lg I (fun i => ordinal_o (Vg f i))).
Definition ipartial_sum I := osum (io I) (restr f I).

Lemma isum_q1 I: sub I E -> worder_on (io I) I.
Proof.
move => h; exact: (conj (induced_wor wor h) (iorder_sr (proj1 wor) h)).
Qed.

Lemma isum_q2 I: sub I E  -> worder (ipartial_order I).
Proof.
move: fprop => [qa qb ofs] seN.
move:(isum_q1 seN) => h.
apply: orsum_wor; hnf; aw; trivial  => x xe; rewrite LgV//.
by apply: ordinal_o_wor; apply: ofs; rewrite qb; apply: seN.
Qed.

Lemma isum_q4 I: sub I E -> 
  orsum_ax (io I)(Lg I (fun z => ordinal_o (Vg f z))).
Proof.
move:fprop => [qa qb ofs] seN.
move:(isum_q1 seN) => [[or _ ] sr].
split => //; hnf; aw; trivial; move => t tE; rewrite LgV//;rewrite - qb in seN.
exact: (proj1 (ordinal_o_wor (ofs _ (seN _ tE)))).
Qed.

Lemma isum_q5 I: sub I E -> 
  substrate (ipartial_order I) = disjointU (restr f I).
Proof.
move =>  En; rewrite (orsum_sr (isum_q4 En)).
congr disjointU; rewrite  /fam_of_substrates Lgd; apply: Lg_exten => i iE.
by rewrite LgV// ordinal_o_sr.
Qed.

Lemma isum_q6 I x: 
   inc x (disjointU (restr f I)) <-> 
   [/\ inc (Q x) I, inc (P x) (Vg f (Q x)) & pairp x].
Proof.
apply: (iff_trans (@disjointU_P (Lg I (Vg f)) x)). 
rewrite Lgd; split => - [qa qb qc]; split => //; move: qb;rewrite LgV//.
Qed.

Lemma isum_q7 I (s:= disjointU (restr f I)) :sub I E -> 
   forall x y, gle (ipartial_order I) x y  <->
   [/\ inc x s, inc y s &
    glt r (Q x)  (Q y) \/ Q x = Q y /\ (P x) <=o (P y)].
Proof.
move => seN; move: (isum_q4 seN) => ax x y.
apply: (iff_trans (orsum_gleP _ _ x y)).
rewrite - (orsum_sr ax) (isum_q5 seN) -/s.
split; move =>[xs ys etc]; split => //; case: etc.
- by move/iorder_gltP => /proj33;left.
- move /isum_q6: xs =>[ra rb rc].
  move => [sa]; rewrite LgV//;move/graph_on_P1 =>[ _ rd re]; right; split => //.
  rewrite - (proj32 fprop) in seN.
  move:(Os_ordinal (proj33 fprop _ (seN _ ra))) => os.
  by split => //; apply: os.
- move => h; left; apply/iorder_gltP.
  by move /isum_q6: xs =>[ra _ _ ]; move /isum_q6: ys =>[rb _ _]. 
- move =>[ha /proj33 hb]; right; split => //.
  move /isum_q6: xs =>[ra rb _].
  move /isum_q6: ys =>[_ ]; rewrite - ha => rc _.
  by rewrite LgV//;  apply/graph_on_P1. 
Qed.                                            



Lemma isum_q7_lt I (s:= disjointU (restr f I)) :sub I E -> 
   forall x y, glt (ipartial_order I) x y  <->
   [/\ inc x s, inc y s &
    glt r (Q x)  (Q y) \/ Q x = Q y /\ (P x) <o (P y)].
Proof.
move => h x y; move: (isum_q7 h x y) => h1.
split.
   move => [/h1  [sa sb sc] sd]; split => //; case: sc => h3; first by left.
   move: h3 => [h4 h5];right; split => //; split => // sp; case: sd.
   move/isum_q6: sa => /proj33 px.
   move/isum_q6: sb => /proj33 py.
   by apply: pair_exten.  
move =>[xs ys etc]; split.
   apply/h1; split => //; case: etc; first by left.
   move =>[h3 h4]; right; split => //; apply: (proj1 h4).
by move => eq; case: etc; rewrite eq; case => // _; case.
Qed.


Lemma isum_q8 u v:
  ordinalp u -> ordinalp v ->
  forall x y, gle (order_sum2 (ordinal_o u) (ordinal_o v)) x y <->
    [/\ inc x (dsum u v), inc y (dsum u v)                   
     & [\/ [/\ Q x = C0, Q y = C0 & (P x) <=o (P y)],
           [/\ Q x <> C0, Q y <> C0 & (P x) <=o (P y)]
         | Q x = C0 /\ Q y <> C0]].
Proof.
move => ou ov x y.
move: C0_ne_C1 C1_ne_C0 => nea neb.
have aux z: inc z (dsum u v) -> ordinalp (P z). 
  move/candu2P => /proj2; case => - [vv _].
     by apply (Os_ordinal ou).
     by apply (Os_ordinal ov).
apply: (iff_trans (orsum2_gleP (ordinal_o u) (ordinal_o v) x y)).
rewrite ! ordinal_o_sr; split; move => [qa qb qc]; split => //; case: qc.
- move => [sa sb sc]; constructor 1; split => //.
  split; [apply: (aux _ qa) | apply: (aux _ qb) | by case/ordo_leP: sc].
- move =>[sa sb sc]; constructor 2; split => //.
  split; [apply: (aux _ qa) | apply: (aux _ qb) | by case/ordo_leP: sc].
- by move => sa; constructor 3.
- move => [sa sb /proj33 sc]; constructor 1; split => //.
  apply/ordo_leP; split => //.
   by case/ candu2P: qa => _; case => - [] // _; rewrite sa.
  by case/ candu2P: qb => _; case => - [] // _; rewrite sb. 
- move => [sa sb /proj33 sc]; constructor 2; split => //.
  apply/ordo_leP; split => //.
      by case/ candu2P: qa => _; case => - [] // _; rewrite sa. 
    by case/ candu2P: qb => _; case => - [] // _; rewrite sb. 
- by move => sa; constructor 3.
Qed.

  
Lemma isum_p0 I: ipartial_sum I = ordinal (ipartial_order I).
Proof.
rewrite /ipartial_sum /ipartial_order /osum; f_equal; f_equal.
by rewrite /Lgcomp; aw; apply: Lg_exten => t tE /=; rewrite LgV.
Qed.


Lemma isum_p1 I: sub I E -> ordinalp (ipartial_sum I).
Proof.
by rewrite isum_p0 => h; apply: OS_ordinal; apply: isum_q2.
Qed.

Lemma isum_p2: ipartial_sum emptyset = \0o.
Proof.
apply: ordinal0_pr1; rewrite orsum_sr.
  apply/set0_P => t /disjointU_P/proj31; rewrite /fam_of_substrates !Lgd.
  by move/in_set0.
hnf; move: (isum_q1 (@sub0_set E)) =>[[or _] ->];saw.
by hnf; aw => i /in_set0.
Qed. 

Lemma isum_p3 n: inc n E -> ipartial_sum  (singleton n) = Vg f n.
Proof.
move => nN.
move:(fprop) => [hb hc hd].
have oi: ordinalp (Vg f n) by  apply: hd; ue.
move: (set1_1 n) => inn.
rewrite isum_p0.
have E1n: sub (singleton n) E by move => i /set1_P ->.
have wo1 := (isum_q2 E1n). 
apply: ordinal_o_isu2 => //.
set w := substrate (ipartial_order (singleton n)).
have wP x: inc x w <-> [/\ Q x = n, inc (P x) (Vg f n) & pairp x].
  rewrite /w (isum_q5 E1n); split.
    by move/ (isum_q6) =>[/set1_P ->].
  move => [sa sb sc]; apply/isum_q6; rewrite sa; split; fprops.
have ax1: lf_axiom P w (Vg f n) by move => t/wP [].
exists (Lf P w (Vg f n)).
move: (proj1 wo1) (proj1 (ordinal_o_wor oi))=> ov fon.
split => //.
  rewrite ordinal_o_sr; saw; apply: lf_bijective => //.
    by move => x y /wP[ sa sb {2} <-] /wP [sd se {2} <-] ->; rewrite sa sd.
  move => y yi; exists (J y n); aw;trivial; apply/wP; aw; split; fprops.
move => x y; rewrite lf_source => xw yw; rewrite !LfV //.
move /wP: (xw) => [sa sn _]; move /wP: (yw) => [sc sd _].
split. 
  move/(isum_q7 E1n x y)=>[_ _ ra]; apply/ordo_leP; split => //.
  by move: ra; rewrite sa sc; case; case => // _ /proj33.
move/ordo_leP =>[_ _] h; apply/(isum_q7 E1n x y).
rewrite - (isum_q5 E1n); split => //; rewrite sa sc; right; split => //.
by split => //; apply:(Os_ordinal oi).
Qed.

Lemma isum_p4 I1 I2: sub I1 E -> sub I2 E ->
  (forall i j, inc i I1 -> inc j I2 -> glt r i j) ->
  (ipartial_sum I1) +o (ipartial_sum I2) = ipartial_sum (I1\cup I2).
Proof.
move => E1N E2N lE1E2.
have E12N: sub (I1 \cup I2) E by apply: setU2_12S. 
move:(fprop) =>[ha hb hc].
rewrite 3! isum_p0.
move:(isum_q2 E1N) (isum_q2 E2N) (proj1 (isum_q2  E12N)).
move:(isum_q5  E1N) (isum_q5 E2N) (isum_q5 E12N).
set s1 := ipartial_order  _; set s2 := ipartial_order  _;
    set s3:= ipartial_order  _.
move => sr1 sr2 sr3 wor1 wor2 or3.
apply: (orsum_invariant5 wor1 wor2).
move: (orsum2_osr (proj1 wor1) (proj1 wor2)) =>[or4 sr4].
have ax:  lf_axiom P (dsum (substrate s1) (substrate s2)) (substrate s3).
  rewrite sr1 sr2 sr3;move => t /candu2P [pt]; case; case.
    by move/isum_q6=>[qa qb qc] qd; apply/isum_q6; split => //;  apply: setU2_1.
  by move/isum_q6=>[qa qb qc] qd; apply/isum_q6; split => //;  apply: setU2_2.
have qa a: inc a (substrate s1) -> inc (Q a) I1.
  by rewrite sr1 => /disjointU_P/proj31; aw. 
have qb a: inc a (substrate s2) -> inc (Q a) I2.
  by rewrite sr2 => /disjointU_P/proj31; aw.
have bp: bijection_prop (Lf P (substrate (order_sum2 s1 s2)) (substrate s3))
     (substrate (order_sum2 s1 s2)) (substrate s3).
  saw; rewrite sr4; apply: lf_bijective; first exact.
    move => x y /candu2P [px qx] /candu2P [py qy] sp; apply: pair_exten => //.
    case: qx; case: qy; move =>[sa ->][sc ->] //.
      by case: (proj2 (lE1E2 _ _ (qa _ sc) (qb _ sa))); rewrite sp.
     by case: (proj2 (lE1E2 _ _ (qa _ sa) (qb _ sc))); rewrite sp.
     rewrite sr3; move => y /disjointU_P []; rewrite Lgd => qd.
     rewrite LgV// => qe qf; case /setU2_P: qd => qd.
     exists (J y C0);aw;trivial;apply:candu2_pra; rewrite sr1.
     by apply/disjointU_P; aw; rewrite LgV.
  exists (J y C1); aw;trivial; apply:candu2_prb;rewrite sr2.
  by apply/disjointU_P; aw; rewrite LgV.
suff : fiso_prop (Lf P (substrate (order_sum2 s1 s2)) (substrate s3))
     (order_sum2 s1 s2) s3.
  by move => iso; exists (Lf P (substrate (order_sum2 s1 s2)) (substrate s3)).
hnf; aw; rewrite sr4 => x y xd yd; rewrite !LfV//.
move/candu2P:(xd) => [px qx]; move/candu2P: (yd) => [py qy].
split.
  move/orsum2_gleP =>[_ _ etc].
  apply/(isum_q7 E12N); rewrite - (isum_q5  E12N); split; fprops.
  case: etc.
  - by move =>[sa sb sc]; move/(isum_q7 E1N): sc => /proj33.
  - by move =>[sa sb sc]; move/(isum_q7 E2N): sc => /proj33.
  - move => [pa pb];case: qx;case; last by rewrite pa => _ h; case: C0_ne_C1.
    move => ps1 _ ; case: qy; case => // ps2 _.
    left; move:(qa _ ps1) (qb _ ps2) => pe qe; exact: (lE1E2 _ _ pe qe). 
move/(isum_q7 E12N) => [_ _ h]; apply/orsum2_gleP; split => //. 
move: (isum_q5 E1N) (isum_q5 E2N) => a1 a2.
case: h.
  move => h.
  case: qx; case: qy; move =>[sa sb][sc sd].
  - constructor 1; split => //; apply/(isum_q7 E1N).
    by rewrite - a1; split => //; left.
  - constructor 3; split => //; rewrite sb; fprops.
  - case: (not_le_gt (proj1 wor) (proj1 h) (lE1E2 _ _ (qa _ sa) (qb _ sc))). 
  - constructor 2; rewrite sd sb; split; fprops; apply/(isum_q7 E2N).
    by rewrite - a2; split => //; left.
move => [sx  sy].
case: qx; case: qy; move =>[sa sb][sc sd].
- constructor 1; split => //;apply/(isum_q7 E1N).
  by rewrite - a1; split => //; right.
- constructor 3; split => //; rewrite sb; fprops.
- by case : (proj2 (lE1E2 _ _ (qa _ sa) (qb _ sc))).
- constructor 2; rewrite sd sb; split; fprops;  apply/(isum_q7 E2N).
  by rewrite - a2; split => //; right.
Qed.

Lemma isum_p5 i j: glt r i j ->
  ipartial_sum (doubleton i j) = Vg f i +o Vg f j.
Proof.
move => lij.
move: (arg1_sr (proj1 lij)) (arg2_sr (proj1 lij)) => iE jE.
have h: (forall i0 j0,
     inc i0 (singleton i) -> inc j0 (singleton j) -> glt r i0 j0).
  by move => i0 j0 /set1_P -> /set1_P ->.
move: (isum_p4 (set1_sub iE) (set1_sub jE) h).
by rewrite (isum_p3 iE) (isum_p3 jE) setU2_11.
Qed.

  

Lemma isum_p6 a b: ordinalp a -> ordinalp b ->
  b <> \0o -> ipartial_sum E = a +o b ->
  exists n u v, [/\ inc n E, ordinalp u, ordinalp v, v <> \0o &
           [/\  Vg f n = u +o v, 
               a = (ipartial_sum (Zo E (fun t => glt r t n))) +o u &
               b = v +o (ipartial_sum (Zo E (fun t => glt r n t))) ]].
Proof.                                        
move =>  oa ob bnz. 
have or := (proj1 wor).
move: (fprop) => [fgf df ofs].
move: C0_ne_C1 C1_ne_C0 => nea neb.
pose oE E := ipartial_order E.
pose oxy x y := (order_sum2 (ordinal_o x) (ordinal_o y)).
rewrite {1} /osum2 isum_p0-/(oE E) -/(oxy _ _).
set osig := oE E.
set oab := oxy a b => eqa.
have Hu c: ordinalp c -> forall x y, inc x c -> inc y c ->
   (gle (ordinal_o c) x y <-> x <=o y). 
  move => oc x y xc yc; split.
    by move/ordo_leP =>[_ _ s]; split => //; apply: (Os_ordinal oc).
  by move => /proj33 s; apply/ordo_leP.
have He x y: ordinalp x -> ordinalp y -> worder (oxy x y).
  move => /ordinal_o_wor xa /ordinal_o_wor xb.
  by apply:orsum2_wor.
have Ha x y: ordinalp x -> ordinalp y -> substrate (oxy x y) = dsum x y. 
  move => /ordinal_o_wor/proj1 qa /ordinal_o_wor/proj1 qb.
  by rewrite (orsum2_sr  qa qb) ! ordinal_o_sr.
have wosig : worder osig by  apply: isum_q2.
have woab: worder oab by apply: He.
move:(Ha _ _ oa ob); rewrite -/oab  => soab.
have sosig : substrate osig = disjointU f.
  by rewrite isum_q5 // -df restr_to_domain.
have: oab \Is osig.
  move: (ordinal_o_is woab); rewrite - eqa => is1.
  exact: (orderIT is1 (orderIS (ordinal_o_is wosig))).
move =>[g [o1 o2 [bg sg tg] gm]].
have fg := proj1 (proj1 bg).
have zb: inc \0o b by apply/(oltP ob); apply: ord_ne0_pos.
have ha: inc (J \0o C1) (source g).
  by rewrite sg soab; apply: candu2_prb.
move: (Vf_target fg ha).
rewrite tg sosig; move/setUf_P.
rewrite/disjointU_fam; rewrite df; aw; move => [n nN]; rewrite LgV//.
set xr := Vf g (J \0o C1) => hb. 
move/indexed_P:(hb) => [hb1 hb2 hb3].
set u := (P xr).
have oan:  ordinalp (Vg f n). by apply:ofs; ue.
have lt1: u <o (Vg f n) by apply/oltP.
have ou := proj31_1 lt1.
move:(odiff_pr (proj1 lt1)); set v := _  -o _; move => [ov eq2].
case: (equal_or_not v \0o) => vnz.
  by move: (proj2 lt1); rewrite eq2 vnz (osum0r ou).
exists n,u,v.
set w1 := ipartial_sum _.
set w2 := ipartial_sum _.
have w1p: sub  (Zo E ((glt r)^~ n)) E. by apply: Zo_S.
have w2p: sub  (Zo E [eta glt r n]) E by apply: Zo_S.
have ow1: ordinalp w1 by apply: isum_p1.
have ow2: ordinalp w2 by apply: isum_p1.
have rb x: inc x b -> gle osig xr (Vf g (J x C1)). 
  move => xb. 
  have xs: inc (J x C1) (source g) by rewrite sg soab; apply: candu2_prb.
  apply/(gm _ _ ha xs);apply/(isum_q8 oa ob); rewrite - soab - sg;split => //.
  constructor 2; aw; split => //; apply: ole0x; apply(Os_ordinal ob xb).
have ra x: inc x a -> glt osig (Vf g (J x C0)) xr. 
  move => xb. 
  have xs: inc (J x C0) (source g) by rewrite sg soab; apply: candu2_pra.
  split; last first.
    by move/(proj2 (proj1 bg) _ _ xs ha) /pr2_def.
  apply/(gm _ _ xs ha);apply/(isum_q8 oa ob);rewrite - soab - sg;split => //.
  by constructor 3; aw.
move: (proj2 (proj2 bg)); rewrite sg tg sosig soab => sjg.
have <- : b = v +o w2.
  rewrite -(ordinal_o_o ob).
  move:(ordinal_o_wor ob) (He _ _ ov ow2) => wo1 wo2.
  apply:(ordinal_o_isu1 wo1 wo2); move: wo1 wo2 => [oo1 _] [oo2 _].
  move:(Ha _ _ ov ow2) => sr2.
  move: (isum_q2 w2p) (isum_q5  w2p); set o3 := ipartial_order _ => wo3 sr3.
  have xx: ordinal o3 = w2 by  rewrite /w2 isum_p0.
  move: (ordinal_o_is wo3); rewrite  xx => is1; clear xx.
  move: is1 =>[f3 [or1 or2] [bf3 sf3 tf3] f3m].
  have ff3 := proj1 (proj1 bf3).
  rewrite ordinal_o_sr in tf3.
  rewrite sr3 in sf3.
  pose h x := let y := (Vf g (J x C1)) in
     Yo (Q y = n) (J ((P y) -o u) C0) (J (Vf f3 y) C1).
  have ax: lf_axiom h b (dsum v w2).
    move => x /rb; rewrite /h; set y := Vf _ _.
    move => /(isum_q7 (@sub_refl E))  [qa qb qc].
    move/isum_q6: qb =>[sa sb sc].
    case: qc.
      rewrite hb3 => lt2; rewrite (Y_false (nesym (proj2 lt2))). 
      apply: candu2_prb.
      by Wtac; rewrite sf3; apply/isum_q6; split => //; apply:(Zo_i sa).
    rewrite hb3; move =>[ea se]; rewrite ea; Ytac0; apply: candu2_pra.
    apply/(oltP ov); rewrite - ea in sb; move/(oltP oan): sb; rewrite eq2.
    move:(odiff_pr se) => [ma mb]; rewrite {1} mb;exact:(osum_Meqltr ma ov ou).
  have Ta x: inc x b -> Q (Vf g (J x C1)) <> n -> 
      inc (Vf g (J x C1)) (source f3). 
    move => xa; move/(isum_q7 (@sub_refl E)) : (rb x xa).
    rewrite sf3; move => [_ /isum_q6 [qa qb qc]]; case.
      move => [ta tb] tc; apply/isum_q6; split => //.
      by apply: (Zo_i qa); split => //; rewrite - hb3.
    by move/proj1 => <-; rewrite hb3.
  have bp: bijection (Lf h b (dsum v w2)).
    apply: lf_bijective => //.
      move => x y xa ya; rewrite /h => aux. 
      suff:  (J x C1) = (J y C1) by apply: pr1_def.
      have xd: inc (J x C1) (dsum a b) by apply: candu2_prb.
      have yd: inc (J y C1) (dsum a b) by apply: candu2_prb.
      have xsg: inc (J x C1) (source g) by rewrite sg soab. 
      have ysg: inc (J y C1) (source g) by rewrite sg soab.
      apply: (proj2 (proj1 bg) _ _ xsg ysg); move: aux.
      rewrite /h; set z1 := Vf g _; set z2 := Vf g _;Ytac na; Ytac nb.
      + move/rb: xa => /(isum_q7 (@sub_refl E)) /proj33; case.
          by move/proj2; rewrite na hb3.
        move/rb: ya => /(isum_q7 (@sub_refl E)) /proj33; case.
          by move/proj2; rewrite nb hb3.
        rewrite -/z1 -/z2 -/u; move => [_ le1] [_ le2].
        move: (Vf_target fg xsg) (Vf_target fg ysg).
        rewrite tg sosig; move => /disjointU_P => /proj33 px.
        move => /disjointU_P => /proj33 py /pr1_def sd.
        apply: pair_exten => //; last by rewrite na nb.
        by move: (odiff_pr le1) (odiff_pr le2) =>[ma ->][mc ->]; rewrite sd.
      + by move => /pr2_def. 
      + by move => /pr2_def. 
      + by move => /pr1_def; apply: (proj2 (proj1 bf3)); apply: Ta.
    move => y /candu2P [pp]; case; move => [sa sb].
      move/(oltP ov): (sa) => sc.
      move: (odiff_pr1 ou (proj31_1 sc)) => sd.
      have: inc (J (u +o (P y)) n)  (disjointU f).
        apply/disjointU_P; aw; rewrite df; split; fprops.
        apply/(oltP oan); rewrite eq2. apply: (osum_Meqlt _ ou).
        by apply/(oltP ov).
      move/sjg  =>[z zab -zv].
      move/candu2P: zab => [pz]; case; move =>[zu zw].
        move: (ra _ zu); rewrite - zw pz - zv.
        move/(isum_q7_lt (@sub_refl E)) =>[_ h3]; rewrite hb3; aw.
        move: (osum_Mle0 ou (proj31_1 sc)) => ll.
        by case; case => // _ /oltNge; case.
      exists (P z) => //;  rewrite /h  - zw pz - zv - sb; aw; Ytac0. 
      by rewrite  sd pp.
    rewrite - tf3 in sa; move: (proj2 (proj2 bf3) _ sa); rewrite sf3.
    move => [x /isum_q6 [/Zo_P [qa qb] qc] qd] qe.
    have: inc x (disjointU f) by apply/disjointU_P; split => //; ue.
    move /sjg =>[z zab -zv].
    move/candu2P: zab => [pz]; case; move =>[zu zw].
      move: (ra _ zu); rewrite - zw pz - zv.
      move/(isum_q7_lt (@sub_refl E)) =>[_ h3]; rewrite hb3; case.
        by move=> h4; move: (not_le_gt or (proj1 qb) h4).
       by move => [nn]; case (proj2 qb).
    exists (P z) => //; rewrite /h - zw pz - zv (Y_false (nesym (proj2 qb))).
    by rewrite zw - sb - qe pp.
  exists (Lf h b (dsum v w2)).
  have tor:= (worder_total (ordinal_o_wor ob)).
  apply: total_order_isomorphism; aw;trivial; first by  rewrite ordinal_o_sr.  
  hnf => x y xa ya /=; rewrite !LfV //; move =>  lea.
  have xd: inc (J x C1) (dsum a b) by apply: candu2_prb.
  have yd: inc (J y C1) (dsum a b) by apply: candu2_prb.
  have xsg: inc (J x C1) (source g) by rewrite sg soab.
  have ysg: inc (J y C1) (source g) by rewrite sg soab.
  have /(gm _ _ xsg ysg) lb:  gle oab (J x C1) (J y C1).
    apply/(isum_q8 oa ob); split => //; constructor 2; aw.
    by split=> //; apply/(Hu _ ob _ _ xa ya).
  move/(isum_q7 (@sub_refl E)): lb.
  rewrite /h; set z1 := (Vf g (J x C1)); set z2 := (Vf g (J y C1)).
  move: (rb _ xa); rewrite -/z2 => /(isum_q7 (@sub_refl E)).
  move/proj33; rewrite hb3 -/u; move => z1prop.
  have f3sm s t:  inc s (source f3) -> inc t (source f3) -> 
     ((glt r (Q s) (Q t) \/ Q s = Q t /\ P s <=o P t) <-> Vf f3 s <=o Vf f3 t).
    move => ss ts.  
    move: (Vf_target ff3 ss) (Vf_target ff3 ts); rewrite tf3 => sw tw.
    apply: iff_trans (iff_trans (f3m s t ss ts) (Hu _ ow2 _ _  sw tw)).
    have aux: sub (Zo E ((glt r) n)) E by apply: Zo_S.
    split; last by case /(isum_q7 aux).
    by move => H; apply/(isum_q7 aux); rewrite - sf3.
  move => [pa pb].
  move/isum_q6: (pa) => [z11 z12 z13].
  move/isum_q6: (pb) => [z21 z22 z23].
  case.
    move => lt12; case: z1prop.
      move => lt2n; move: (lt_lt_trans or lt2n lt12) => lt1n.
      rewrite (Y_false (nesym (proj2 lt1n))) (Y_false (nesym (proj2 lt2n))).
      have z1f3: inc z1 (source f3).
        by  rewrite sf3; apply/isum_q6; split => //; apply: Zo_i => //.
      have z2f3: inc z2 (source f3).
        by  rewrite sf3; apply/isum_q6; split => //; apply: Zo_i => //.
      apply/(isum_q8 ov ow2); split.
      - apply: candu2_prb; Wtac. 
      - apply: candu2_prb; Wtac.
      - by constructor 2; aw; split=>//; apply/(f3sm z1 z2 z1f3 z2f3); left.
    move => [ea la]; rewrite ea -/z1 (Y_false (nesym (proj2 lt12))); Ytac0.
    apply/(isum_q8 ov ow2); split.
    - apply: candu2_pra; move: (odiff_pr la) => [ma mb].
      apply/(oltP ov); apply: (osum_Meqltr ma ov ou); rewrite - mb - eq2.
      by apply/(oltP oan); rewrite ea.
    - apply: candu2_prb; Wtac; rewrite sf3; apply/isum_q6; split => //. 
      apply: Zo_i => //; ue.
    - by constructor 3; aw. 
  move => [pc pd]; case: z1prop.
     move => lt2n; rewrite - pc 2! (Y_false (nesym (proj2 lt2n))).
    have z1f3: inc z1 (source f3).
      by rewrite sf3;apply/isum_q6; split => //; apply: Zo_i => //; ue.
    have z2f3: inc z2 (source f3).
        rewrite sf3; apply/isum_q6; split => //; apply: Zo_i => //; ue.
    apply/(isum_q8 ov ow2); split.
    - apply: candu2_prb; Wtac. 
    - apply: candu2_prb; Wtac.
    - by constructor 2; saw; apply/(f3sm z1 z2 z1f3 z2f3); right.
  move => [ea la]; rewrite - pc - ea; Ytac0; Ytac0.
  move: (oleT la pd) => lb.
  move: (odiff_pr la) (odiff_pr lb) => [ma mb] [mc md].
  have aux: P z1 -o u <=o P z2 -o u.
     by apply:(osum_Meqler ma mc ou); rewrite - mb - md.
  apply/(isum_q8 ov ow2); split.
  - apply: candu2_pra; apply/(oltP ov); apply:(osum_Meqltr ma ov ou).
    by rewrite - mb - eq2; apply/(oltP oan); rewrite ea.
  - apply: candu2_pra; apply/(oltP ov); apply:(osum_Meqltr mc ov ou).
    by rewrite - md - eq2; apply/(oltP oan); rewrite ea pc.
  - by constructor 1; aw. 
suff <- : a = w1 +o u  by split.
rewrite -(ordinal_o_o oa).    
move:(ordinal_o_wor oa) (He _ _ ow1 ou) => wo1 wo2.
apply:(ordinal_o_isu1 wo1 wo2); move: wo1 wo2 => [oo1 _] [oo2 _].
move:(Ha _ _ ow1 ou) => sr2.
move: (isum_q2 w1p) (isum_q5 w1p); set o3 := ipartial_order _ => wo3 sr3.
have xx: ordinal o3 = w1 by rewrite /w1 isum_p0. 
move: (ordinal_o_is wo3); rewrite  xx => is1; clear xx.
move: is1 =>[f3 [or1 or2] [bf3 sf3 tf3] f3m].
have ff3 := proj1 (proj1 bf3).
rewrite ordinal_o_sr in tf3.
rewrite sr3 in sf3.
pose h x := let y := (Vf g (J x C0)) in
   Yo (Q y = n) (J (P y) C1) (J (Vf f3 y) C0).
have suan: sub u (Vg f n).
  move => t /(oltP ou) => ltu; apply/(oltP oan); rewrite eq2.
   by apply: (olt_leT ltu (osum_Mle0 ou ov)).
have ax: lf_axiom h a (dsum w1 u).
  move => x /ra; rewrite /h; set y := Vf _ _.
  move => /(isum_q7_lt (@sub_refl E)) [qa qb qc].
  move/isum_q6: qa =>[sa sb sc].
  case: qc.
    rewrite hb3 => lt2; rewrite (Y_false (proj2 lt2)); apply: candu2_pra.
    by Wtac; rewrite sf3; apply/isum_q6; split => //; apply:(Zo_i sa).
  rewrite hb3; move =>[sd se]; Ytac0; apply: candu2_prb.
  by apply/(oltP ou). 
  have Ta x: inc x a -> Q (Vf g (J x C0)) <> n -> 
      inc (Vf g (J x C0)) (source f3). 
    move => xa; move/(isum_q7_lt (@sub_refl E)) : (ra x xa).
    rewrite sf3; move => [/isum_q6 [qa qb qc] _]; case.
      move => [ta tb] tc; apply/isum_q6; split => //.
      apply: (Zo_i qa); split => //; ue.
    by rewrite hb3; case.
have bp: bijection (Lf h a (dsum w1 u)).
  apply: lf_bijective => //.
    move => x y xa ya; rewrite /h => aux. 
    suff:  (J x C0) = (J y C0) by apply: pr1_def.
    have xd: inc (J x C0) (dsum a b) by apply: candu2_pra.
    have yd: inc (J y C0) (dsum a b) by apply: candu2_pra.
    have xsg: inc (J x C0) (source g) by rewrite sg soab. 
    have ysg: inc (J y C0) (source g) by rewrite sg soab.
    apply: (proj2 (proj1 bg) _ _ xsg ysg); move: aux.
     rewrite /h; set z1 := Vf g _; set z2 := Vf g _;Ytac na; Ytac nb.
    + move: (Vf_target fg xsg) (Vf_target fg ysg).
      rewrite tg sosig; move => /disjointU_P => /proj33 px.
      move => /disjointU_P => /proj33 py.
      move => /pr1_def ee; apply: pair_exten => //; ue.
    + by move => /pr2_def. 
    + by move => /pr2_def. 
    + by move => /pr1_def; apply: (proj2 (proj1 bf3)); apply: Ta.
  move => y /candu2P [pp]; case; move => [sa sb].
    rewrite - tf3 in sa; move: (proj2 (proj2 bf3) _ sa); rewrite sf3.
    move => [x /isum_q6 [/Zo_P [qa qb] qc] qd] qe.
    have: inc x (disjointU f) by apply/disjointU_P; split => //; ue.
    move /sjg =>[z zab -zv].
    move/candu2P: zab => [pz]; case; move =>[zu zw].
      exists (P z) => //; rewrite /h - zw pz - zv (Y_false (proj2 qb)).
      by rewrite zw - sb - qe pp.
    move: (rb _ zu); rewrite - zw pz - zv.
    move/(isum_q7 (@sub_refl E)) =>[_ h3]; rewrite hb3; case.
      by move=> h4; move: (not_le_gt or (proj1 qb) h4).
     by move => [nn]; case (proj2 qb).
  have: inc (J (P y) n)  (disjointU f).
    by apply/disjointU_P; aw; rewrite df; split; fprops; apply: suan.
  move/sjg  =>[z zab -zv].
  move/candu2P: zab => [pz]; case; move =>[zu zw].
    by exists (P z)=>//; rewrite /h  - zw pz - zv - sb; aw; Ytac0; rewrite pp.
  move: (rb _ zu); rewrite - zw pz - zv.
  move/(isum_q7 (@sub_refl E)) =>[_ h3]; rewrite hb3; aw; case; case => //.
  by move => _ /oleNgt; case; apply/(oltP ou).
exists (Lf h a (dsum w1 u)).
have tor:= (worder_total (ordinal_o_wor oa)).
apply: total_order_isomorphism; aw; trivial;first by  rewrite ordinal_o_sr.  
hnf => x y xa ya /=; rewrite !LfV//; move =>  lea.
have xd: inc (J x C0) (dsum a b) by apply: candu2_pra.
have yd: inc (J y C0) (dsum a b) by apply: candu2_pra.
have xsg: inc (J x C0) (source g) by rewrite sg soab.
have ysg: inc (J y C0) (source g) by rewrite sg soab.
have /(gm _ _ xsg ysg) lb:  gle oab (J x C0) (J y C0).
  apply/(isum_q8 oa ob); split => //; constructor 1; aw.
  by split=> //; apply/(Hu _ oa _ _ xa ya).
move/(isum_q7 (@sub_refl E)): lb.
rewrite /h; set z1 := (Vf g (J x C0)); set z2 := (Vf g (J y C0)).
move: (ra _ ya); rewrite -/z2 => /(isum_q7_lt (@sub_refl E)).
move/proj33; rewrite hb3 -/u; move => z2prop.
have f3sm s t:  inc s (source f3) -> inc t (source f3) -> 
   ((glt r (Q s) (Q t) \/ Q s = Q t /\ P s <=o P t) <-> Vf f3 s <=o Vf f3 t).
  move => ss ts.  
  move: (Vf_target ff3 ss) (Vf_target ff3 ts); rewrite tf3 => sw tw.
  apply: iff_trans (iff_trans (f3m s t ss ts) (Hu _ ow1 _ _  sw tw)).
  have aux: sub (Zo E ((glt r)^~ n)) E by apply: Zo_S.
  split.
     by move => H; apply/(isum_q7 aux); rewrite - sf3.
  by case /(isum_q7 aux).
move => [pa pb].
move/isum_q6: (pa) => [z11 z12 z13].
move/isum_q6: (pb) => [z21 z22 z23].
case.
  move => lt12; case: z2prop.
    move => lt2n; move: (lt_lt_trans or lt12 lt2n) => lt1n.
    rewrite (Y_false (proj2 lt1n))(Y_false (proj2 lt2n)).
    have z1f3: inc z1 (source f3).
      by  rewrite sf3; apply/isum_q6; split => //; apply: Zo_i => //.
    have z2f3: inc z2 (source f3).
      by  rewrite sf3; apply/isum_q6; split => //; apply: Zo_i => //.
    apply/(isum_q8 ow1 ou); split.
    - apply: candu2_pra; Wtac. 
    - apply: candu2_pra; Wtac.
    - by constructor 1; aw; split=>//; apply/(f3sm z1 z2 z1f3 z2f3); left.
  move => [ea la]; rewrite - ea (Y_false (proj2 lt12)); Ytac0.
  apply/(isum_q8 ow1 ou); split.
  - apply: candu2_pra; Wtac; rewrite sf3; apply/isum_q6; split => //. 
    apply: Zo_i => //; ue.
  - by apply: candu2_prb; apply/(oltP ou).
  - by constructor 3; aw. 
move => [pc pd]; case: z2prop.
  move => lt2n; rewrite pc 2! (Y_false (proj2 lt2n)).
  have z1f3: inc z1 (source f3).
    by rewrite sf3;apply/isum_q6; split => //; apply: Zo_i => //; ue.
  have z2f3: inc z2 (source f3).
    by  rewrite sf3; apply/isum_q6; split => //; apply: Zo_i => //.
  apply/(isum_q8 ow1 ou); split.
  - apply: candu2_pra; Wtac. 
  - apply: candu2_pra; Wtac.
  - by constructor 1; aw; split=>//; apply/(f3sm z1 z2 z1f3 z2f3); right.
move => [ea la]; rewrite pc - ea; Ytac0; Ytac0.
move: (ole_ltT pd la) => lb.
apply/(isum_q8 ow1 ou); split.
- by apply: candu2_prb; apply/(oltP ou).
- by apply: candu2_prb; apply/(oltP ou).
- by constructor 2; aw. 
Qed.

Lemma isum_p7a n:
  (ipartial_sum (Zo E (fun t => glt r t n))) <=o  ipartial_sum E.
Proof.
set I := Zo _ _.
set J := E -s I.
have sa: sub I E by apply:Zo_S.
have sb: sub J E by apply:sub_setC.
have sc i j :inc i I -> inc j J -> glt r i j.
  move => /Zo_P [iE la] /setC_P [jE ll].
  case: (total_order_pr1 (worder_total wor) iE jE) => // lc; case: ll.
    apply:Zo_i=> //; apply:(lt_lt_trans (proj1 wor) lc la).
  apply:Zo_i=> //;ue.
move: (isum_p4 sa sb sc); rewrite (setU2_Cr sa) => <-.
by apply: osum_Mle0; apply: isum_p1.
Qed.

Lemma isum_p7b (ps := fun n => (ipartial_sum (Zo E (fun t => glt r t n)))):
  has_greatest r \/
  ipartial_sum E = \osup (fun_image E ps).
Proof.
case: (p_or_not_p (has_greatest r)); [ by left | move => nhg; right].
have ha: ordinalp (ipartial_sum E) by apply: isum_p1.
have hb: ordinal_ub (fun_image E ps) (ipartial_sum E).
  move => y /funI_P [z ze ->]; rewrite /ps; apply: isum_p7a.
move: (ord_ub_sup ha hb); case/ ole_eqVlt => //.
set a := \osup _ => lab.
have oa := (proj31_1 lab).
move: (odiff_pr (proj1 lab)); set b := _ -o _; move =>[ob sab].
case: (equal_or_not b \0o) => bnz.
  by case: (proj2 lab); rewrite sab bnz (osum0r oa).
move: (isum_p6 oa ob bnz sab).
move =>[n [u [v [nE ou ov vnz [qa qb qc]]]]].
set I1 := (Zo E ((glt r)^~ n)).
have i1p: I1 = segment r n.
  set_extens t; first by  move /Zo_P => [sa sb]; apply/segmentP.
  move/segmentP => sa; apply/Zo_P; split => //.
  exact: (arg1_sr (proj1 sa)).
move: (segmentc_pr (proj1 wor) nE). rewrite - i1p => eq2.
have sa: sub I1 E  by apply: Zo_S.
have sb: sub (singleton n) E by move => t/set1_P ->.
have sc i j: inc i I1 -> inc j (singleton n) -> glt r i j.
  by   move=> /Zo_hi ma /set1_P ->.
have sd: ordinalp (ipartial_sum I1) by apply: isum_p1.
move: (isum_p4  sa sb sc); rewrite (isum_p3 nE) qa (osumA sd ou ov) - qb.
set y := ipartial_sum (I1 +s1 n) => yv.
have lay: a <o y.
  rewrite - yv; move: (osum_Meqlt (ord_ne0_pos ov vnz) oa). 
  by rewrite(osum0r oa).
have yT: inc y (fun_image E ps).
  have or := proj1 wor.
  have /(inc_segmentsP wor): segmentp r (I1 +s1 n).
    rewrite eq2; apply: (segmentc_segment _ or).
  case/setU1_P.
    move/funI_P => [m mE mv]; apply/funI_P; exists m => //.
      rewrite /y /ps; apply: f_equal; rewrite mv;  set_extens t.
        move/segmentP => lt; apply:Zo_i => //;exact: (arg1_sr (proj1 lt)).
      by move/Zo_hi => lt; apply/segmentP.
   move => eq;case : nhg; exists n; split;rewrite - eq; fprops.
   by move => x/setU1_P; case; [ move/Zo_hi/proj1 | move ->;  order_tac]. 
have os: ordinal_set (fun_image E ps).
  move => t /funI_P [m mE ->]; apply: isum_p1; apply: Zo_S.
by case: (oleNgt (ord_sup_ub os yT)). 
Qed.


End InfiniteSum.


Lemma isum_p8 f g r: worder r -> fgraph f  -> fgraph g -> 
  domain f = substrate r -> domain g = substrate r -> 
  (forall x, inc x (substrate r) -> Vg f x <=o Vg g x) -> 
  ipartial_sum f r (substrate r) <=o ipartial_sum g r (substrate r). 
Proof.
move => wor fgf fgg df dg le1.
have fp: [/\ fgraph f, domain f = substrate r & allf f ordinalp].
  by split => // t; rewrite  df => /le1 /proj31.
have gp: [/\ fgraph g, domain g = substrate r & allf g ordinalp].
  by split => // t; rewrite  dg => /le1 /proj32.
rewrite 2! isum_p0.
pose rr := (@sub_refl (substrate r)).
move: (isum_q2 wor fp rr)(isum_q2 wor gp rr) => wo1 wo2.
apply: (order_cp2 wo1 wo2).
apply/(order_cp0 (proj1 wo1) (proj1 wo2)) => x y.
have aux : sub (disjointU (restr f (substrate r)))
               (disjointU (restr g (substrate r))).
  move => t /isum_q6 [sa sb sc]; apply/isum_q6; split => //.
  move:(le1 _ sa) => le2; move: (le2) => [oa ob _].
  by apply/(oltP ob); apply: olt_leT le2; apply/(oltP oa).
move/(isum_q7 wor fp rr) =>[xd yd cxy].
by apply/(isum_q7 wor gp rr); split => //; apply: aux.
Qed.

Lemma isum_p9 f E r: worder r -> sub E (substrate r) ->
  [/\ fgraph f, domain f = substrate r & allf f ordinalp] ->
  (forall i, inc i (substrate r -s E) -> Vg f i = \0o) ->
  ipartial_sum f r (substrate r) = ipartial_sum f r E.
Proof.
move => wor esr fp fz.
have rr := (@sub_refl (substrate r)).
move: (isum_q2 wor fp rr)(isum_q2 wor fp esr) => wo1 wo2.
rewrite 2! isum_p0; f_equal; apply:(order_exten (proj1 wo1) (proj1 wo2)).
have eq1: (disjointU (restr f (substrate r))) = (disjointU (restr f E)).
  set_extens t => /isum_q6 [pa pb pc]; apply/isum_q6; split => //.
    case: (inc_or_not (Q t) E) => // nqe.
    have: inc (Q t) (substrate r -s E) by apply /setC_P.
    by move/fz => pz; move: pb; rewrite pz => /in_set0.
  by apply: esr.
move => x y; split.
  move/(isum_q7 wor fp rr) =>[sa sb sc].
  by apply/(isum_q7 wor fp esr); rewrite - eq1.
move/(isum_q7 wor fp esr) =>[sa sb sc].
by apply/(isum_q7 wor fp rr); rewrite eq1.
Qed.


Lemma isum_p10 f E1 E2 r: worder r -> sub E1 E2 -> sub E2 (substrate r) ->
  [/\ fgraph f, domain f = substrate r & allf f ordinalp] ->
  ipartial_sum f r E1 <=o ipartial_sum f r E2.
Proof.
move => wor s12 s2r [fa fb fc].
pose g1 := Lg (substrate r) (fun i => Yo (inc i E1) (Vg f i) \0o).
pose g2 := Lg (substrate r) (fun i => Yo (inc i E2) (Vg f i) \0o).
have ax1: [/\ fgraph g1, domain g1 = substrate r & allf g1 ordinalp].
  rewrite/g1; split; aww; hnf; aw => x xs; rewrite LgV//.  
  Ytac h; [ apply: fc; ue | exact OS0].
have ax2: [/\ fgraph g2, domain g2 = substrate r & allf g2 ordinalp].
  rewrite/g2; split; aww; hnf; aw => x xs; rewrite LgV//.
  Ytac h; [ apply: fc; ue | exact OS0].
have g1p i: inc i (substrate r -s E1) -> Vg g1 i = \0o.
  by move =>/setC_P [xe bad]; rewrite /g1 LgV //; Ytac0.
have g2p i: inc i (substrate r -s E2) -> Vg g2 i = \0o.
  by move =>/setC_P [xe bad]; rewrite /g2 LgV//; Ytac0.
have l12 x: inc x (substrate r) -> Vg g1 x <=o Vg g2 x.
  rewrite /g1 /g2 => xe; rewrite !LgV//; Ytac h.
     rewrite (Y_true (s12 _ h)); apply: oleR; apply: fc; ue.
  by apply: ole0x; Ytac h2; [ apply: fc; ue | apply: OS0].
have g1v: (restr g1 E1) = restr f E1.
  by apply: Lg_exten=> t te;rewrite /g1 LgV//;[ Ytac0 | apply: s2r; apply: s12].
have g2v: (restr g2 E2) = restr f E2.
  by apply: Lg_exten => t te; rewrite /g2 LgV; [ Ytac0 | apply: s2r].
move: (isum_p8 wor (proj31 ax1) (proj31 ax2) (proj32 ax1)
                (proj32 ax2) l12).     
rewrite (isum_p9 wor (sub_trans s12 s2r) ax1 g1p) (isum_p9 wor s2r ax2 g2p).
by rewrite /ipartial_sum g1v g2v.
Qed.

Lemma isum_p11 f r r' g
  (fg := Lg (substrate r') (fun i => Vg f (Vf (inverse_fun g) i))):
  worder r -> order_isomorphism g r r' ->
  [/\ fgraph f, domain f = substrate r & allf f ordinalp] ->
  ipartial_sum f r (substrate r) =
  ipartial_sum fg r' (substrate r'). 
Proof.
move =>  wor isog axf.
have rr: r \Is r' by exists g.
have axg: [/\ fgraph fg, domain fg = substrate r' & allf fg ordinalp].
   move: axf =>[qa qb qc].
   rewrite /fg Lgd; split; fprops; hnf; aw => x xsr; rewrite LgV//; apply: qc.
   move: isog =>[_ _ /inverse_bij_bp [/proj1/proj1 bg sg tf] _].
   rewrite qb; Wtac.
move:(worder_invariance rr wor) => wor' {rr}.
move: (isum_q2 wor axf (@sub_refl (substrate r))) => woa.
move:(isum_q2 wor' axg (@sub_refl (substrate r'))) =>wob.
move: (isum_q5 wor axf (@sub_refl (substrate r))) => sra.
move: (isum_q5 wor' axg (@sub_refl (substrate r'))) => srb.
rewrite 2! isum_p0; apply: (ordinal_o_isu1 woa wob).
move: (proj1 woa) (proj1 wob) => oa ob.
set  A := disjointU (restr f (substrate r)).
set  B := disjointU (restr fg (substrate r')).
pose h := (fun p => (J (P p) (Vf g (Q p)))).
move: isog => [_ _ [bg sg th] gm]; move: (proj1 (proj1 bg)) =>  fctg.
have axh: lf_axiom h A B.
  rewrite /h => x /isum_q6 [qa qb qc]; apply/isum_q6; aw.
  have ha:  inc (Vf g (Q x)) (substrate r') by Wtac.
  split; fprops; rewrite /fg LgV//.
  rewrite (inverse_V2 bg) => //; ue.
have bb:  bijection (Lf h A B).
  apply: lf_bijective => //.
    move => u v /isum_q6 [qa qb qc] /isum_q6 [qa' qb' qc'].
    move/pr12_def => [sp sa]; apply: pair_exten => //.
    apply:(proj2 (proj1 bg)); ue.
  move => y /isum_q6 [qa qb qc].
  have ytg: inc (Q y) (target g) by ue.
  move: (proj2 (proj2 bg) _ ytg); rewrite sg; move =>[x xsf xv].
  exists (J (P y) x); last by rewrite /h;  aw; rewrite - xv qc.
  apply/isum_q6; saw; fprops.
  move: qb; rewrite /fg LgV// xv inverse_V2 => //; ue.
exists (Lf h  A B).
split => //; first by rewrite sra srb; saw.
hnf; aw => x y xA yA.
move:(axh _ xA) (axh _ yA) => xB yB.
set H := (isum_q7  wor axf (@sub_refl (substrate r))).
set H' := (isum_q7  wor' axg (@sub_refl (substrate r'))).
have qxs: inc (Q x) (source g) by move/isum_q6: xA=> /proj31; ue.
have qys: inc (Q y) (source g) by move/isum_q6: yA=> /proj31; ue.
have ij: Vf g (Q x) = Vf g (Q y) -> Q x =  Q y.
  by apply (proj2 (proj1 bg)).
split.
  move/H => /proj33 etc; apply/H'; rewrite !LfV//; split => //.
  rewrite /h; aw; case: etc.
    move => [sa sb]; left; split; first by apply/(gm _ _ qxs qys).
    by move/ij.
  by move =>[sa sb]; right; rewrite sa.
move/H' => /proj33 etc; apply/H; split => //.
move: etc; rewrite /h !LfV//;aw; case.
  move => [/(gm _ _ qxs qys) sa sb];left.
  by split => // ss; case: sb; rewrite ss.
move =>[/ij qa qb]; right; split => //.
Qed.

Definition nat_ord_seq f :=
  [/\ fgraph f, domain f = Nat & allf f ordinalp].

Definition n_partial_sum f E :=
  ipartial_sum f Nat_order E.
Definition n_sum f := osum Nat_order f.
Definition n_sum_to_n f n := n_partial_sum f n.
Definition n_sum_from_n f n := n_partial_sum f (Nat -s n).

Lemma nsum_p0 f:  nat_ord_seq f ->
  [/\ fgraph f, domain f = substrate Nat_order & allf f ordinalp].
Proof.
move:Nat_order_wor => [wor sr] [ha hb hc].
split => //; ue.
Qed.

    
Lemma OS_nsum f E: nat_ord_seq f -> sub E Nat -> 
  ordinalp (n_partial_sum f E).
Proof.
move:Nat_order_wor => [wor sr] /nsum_p0 fp En.
have sE: sub E (substrate Nat_order) by ue. 
exact (isum_p1  wor fp sE).
Qed.

Lemma nsum_p1 f: nat_ord_seq f ->
  n_sum f = n_partial_sum f  Nat.
Proof.
move:Nat_order_wor => [[or _] sr]  [ha hb hc];
rewrite /n_sum /n_partial_sum /ipartial_sum - {1} sr (iorder_substrate or).
by rewrite  - hb restr_to_domain.
Qed.


Lemma OS_nsuma f: nat_ord_seq f -> 
  ordinalp (n_sum f).
Proof.
by move =>h; rewrite (nsum_p1 h); apply: OS_nsum.
Qed.              


Lemma OS_nsumb  f n: nat_ord_seq f -> natp n ->
  ordinalp (n_sum_to_n f n).
Proof.
by move => ha nN;apply: OS_nsum => //; apply: NS_inc_nat.
Qed.

Lemma OS_nsumc  f n: nat_ord_seq f -> natp n ->
   ordinalp (n_sum_from_n f n). 
Proof.
by move => ha nN;apply: OS_nsum => //; apply:sub_setC.
Qed.
  
Lemma nsum_p2 f n: nat_ord_seq f -> natp n ->
  n_sum f = n_sum_to_n f n +o n_sum_from_n f n.  
Proof.
move:Nat_order_wor => [wor sr] fp nN; rewrite (nsum_p1 fp).
move /nsum_p0: fp => fp.
have ra : sub n (substrate Nat_order)  by rewrite sr;apply: NS_inc_nat.
have rb: sub (Nat -s n) (substrate Nat_order)  by rewrite sr; apply: sub_setC.
have rc i j: inc i n -> inc j (Nat -s n) -> glt Nat_order i j.
  move => /(NltP nN) iN /setC_P [jN /(NltP nN) h ].
  have: i <c j by case: (NleT_el nN jN) => // lnj ; apply:(clt_leT iN lnj).
  move => [lij nij]; split => //; apply /Nat_order_leP; split => //.
  apply: (NS_le_nat lij jN). 
symmetry; move:(isum_p4 wor fp ra rb rc).
by rewrite  setU2_C;  move/setCU_K: ra; rewrite sr => ->. 
Qed.

Lemma nsum_p3 f n: nat_ord_seq f -> natp n ->
  n_sum_to_n f (csucc n) = n_sum_to_n f n +o Vg f n.  
Proof.
move => /nsum_p0 fp nN.
move:Nat_order_wor => [wor sr].
have ns: inc n (substrate Nat_order) by ue.
have ra: sub n (substrate Nat_order)  by rewrite sr; apply: NS_inc_nat.
have rb:  sub (singleton n) (substrate Nat_order).
  by  rewrite sr; apply: set1_sub.
have rc i j: inc i n -> inc j (singleton n) -> glt Nat_order i j.
  move =>/(NltP nN) [sa sb] /set1_P ->; split => //.
  apply /Nat_order_leP; split => //; apply: (NS_le_nat sa nN). 
move: (isum_p4 wor fp ra rb rc).
by rewrite (isum_p3 wor fp ns) (succ_of_nat nN).
Qed.

Lemma nsum_p4 f n: nat_ord_seq f -> natp n ->
  n_sum_from_n f n = Vg f n +o n_sum_from_n f (csucc n).
Proof.
move => /nsum_p0 fp nN.
move:Nat_order_wor => [wor sr].
have ns: inc n (substrate Nat_order) by ue.
have ra:  sub (singleton n) (substrate Nat_order)
 by rewrite sr; apply: set1_sub.
have rb: sub (Nat -s csucc n) (substrate Nat_order)
   by rewrite sr; apply: sub_setC.
have rc i j:  inc i (singleton n) -> inc j (Nat -s csucc n) ->
   glt Nat_order i j.
  move => /set1_P -> /setC_P [jN /(NleP nN)]; case: (NleT_el jN nN) => //.
   move => [la sa ] -. split => //.
  apply /Nat_order_leP; split => //; apply: (NS_le_nat sa nN). 
have rd: (singleton n \cup (Nat -s csucc n)) =  (Nat -s n).
  rewrite (succ_of_nat nN) - setCC_l setU2_C setC1_K //;apply/setC_P.
  by split => //; apply: Nat_decent.
by move: (isum_p4 wor fp ra rb rc); rewrite rd (isum_p3 wor fp ns). 
Qed.

Definition f_perm_t f t := 
   Lg Nat (fun i => Vg f (Vf t i)).
Definition  n_all_sums f := 
  fun_image (permutations Nat) (fun t => n_sum (f_perm_t f t)).


Lemma f_perm_t_ax f t: nat_ord_seq f -> inc t (permutations Nat) ->
  nat_ord_seq (f_perm_t f t).
Proof.
move => [ha hb hc] /permutationsP [/proj1/proj1 bt sf tt].
rewrite /f_perm_t; split; aw; fprops; hnf; aw => i iN; rewrite LgV//.
apply:hc; rewrite hb; Wtac.
Qed.
  

Lemma all_sum1_p1 f: nat_ord_seq f ->  ordinal_set (n_all_sums f).
Proof.
move => ax y /funI_P [t tp ->].
by move: (f_perm_t_ax ax tp) => ay; apply: OS_nsuma.
Qed.

Lemma all_sums_p2 f: nat_ord_seq f -> (allf f (fun z => z = \0o)) ->
  (n_all_sums f) = singleton \0o.
Proof.
move => ha hb; apply: set1_pr1.
  apply: funI_setne; exists (identity Nat); apply:permutation_id.  
move => y /funI_P [t tp ->].
move: (f_perm_t_ax  ha tp); set g :=  (f_perm_t f t) => axg.
move:Nat_order_wor => [wor sr].
have ses: sub emptyset (substrate Nat_order) by move =>  x /in_set0. 
have allz i:inc i (substrate Nat_order -s emptyset) -> Vg g i = \0o.
   move/permutationsP: tp => [[[ft injt][_ stjt]] st tt].
   rewrite sr - st => /setC_P []; rewrite st /g  /f_perm_t => iN _; rewrite LgV//.
   move: iN; rewrite - st => /(Vf_target ft); rewrite tt - (proj32 ha).
   apply/hb.
move: (isum_p9 wor ses (nsum_p0 axg) allz); rewrite (isum_p2 _  wor).
by rewrite sr -/(n_partial_sum _ _) - (nsum_p1 axg).
Qed.

Lemma all_sums_p3 f: nat_ord_seq f -> ~ (allf f (fun z => z = \0o)) ->
  \0o <o n_sum f.
Proof.
move => ax;case :(all_exists_dichot1(fun z => Vg f z = \0o) (domain f)) => //.
move => [n nN bnz] _.
apply: ord_ne0_pos; first by apply: OS_nsuma.
rewrite  (proj32 ax) in nN; rewrite (nsum_p2 ax nN).
have rd: ordinalp (Vg f n) by apply: (proj33 ax); rewrite (proj32 ax).
move/(osum2_zero (OS_nsumb ax nN)(OS_nsumc ax nN)); move => /proj2.
rewrite (nsum_p4 ax nN).
by move/(osum2_zero rd (OS_nsumc ax (NS_succ nN)))  => /proj1.
Qed.

Definition nsupport f := Zo Nat (fun i => Vg f i  <> \0o).

Lemma nsum_p5 f n: nat_ord_seq f -> natp n -> n_sum_from_n f n = \0o ->
  (forall m, natp m -> n <=c m -> Vg f m = \0o)  /\
  (forall m, natp m -> n <=c m -> n_sum_from_n f m = \0o).
Proof.
move => ax nN rs.
have aux m: natp m -> n_sum_from_n f m = \0o ->
   Vg f m = \0o/\ n_sum_from_n f (csucc m) = \0o.
  move => mN; rewrite (nsum_p4 ax mN).
  have rd: ordinalp (Vg f m) by apply: (proj33 ax); rewrite (proj32 ax).
  by move/(osum2_zero rd  (OS_nsumc ax (NS_succ mN))).
have ra : (forall m : Set, natp m -> n <=c m -> n_sum_from_n f m = \0o).
  apply: Nat_induction; first by move/cle0 => <-.
  move => m mN Hr; case/(cle_eqVlt); first by move <-.
  by move/(cltSleP mN) => /Hr /(aux _ mN) /proj2.
split => //.
move => m mN ll; exact: (proj1 (aux _ mN (ra _ mN ll))). 
Qed.

Lemma nsum_p6 f n: nat_ord_seq f -> natp n -> n_sum_from_n f n = \0o ->
  finite_set (nsupport f).
Proof.
move => ax nN rz; move: (proj1 (nsum_p5 ax nN rz)) => ms.
have h :  sub (nsupport f) n.
  move => t /Zo_P [tN fnz].
  case: (NleT_el nN tN); first  by move => h; case: fnz; apply: ms.
  by move/(NltP nN).  
exact: (sub_finite_set h (finite_set_nat nN)).
Qed.

Lemma finite_subset_Nat_bis A: sub A Nat -> finite_set A ->
  exists2 m, natp m & forall n, inc n A -> n <c m. 
Proof.
move => sN fs.
case: (emptyset_dichot A) => se.
  by rewrite se; exists \0c; [ fprops | move => m  /in_set0].
move: (finite_subset_Nat sN fs se) =>[n /sN nN nb]; exists (csucc n).
   by apply: NS_succ.
by move => m /nb /(cltSleP nN).
Qed.
  

  
Lemma nsum_p7 f : nat_ord_seq f -> finite_set (nsupport f) ->
  exists2 n,  natp n & n_sum_from_n f n = \0o.
Proof.
move => ax fs.
have [m mN mp]: exists2 m, natp m & forall n, inc n (nsupport f) -> n <c m. 
  have sN: sub (nsupport f) Nat by apply/Zo_S.
  exact:(finite_subset_Nat_bis sN fs).
exists m => //.
move:Nat_order_wor => [wor sr].
have ra: sub m (substrate Nat_order) by rewrite sr; apply: NS_inc_nat.
have rb i: inc i (substrate Nat_order -s m) -> Vg f i = \0o.
  rewrite sr => /setC_P [iN im]; ex_middle  bad.
  have:  inc i (nsupport f) by apply: Zo_i.
  by move/mp  => /(NltP mN).
move: (isum_p9  wor ra (nsum_p0 ax) rb).
rewrite sr - [ipartial_sum f Nat_order Nat] (nsum_p1 ax) (nsum_p2 ax mN).
rewrite -/(n_partial_sum _  _ ) -/(n_sum_to_n _ _ ).
rewrite - {2} (osum0r (OS_nsumb ax mN)).
by move/(osum2_simpl (OS_nsumc ax mN) OS0 (OS_nsumb ax mN)).
Qed.


Lemma nsum_ne f : nat_ord_seq f -> ~ finite_set (nsupport f) ->
   \0o <o n_sum f. 
Proof.
move => axf si.
apply:(all_sums_p3 axf) => allz; case: si.
suff: (nsupport f) = emptyset by   move ->; apply: emptyset_finite.
apply/set0_P => x /Zo_P [xN xv].
have xdf: inc x (domain f) by rewrite (proj32 axf).
by move: (allz x xdf).
Qed.

Lemma all_sume_p4b f t: nat_ord_seq f -> inc t (permutations Nat) ->
  ( finite_set (nsupport f) <->  finite_set (nsupport (f_perm_t f t))).
Proof.
move:f t.
suff aux  f t:  nat_ord_seq f -> inc t (permutations Nat) ->
  finite_set (nsupport f) ->  finite_set (nsupport (f_perm_t f t)).
  move => f t ha hb; split; first by apply: aux.
  move => ff.
  move: (permutation_Si hb) => hb1.
  have ha1: (nat_ord_seq (f_perm_t f t)) by apply: f_perm_t_ax.
  move: (aux _ _ ha1 hb1 ff); congr finite_set; congr nsupport.
  move:  ha =>[fgf df _]; rewrite /f_perm_t; apply: fgraph_exten; fprops; aw.
    done.
  move /permutationsP: hb =>[bt st tt].
  hnf => x xn /=.
  have xtt: inc x (target t) by ue.
  move: (inverse_Vis bt xtt); rewrite st => txs.
  by rewrite !LgV// (inverse_V bt xtt).
move => [fgf df fp] /permutationsP [bt st tt].
have fy := (proj1 (proj1 bt)).
rewrite /nsupport /f_perm_t; set E := Zo  _ _ ; set F := Zo _ _ => fse.
have: sub  F (fun_image E (Vf (inverse_fun t))).
  move => x /Zo_P [xN]; rewrite LgV// => h; apply/funI_P.
  move: (proj1 (proj1 bt)) => ft.
  have xst:  inc x (source t) by ue.
  have txe: inc (Vf t x) E by apply: Zo_i h; Wtac.
  by ex_tac; rewrite inverse_V2.
by move/sub_finite_set; apply; apply:  finite_fun_image.
Qed.
  

  
Lemma nsum_p8 f : nat_ord_seq f -> ~ finite_set (nsupport f) ->
  exists2 n, natp n & n_sum_from_n f n = least_rem (n_sum f).
Proof.
move => axf si.
move:(nsum_ne axf si) => sp.
move: (least_rem_p1 sp) (least_rem_p3 sp); set b := least_rem _.
move => [bp [a oa sv]] inb.
move:(bp) => [[_ ob _] /nesym bnz].
move:Nat_order_wor => [wor sr].
move /nsum_p0: (axf) => fp.
have sv1: ipartial_sum f Nat_order (substrate Nat_order) = a +o b.
   by rewrite sr - /(n_partial_sum _ _)- (nsum_p1 axf) sv.
move:(isum_p6 wor fp oa ob bnz sv1) => [n [u [v ]]]; rewrite sr.
move => [nN ou ov vp [eqa eqb eqc]]; exists (csucc n); first by apply: NS_succ.
move: eqc. rewrite -/(n_partial_sum _ _).
have ->: (Zo Nat [eta glt Nat_order n]) = Nat -s (csucc n).
  set_extens t.
    move =>/ Zo_P [tN [/Nat_order_leP [ha hb hx]] hd].
    by apply/setC_P; split => //; move/(NleP nN) => he; case: hd; apply: cleA. 
  move => /setC_P [tN /(NleP nN)  ltn].
  case:(NleT_el tN nN) => // - [lnt nnt]; apply:(Zo_i tN).
  by split => //; apply/Nat_order_leP.
rewrite -/(n_sum_from_n _ _).
set c := n_sum_from_n f (csucc n) => eq4.
have oc: ordinalp c by apply: (OS_nsumc axf (NS_succ nN)).
case: (indecomp_pr ov oc inb (esym eq4)) => //.
rewrite eq4 => /esym eq5; move: (osum2_a_ab ov oc eq5) => cz.
case: si; apply:(nsum_p6 axf (NS_succ nN) cz).
Qed.

Lemma nsum_p9 f : nat_ord_seq f -> ~ finite_set (nsupport f) ->
  exists2 n, natp n &
   forall m, natp m -> n <=c m ->  n_sum_from_n f m = least_rem (n_sum f).
Proof.
move => axf si.
move:(nsum_ne axf si) => sp.
move: (nsum_p8 axf si) => [n nN hc]; exists n => //.
apply: Nat_induction; first by move /cle0 => <-.
move => m mN  Hrec /cle_eqVlt; case; first by move <-.
move/(cltSleP mN) => /Hrec; rewrite (nsum_p4 axf mN).
move: (least_rem_p3 sp); set b := least_rem _ => inb => eq1.
have aox: ordinalp (Vg f m) by apply : (proj33 axf); rewrite (proj32 axf).
have or := (OS_nsumc axf (NS_succ mN)).
move: (@indecomp_pr  b (Vg f m) (n_sum_from_n f (csucc m)) aox or inb eq1).
case => //.
rewrite - eq1 => /esym eq5; move: (osum2_a_ab aox or eq5) => cz.
case: si; apply:(nsum_p6 axf (NS_succ mN) cz).
Qed.

Definition n_sum_small_idx1 f := 
 (Zo Nat (fun i => (least_rem (n_sum f)) <=o Vg f i)).


Definition n_sum_small_idx f := 
  Yo (finite_set (nsupport f)) (nsupport f) (n_sum_small_idx1 f).

Definition n_sum_rem f :=
   Yo (finite_set (nsupport f)) \0o (least_rem (n_sum f)).

           
Lemma nsum_p10a f (rho := least_rem (n_sum f)):
  nat_ord_seq f -> ~ finite_set (nsupport f) ->
  exists2 n, natp n &
   forall m, natp m -> n <=c m ->  n_sum_from_n f m = rho /\ Vg f m <o rho.
Proof.
move => axf si.
move: (nsum_p9 axf si); rewrite -/rho; move => [n nN np].
have rp := (proj1 (least_rem_p1 (nsum_ne  axf si))).
exists n => //m mN le1; move:(np m mN le1) => eq1; split => //.
move: (nsum_p4 axf mN).
rewrite eq1 (np _ (NS_succ mN) (cleT le1 (cleS mN))) => sc.
have ox: ordinalp (Vg f m) by apply: (proj33 axf); rewrite (proj32 axf).
by move: (osum_Meqlt rp  ox); rewrite - sc (osum0r ox).
Qed.

Lemma nsum_p10b f:  nat_ord_seq f -> ~ finite_set (nsupport f) ->
  finite_set(n_sum_small_idx1 f).
Proof.
move => ha hb; move: (nsum_p10a ha hb) =>[n nN np].
rewrite/n_sum_small_idx1; set E := Zo _ _.
suff: sub E n by  move => h; move : (sub_finite_set h (finite_set_nat nN)).
move => i /Zo_P [iN le1]; case: (NleT_el nN iN); last by move/(NltP nN).
move => le2; case: (oleNgt  le1 (proj2 (np i iN le2))).
Qed.

Lemma nsum_p10c f:  nat_ord_seq f ->  finite_set (n_sum_small_idx f).
Proof.
by move =>h; rewrite/n_sum_small_idx; Ytac hh => //; apply:nsum_p10b.
Qed.


Lemma nsum_p10e f (rho := (least_rem (n_sum f))):
   nat_ord_seq f -> ~ finite_set (nsupport f) ->
  n_sum f = (n_partial_sum f (n_sum_small_idx1 f)) +o rho.
Proof.
move => ha hb.
move: (nsum_p10a ha hb) =>[n nN np].
move: (proj1 (np n nN (cleR (CS_nat nN)))); rewrite -/rho  => eq1.
move: (least_rem_p3 (nsum_ne  ha hb)); rewrite -/rho => ri.
rewrite (nsum_p2 ha nN) eq1.
set E :=  (n_sum_small_idx1 f). 
have /setI2id_Pl sEn: sub E n.
  move => i /Zo_P [iN le1]; case: (NleT_el nN iN); last by move/(NltP nN).
  by move => le2; case: (oleNgt  le1 (proj2 (np i iN le2))).
rewrite - sEn.
rewrite /n_sum_to_n /n_partial_sum.
pose A m := n -s (n -c m).
have Ap m : A m = Zo n (fun i =>  n -c m <=c i).
  have uN :=(NS_diff m nN).
  set_extens t. 
    move => /Zo_P [tn /(NltP uN) nn].
    have tN: natp t by exact: (NS_inc_nat nN tn ).
    by case: (NleT_el uN tN) => // ll; apply: Zo_i.
  by move =>/Zo_P [tn /cleNgt le]; apply: (Zo_i tn) => /(NltP uN).
have ->: n = A n by rewrite /A cdiff_nn setC_0.
move: (cleR (CS_nat nN)).
move:Nat_order_wor => [wor sr].
move: {-3} (n) (nN); apply: Nat_induction.
   move => _; rewrite /A (cdiff_n0 nN) setC_v.
   have -> //: E  \cap emptyset= emptyset. 
   by apply/set0_P => t /setI2_P [_ /in_set0].
move => m  mN Hrec ll.
set v := n -c (csucc m).
move:  (csucc_diff nN mN ll) => sv.
have vN: natp v . by apply: NS_diff.
have lvb: v <c n by  apply: (cdiff_ltb nN ll (@succ_nz _)).
have ->: A (csucc m) = singleton v \cup (A m).
  rewrite ! Ap; set_extens t.
    move => /Zo_P [rn]; case/cle_eqVlt.
     rewrite /v; move ->; apply: setU2_1; fprops.
    by move/(cleSltP vN); rewrite sv => xx; apply: setU2_2; apply: Zo_i. 
  case/setU2_P. 
    move/set1_P ->; apply: Zo_i; first by  apply/(NltP nN). 
    apply: (cleR (CS_nat vN)).
  move => /Zo_P [tn hyp]; apply:(Zo_i tn).
  suff: n -c csucc m <c t by case.
  by apply /(cleSltP vN); rewrite - sv.
move: (nsum_p0 ha) => axf.
have ra: sub (singleton v) (substrate Nat_order) by  move => u /set1_P ->; ue.
have rb: sub (A m) (substrate Nat_order).
   by rewrite sr; move =>u  /setC_P [/ (NS_inc_nat nN)].
have rc i j: inc i (singleton v) -> inc j (A m) -> glt Nat_order i j.
  rewrite Ap; move => /set1_P -> /Zo_P [jn lt].
  move: (NS_inc_nat nN jn) => jN.
  have [qa qb] : v <c j. by apply/(cleSltP vN); rewrite - sv.
  split => //;  apply/Nat_order_leP; split => //.
have rd: inc v (substrate Nat_order) by ue.
rewrite - (isum_p4 wor axf ra rb rc).
have ov: ordinalp (Vg f v) by apply (proj33 ha); rewrite (proj32 ha).
have orho: ordinalp rho by move: (proj32_1 (proj1 ri)).
have os1: ordinalp (ipartial_sum f Nat_order (A m))  by apply: isum_p1.
rewrite (isum_p3 wor axf rd).
case: (inc_or_not v E) => ivE.
  have h: sub (singleton v) E  by move => y /set1_P ->.
  move/ (setU2id_Pl): h  => <-; rewrite - set_UI2r.
  have rb1: sub (E \cap A m) (substrate Nat_order).
    by move => t/setI2_P [_]; apply: rb.
  have rc1 i j: inc i (singleton v)-> inc j (E \cap (A m))-> glt Nat_order i j.
    by move => ii /setI2_P [_ jj]; apply: rc.
  have os2: ordinalp (ipartial_sum f Nat_order (E \cap A m)) by apply: isum_p1.
  rewrite - (isum_p4 wor axf ra rb1 rc1) (isum_p3 wor axf rd).
  rewrite - (osumA ov os2 orho) - (osumA ov os1 orho).
  by rewrite (Hrec (cleT (cleS mN) ll)).
have -> :  (E \cap (singleton v \cup A m)) = E \cap (A m).
  rewrite set_IU2r; set_extens t.
     case/setU2_P => // /setI2_P [iE /set1_P ee]; case: ivE; ue.
  by move => qa; apply: setU2_2.
case: (oleT_el orho ov) => vs; first by case: ivE; apply : Zo_i.
rewrite - (Hrec (cleT (cleS mN) ll)).
apply: (indecomp_sier os1 ri vs).
Qed.    

Lemma nsum_p10f f:nat_ord_seq f -> finite_set (nsupport f) ->
  n_sum f = (n_partial_sum f (nsupport f)) +o \0o.
Proof.
move => axf fs.
have sEN: sub (nsupport f) Nat by apply: Zo_S.
rewrite (osum0r (OS_nsum axf sEN)) (nsum_p1 axf).
move:Nat_order_wor => [wor sr].
rewrite - sr in sEN.
move:(nsum_p0 axf) => foo.
have ok i: inc i (substrate Nat_order -s (nsupport f)) -> Vg f i = \0o.
  by rewrite sr => /setC_P [iN /Zo_P ie]; ex_middle bad; case ie.
rewrite /n_partial_sum - sr; exact: (isum_p9 wor sEN foo ok).
Qed.


Lemma nsum_p10g f: nat_ord_seq f -> 
  n_sum f = (n_partial_sum f (n_sum_small_idx f)) +o (n_sum_rem f).
Proof.
move => ha.
rewrite /n_sum_small_idx/n_sum_rem; Ytac h; Ytac0.
  by apply: nsum_p10f.
by apply: nsum_p10e. 
Qed.

Lemma nsum_p11a f:  nat_ord_seq f ->
  (forall i, natp i -> Vg f i <=o (Vg f (csucc i))) ->
  n_sum_small_idx f = emptyset.
Proof.
move => ha hb.
have mn i j: natp j -> i <=c j -> Vg f i <=o Vg f j.
  move: j; apply: Nat_induction.
    move/cle0 ->; exact (oleR (proj31 (hb _ NS0))).
  move => n nN Hrec; move: (hb _ nN) => lea.
  case /(cle_eqVlt); first by move ->; exact: (oleR (proj32 lea)).
  move/(cltSleP nN) => /Hrec leb; exact (oleT leb lea).
case: (all_exists_dichot1 (fun i => Vg f i = \0o) Nat).
  move => H.
  have se: nsupport f = emptyset.
    by apply/set0_P => i /Zo_P [ iN]; case; apply: H.
  by rewrite /n_sum_small_idx se (Y_true emptyset_finite).
move => [j jN jv].
move:(ha) =>[_ hc hd].
have jp: \0o <o Vg f j by  apply: (ord_ne0_pos _ jv); apply: hd; ue.
case: (p_or_not_p (finite_set (nsupport f))) => fs.
  have ss: sub (nsupport f) Nat by apply: Zo_S.
  move: (finite_subset_Nat_bis ss fs) =>[n nN] np.
  pose i := cmax j n.
  move: (Nmax_p1 jN nN) =>[qa qb qc].
  move: (nesym (proj2 (olt_leT jp (mn _ _ qa qb)))) => qd.
  have:inc (cmax j n) (nsupport f) by apply: Zo_i.
  by move/np => /cltNge.
rewrite /n_sum_small_idx; Ytac0.
move: (nsum_p10a ha fs) =>[n nN np].
apply/set0_P => i /Zo_P [iN]; apply: oltNge.
case: (NleT_el nN iN) => hi; first exact: (proj2 (np i iN hi)).
move: (proj2 (np n nN (cleR (CS_nat nN)))) => sa.
exact: (ole_ltT (mn _ _ nN (proj1 hi)) sa).
Qed.


Lemma nsum_p11b f:  nat_ord_seq f ->
  n_sum f = \osup (fun_image Nat (n_sum_to_n f)).
Proof.
move => ha.
move:Nat_order_wor => [wor sr].
move: (nsum_p0 ha) => ax.
case:(isum_p7b wor ax).
  move => [n []]; rewrite sr => nN h.
  move:(h _ (NS_succ nN)) => /Nat_order_leP [ _ _ /cleNgt]; case; exact: cltS.
rewrite (nsum_p1 ha) sr /n_partial_sum => ->.
rewrite /n_sum_to_n /n_partial_sum.
apply: f_equal;apply: funI_exten => i iN; apply:f_equal.
set_extens t.
  by move => /Zo_P[tN [/Nat_order_leP [_ _ qa] qb] ]; apply/(NltP iN).
move/(NltP iN) =>[qa qb]; move: (NS_le_nat qa iN) => tN.
by apply: (Zo_i tN); split => //;apply/Nat_order_leP.
Qed. 


Lemma nsum_p11c f a:  nat_ord_seq f ->
  (forall n, natp n ->  (n_sum_to_n f n) <=o a) ->
  n_sum f <=o a.
Proof.
move => ha hb.
move: (proj32 (hb _ NS0)) => oa.
rewrite (nsum_p11b ha). 
by apply: (ord_ub_sup oa) => i /funI_P [j jN ->]; apply: hb.
Qed.

Lemma nsum_p11d f r:  nat_ord_seq f -> indecomposable r ->
  (forall i, natp i -> Vg f i <o  r) ->
  n_sum f <=o r.
Proof.
move => axf ir ss.
have sp: forall n, natp n -> n_sum_to_n f n <o r.
  apply: Nat_induction.
    move:Nat_order_wor => [wor sr].
    by rewrite /n_sum_to_n /n_partial_sum (isum_p2 _ wor); case: ir.
  move => n nN hr; rewrite (nsum_p3 axf nN).
  apply: (indecomp_prop2 hr (ss _ nN) ir).
by apply/ (nsum_p11c axf) => n /sp/proj1.
Qed.


Lemma nsum_p11e f: nat_ord_seq f -> 
  n_sum_rem f <> \1o. 
Proof.
move => ax.
rewrite /n_sum_rem; Ytac fs; first by fprops.
move => v1.
move: (nsum_p10a ax fs) =>[n nN np].
have h i: natp i -> n <=c i -> Vg f i = \0o.
  by move => qa qb; move: (proj2(np _ qa qb)); rewrite v1 => /olt1.
have ss: sub (nsupport f) n.
  move => t/Zo_P [tN fnZ]; apply/(NltP nN).
  by case: (NleT_el nN tN) => // /(h _ tN).
by move:(sub_finite_set ss (finite_set_nat nN)). 
Qed.


Lemma nsum_p11f f q:
  nat_ord_seq f -> ~ finite_set (nsupport f) -> ordinalp q ->
  n_sum f = oopow q -> n_sum_small_idx f = emptyset.
Proof.
move => axf fs oq sv.
move: (indecomp_prop4 oq) => ir.
move: (least_rem_p5 ir) => eqa.
move: (nsum_p10a axf fs) =>[n nN np].
move: (proj1 (np n nN (cleR (CS_nat nN)))) => eq1.
rewrite /n_sum_small_idx; Ytac0; apply/set0_P => i /Zo_P [iN].
move: (osum_M0le (OS_nsumb axf iN)(OS_nsumc axf iN)).
rewrite - (nsum_p2 axf iN)sv eqa (nsum_p4 axf iN) => ea eb.
move: (NS_succ iN) => siN; case: fs.
have aux := (OS_nsumc axf siN).
move : (osum_Mle0  (proj32 eb) aux) => ec.
exact: (nsum_p6 axf siN (osum2_a_ab (proj31 ec) aux (oleA (oleT  ea eb) ec))).
Qed.


Lemma nsum_p11g f: nat_ord_seq f -> ~ finite_set (nsupport f) ->
  omega0 <=o n_sum f.
Proof.
move => axf fs.
move: (nsum_p10a axf fs) =>[n nN np].
move: (proj1 (np n nN (cleR (CS_nat nN)))) => eq.
move: (osum_M0le (OS_nsumb axf nN)(OS_nsumc axf nN)).
rewrite - (nsum_p2 axf nN) eq;  apply: oleT.
move: (nsum_p11e axf); rewrite /n_sum_rem; Ytac0.
move: (indecomp_prop3 (least_rem_p3 (nsum_ne axf fs))) => [p op ->].
case: (ozero_dichot op); first by move ->; rewrite oopow0.
by move=> /oge1P /opow_Mo_le; rewrite oopow1.
Qed.

Lemma nsum_p11h f: nat_ord_seq f ->
  \osup (fun_image (range f) odegree) = \0o ->
  ~ finite_set (nsupport f) ->
  n_sum f = omega0.
Proof.
move => ax sz fs.
move: (ax) => [fgf df fo].
have ha i: natp i -> odegree (Vg f i) = \0o.
  move => iN. 
  have vf: inc (odegree (Vg f i)) (fun_image (range f) odegree).
    by apply: funI_i; apply/(range_gP fgf); rewrite df; exists i.
  case: (emptyset_dichot (odegree (Vg f i))) => //.
  by move => [t ta]; move: (setU_i ta vf); rewrite sz => /in_set0.
have hb i: natp i -> (Vg f i) <o omega0.
  move => iN; move: (ha i iN) => d0.
  have oi: ordinalp (Vg f i) by apply: fo; ue.
  case: (ozero_dichot oi); first by move ->; apply: olt_0omega.
  by move/ the_cnf_p4 => /proj2; rewrite d0 osucc_zero oopow1.
apply: oleA.
 exact: (nsum_p11d ax indecomp_omega hb).
by apply: nsum_p11g.
Qed.

Lemma nsum_p11i f q: nat_ord_seq f -> ordinalp q ->
  \osup (fun_image (range f) odegree) = q ->
  n_sum f  <=o oopow (osucc q).
Proof.
move => axf oq sf; move: (OS_succ oq) => osq.
move: (indecomp_prop4 osq) => iq.
apply: (nsum_p11d axf iq)  => i iN.
move: (axf) => [fgf df fo].
have ov: ordinalp (Vg f i) by apply: fo; ue.
case: (ozero_dichot ov); first by  move ->; apply: oopow_pos.
move/ the_cnf_p4 => /proj2 => h; apply:(olt_leT h).
apply/opow_Mo_le; apply/oleSSP; rewrite - sf; apply: ord_sup_ub.
  move => t /funI_P [v /(range_gP fgf) [j jN ->] ->].    
  by apply: OS_degree; apply: fo.
by apply: funI_i; apply/(range_gP fgf); rewrite df; exists i.
Qed.

  
Lemma nsum_p11j f q (r:= oopow q) : nat_ord_seq f -> \0o <o q ->   
  (forall i, natp i -> Vg f i <o  r) ->
  \osup (fun_image (range f) odegree) = q ->
  n_sum f = r.
Proof.
move => axf qp ha hb.
move: (axf) => [fgf df fo].
move: (proj32_1 qp) => oq.
move: (indecomp_prop4 oq) => ir.
pose S := nsupport f.
have hc i: natp i -> ~ inc i S -> odegree (Vg f i) = \0o.
  move => iN /Zo_P w; case:(equal_or_not (Vg f i) \0o).
    by move ->; rewrite odegree_zero.
  by move => h; case:w.
have hd: forall i, natp i -> odegree (Vg f i) <o q. 
  move => i iN; case: (inc_or_not i S) => eis; last by  rewrite (hc _ iN eis).
  have oi: ordinalp (Vg f i) by apply: fo; ue.
  move/Zo_hi: eis => fnz.
  move: (OS_degree oi) => od.
  move: (ole_ltT (proj1 (the_cnf_p4 (ord_ne0_pos oi fnz))) (ha _ iN)).
  by move /(opow_Mo_ltP od oq).
pose W z := fun_image z (fun i => odegree (Vg f i)).
have aux n: natp n ->q = \osup (W (Nat -s n)).
  move => nN.
  move: (@funU_setC Nat n (fun i => odegree (Vg f i))).
  rewrite /= -/(W _) -/(W _); move =>[rq rb].
  have rc: ordinal_set (W Nat).
    by move => t /funI_P [i /hd/proj31_1 iN ->].
  have rd: sub (W Nat -s W (Nat -s n)) (W Nat) by move => t /setC_P[].
  have re: finite_set (W Nat -s W (Nat -s n)). 
    by apply:rb; apply: finite_set_nat.
  have rf x: inc x (W Nat) -> x <o q.
    by move => /funI_P [i /hd hh -> ].   
  have rg: q = \osup (W Nat).
    rewrite - hb; apply: f_equal; set_extens t.
      move/funI_P =>[v /(range_gP fgf)[i idf ->] ->]; apply: funI_i; ue.
    move/funI_P =>[i iN ->]; apply: funI_i; apply/(range_gP fgf).
    rewrite df; ex_tac.
  by move: (osup_Un rc rd re rf rg) ; rewrite - rq.
case: (p_or_not_p (finite_set (nsupport f))) => fs.
  have fsu: sub (nsupport f) Nat by apply:Zo_S.
  move: (finite_subset_Nat_bis fsu fs)=> [n nN hn].
  move: (aux n nN) => qn.
  have hh: ordinal_set (W (Nat -s n)).
    move => t /funI_P[i /setC_P/proj1 iN ->]; apply:OS_degree.
    by apply:fo; ue.
  move: qp; rewrite qn. 
  move/(olt_sup hh) => [z /funI_P [i /setC_P[iN ini] ->] dv].
  case: ini; apply/(NltP nN).
  case: (inc_or_not i (nsupport f)); first by move /hn. 
  by move => ns; case: (nesym(proj2 dv)); move: (hc _ iN ns).
move: (nsum_p10a axf fs) =>[n nN np].
move: (indecomp_prop3 (least_rem_p3 (nsum_ne axf fs))) => [ p op pv].
case: (oleT_el oq op); last first.
 have hh: ordinal_set (W (Nat -s n)).
    move => t /funI_P[i /setC_P/proj1 iN ->]; apply:OS_degree.
    by apply:fo; ue.
  rewrite (aux _ nN);  move/(olt_sup hh) => [d /funI_P [i ii ->] ] la.
  move/Zo_P: ii => [iN /(NltP nN) lin].
  case: (NleT_el nN iN) => // lein.
  have ov: ordinalp (Vg f i) by apply: fo; ue.
  case:(ozero_dichot ov) => vp.
    by move: la; rewrite vp odegree_zero => /olt0.
  move: (ole_ltT (proj1 (the_cnf_p4 vp))  (proj2 (np _ iN lein))).
  rewrite  pv => /oltNge; case; exact: (proj1(opow_Mo_lt la)).
move => lpq.
move: (proj1 (np n nN (cleR (CS_nat nN)))); rewrite pv => eq1.
move: (nsum_p11d axf ir ha) => eq2.
move: (opow_Mo_le lpq) => eq3.
move: (osum_M0le (OS_nsumb axf nN)(OS_nsumc axf nN)).
rewrite - (nsum_p2 axf nN) eq1 => eq4.
exact:  (oleA eq2 (oleT eq3 eq4)). 
Qed.

                              
Lemma nsum_p11k f q (r:= oopow (osucc q)) : nat_ord_seq f -> \0o <o q ->   
   ~ (finite_set (Zo Nat (fun i => oopow q <=o Vg f i))) ->
  \osup (fun_image (range f) odegree) = q ->
  n_sum f = r.
Proof.
move => axf qp ha hb.
move: (axf) => [fgf df fo].
move: (proj32_1 qp) => oq.
have ooq := OS_oopow oq.
move: (indecomp_prop4 (OS_succ oq)) => ir.
apply: oleA; first by  apply: nsum_p11i.
move: ha; set A := Zo _ _ => nfA.
set s1 :=  ipartial_sum f Nat_order (substrate Nat_order).
move: (nsum_p0 axf) => ax.
move:Nat_order_wor => [wor sr].
have <-: s1 = n_sum f.
  by rewrite (nsum_p1 axf) /n_partial_sum /s1 sr.
set s2 :=  ipartial_sum f Nat_order A.
have saN: sub A Nat by apply: Zo_S.
have sas: sub A (substrate Nat_order) by rewrite sr.
have ra: s2 <=o s1 by apply:(isum_p10 wor sas (@sub_refl _) ax).
move: (induced_wor wor sas) (iorder_sr (proj1 wor) sas).
set r1 := induced_order _ _ => wor1 sr1.
set s3 :=  ipartial_sum (Lg A (fun _ => (oopow q)))  Nat_order A.
have rb: s3 <=o s2.
  set g := (Lg A (fun _ => (oopow q))).
  have pa: fgraph g by rewrite /g; fprops.
  have pb: fgraph (restr f A)by apply: restr_fgraph.
  have pc: domain g = substrate r1 by rewrite /g; aw.
  have pd:  domain (restr f A) = substrate r1 by  aw.
  have pe x: inc x (substrate r1) -> Vg g x <=o Vg (restr f A) x.
    by rewrite /g sr1 => tA; rewrite !LgV//; move/Zo_hi: tA.
  have AA : sub A A by [].
  move: (isum_p8 wor1 pa pb pc pd pe).
  by rewrite /s2 /s3 /ipartial_sum /r1 sr1 (iorder_trans _ AA) (double_restr ).
move:(oleT rb ra).
pose fA :=  (Lg A (fun _ : Set => oopow q)).
have ->: s3 = ipartial_sum  fA r1 (substrate r1).
  by rewrite /s3/ipartial_sum sr1 /r1 (iorder_trans _(@sub_refl A)).
have axa: [/\ fgraph fA, domain fA = substrate r1 & allf fA ordinalp].
  by rewrite /fA /allf; aw; split; fprops => x xA; rewrite LgV//.
have is1: ordinal_o omega0 \Is Nat_order.
  apply: orderIS;  rewrite - ord_omega_pr;apply: (ordinal_o_is wor).
move:(proj2 (sub_nat_isomorphism saN) nfA)=>[g isg].
rewrite (isum_p11 wor1 isg axa).
set fB := Lg _ _.
move: (oprod_pr1 ooq OS_omega is1). rewrite - (oopow_succ oq) -/r => ->.
rewrite /ipartial_sum (iorder_substrate (proj1 wor)).
congr (osum Nat_order _ <=o s1).
apply: Lg_exten => x xsr;rewrite /fB /fA !LgV//.
move: isg =>[_ _ [bg sg tg] _].
by rewrite - sr1 /r1 - sg; apply: (inverse_Vis bg); rewrite tg.
Qed.


Lemma nsum_eventually_const f c:
  nat_ord_seq f -> \0o <o c ->
  (exists2 n, natp n & forall i, natp i -> n <=c i -> Vg f i = c) ->
  n_sum_rem f  = c *o omega0.
Proof.
move => axf cp [n nN np].
case: (p_or_not_p (finite_set (nsupport f))) => fs.
  have sn: sub  (nsupport f) Nat by apply: Zo_S.
  move: (finite_subset_Nat_bis sn fs) => [m] mN mp; ex_middle bad.
  move: (Nmax_p1 nN mN).
  set k := cmax _ _; move => [kN  qb  /cleNgt qc].
  case: (inc_or_not k (nsupport f)); first by  move/mp. 
  case; apply:(Zo_i kN); rewrite (np _ kN qb); exact (nesym (proj2 cp)).
move: (nsum_p10a axf fs) => [m mN mp].
move: (Nmax_p1 nN mN).
set k := cmax _ _; move => [kN  le1 le2].
move: (proj1 (mp k kN le2)).
rewrite /n_sum_rem; Ytac0; move <-.
move:Nat_order_wor => [wor sr]; move: (proj1 wor) => or.
rewrite /n_sum_from_n/n_partial_sum.
set shift := Lf (fun i => k +c i) Nat (Nat -s k).
have sr1: sub  (Nat -s k) (substrate Nat_order).
  by rewrite sr; apply: sub_setC.
move: (iorder_osr or sr1).
set r' := (induced_order Nat_order (Nat -s k)).
move => [or2 sr2].
have axs: lf_axiom (csum2 k) Nat (Nat -s k).
  move => x xN; apply/setC_P; split; first by apply: NS_sum.
  by move => /(NltP kN) /cltNge; case;  apply: csum_M0le; fprops.
have bsh: bijection shift.
  apply: lf_bijective => //.
    by move => x y xN yhN; apply:csum_eq2l.
  move => y /setC_P [yN xl].
  case: (NleT_el kN yN); last by move/(NltP kN).
  move => xcp;  move: (cdiff_pr xcp); move: (NS_diff k yN) => av bv.
  exists (y -c k) => //.
have ois : order_isomorphism shift Nat_order r'.
  split => //; first  by split => //; rewrite/shift; aw. 
  hnf; rewrite /shift; aw => x y xN yN; rewrite !LfV//.
  move:(axs x xN) (axs y yN) => xs ys.
  split.
    move /Nat_order_leP =>[_ _ lexy]; apply/(iorder_gle0P _ xs ys).
    apply/Nat_order_leP; split => //; fprops.
    by apply: csum_Meqle.
  move/(iorder_gle0P _ xs ys)=> /Nat_order_leP/proj33 /(csum_le2l kN xN yN).
  by move => kk; apply /Nat_order_leP.
pose fna := Lg Nat (fun i => Vg f (i+c k)).
have fnag: fgraph fna by rewrite /fna; fprops.
have dfna: domain fna = substrate Nat_order by rewrite /fna sr; aw.
have fnax:  [/\ fgraph fna, domain fna = substrate Nat_order
     & allf fna ordinalp].  
  split => //; rewrite /fna/allf; aw => x xN; rewrite LgV//; apply:(proj33 axf).
  by rewrite (proj32 axf); apply: NS_sum.
move: (isum_p11 wor ois fnax). 
set w := Lg _ _.
have ->: w = restr f (substrate r').
  apply: Lg_exten; rewrite sr2 => x xs.
  have xts: inc x (target shift) by rewrite /shift; aw.
  move: (inverse_V bsh xts).
  move: (inverse_Vis bsh xts); rewrite {2}/shift; aw.
  set y :=  (Vf (inverse_fun shift) x) => yN.
  rewrite /shift LfV// => eqa.
  move/setC_P : xs => [xN _].
  by  rewrite /fna /f_perm_t LgV// csumC eqa.
have -> : ipartial_sum (restr f (substrate r')) r' (substrate r') = 
  ipartial_sum f Nat_order (Nat -s k).
  have tt: sub (Nat -s k) (Nat -s k) by [].
  by rewrite /ipartial_sum sr2 /r'  (double_restr _ tt) (iorder_trans _ tt).
move <-.
rewrite /ipartial_sum (iorder_substrate  or).
have ->: restr fna (substrate Nat_order)  = cst_graph (substrate Nat_order)c.
  apply: Lg_exten; rewrite sr => i iN.
  rewrite /fna LgV//; apply: (np _ (NS_sum iN kN)).
  exact: (cleT le1 (csum_Mle0 i (CS_nat kN))).
have is1: ordinal_o omega0 \Is Nat_order.
  apply: orderIS;  rewrite - ord_omega_pr;apply: (ordinal_o_is wor).
symmetry; exact: (oprod_pr1 (proj32_1 cp) OS_omega is1).
Qed.

  
  
Definition except_in_nsum f k := 
  finite_set (Zo Nat (fun n => Vg f k <=o Vg f n)).
Definition except_in_nsums f := Zo Nat (except_in_nsum f).


                            
Lemma except_in_nsum_finite f: nat_ord_seq f ->
  exists2 n, natp n & forall i, inc i (except_in_nsums f) -> i <=c n.
Proof.
move =>[pq pb pc].
have aux k: natp k ->  (except_in_nsum f) k -> exists2 n, natp n &
  forall m, natp m -> n <c m -> Vg f m <o Vg f k.
  rewrite /except_in_nsum; set E := Zo _ _ =>kN Ef.
  have qa: sub E Nat by apply: Zo_S.
  have ofk: ordinalp (Vg f k) by  apply: pc; ue.
  have qb: nonempty E by exists k; apply:(Zo_i kN); apply: oleR.
  move: (finite_subset_Nat qa Ef qb) => [n /Zo_P [qc qd] qe].
  exists n => // m mN lem.
  have oo: ordinalp (Vg f m) by apply: pc; ue.
  case: (oleT_el ofk oo) => // lt2.
  have /qe /cleNgt mE//: inc m E by apply: (Zo_i mN).
rewrite /except_in_nsums;set E := Zo _ _.
case: (emptyset_dichot E).
  move ->; exists \0c; [exact NS0 | by move => i /in_set0].
move => [t tE].
pose p x := exists2 k, inc k E & x = Vg f k.
have pt: p (Vg f t) by exists t.
have ot: ordinalp (Vg f t) by apply: pc; rewrite pb; move/Zo_S:tE.
move: (least_ordinal4 ot pt); set u := least_ordinal _ _.
move => [ou [k /Zo_P [kN kE] kv] etc].
move: (aux k kN kE) =>[n nN np].
exists n => // m mE; move: (mE) => /Zo_P [mN mp].
case: (NleT_el mN nN) => // lmn.
case: (oltNge (np m mN lmn)).
have pm: (p (Vg f m)) by  exists m.
have oo: ordinalp (Vg f m) by apply: pc; ue.
by move: (etc _ oo  pm);rewrite kv.
Qed.


Lemma except_in_nsum_finite2 f: nat_ord_seq f ->
   finite_set (except_in_nsums f).
Proof.
move => h; move: (except_in_nsum_finite h) =>[n nN etc].
have /sub_finite_set aux: sub (except_in_nsums f) (Nintc n).
  by move => t /etc/(NintcP nN).
apply: aux;apply: finite_Nintcc.
Qed.



Lemma nsum_p12a f t: nat_ord_seq f ->
    inc t (permutations Nat) -> ~ finite_set (nsupport f) ->
    least_rem (n_sum (f_perm_t f t)) <=o  least_rem (n_sum f).
Proof.
move => ax tp fs.
move: (nsum_p9 ax fs) =>[n0 n0N remf].
move/(all_sume_p4b ax tp): fs => fts.
move:(nsum_p9 (f_perm_t_ax ax tp) fts) =>[n1 n1N remtf].
move: (except_in_nsum_finite ax) => [n2 n2N n2p].
set E := fun_image (except_in_nsums f) (Vf (inverse_fun t)).
have fse: finite_set E.
  apply: finite_fun_image; apply(except_in_nsum_finite2 ax).
  have sN: sub E Nat. 
  move/permutationsP:tp => /inverse_bij_bp [[[ft _]_] st tt].
  move => x/funI_P [i /Zo_S iN ->]; Wtac.
move: (finite_subset_Nat_bis sN fse) =>[n3 n3N n3p].
pose bp i m n := [/\ natp n, m <c n &  Vg f (Vf t i) <=o Vg f n].
have aux i m: natp i -> natp m -> n3 <=c i -> exists n, bp i m n.
  move => iN mN la.
  move/permutationsP:tp => [ bt st tt].
  have tiN: natp (Vf t i) by rewrite /natp; Wtac; [ fct_tac | ue].
  case: (inc_or_not (Vf t i)  (except_in_nsums f)) => h.
    have sit: inc i (source t) by ue.
    have: inc i E by apply /funI_P;ex_tac; rewrite  (inverse_V2 bt sit). 
    by move=> /n3p /cltNge; case.
  set T := (Zo Nat (fun n => Vg f (Vf t i) <=o Vg f n)).
  case:(all_exists_dichot2 (fun n => m <c n) T); last first.
    by move => [n /Zo_P[qa qb] qc]; exists n. 
  move => ha; case: h; apply: (Zo_i tiN). 
  have hb: sub T (csucc m).
     move => s sT; apply/(NleP mN).
     have nN: natp s by move/ Zo_S: sT. 
     by case: (NleT_el nN mN) => //; move:(ha _ sT).  
  exact:(sub_finite_set  hb (finite_set_nat (NS_succ mN))).
pose b i m := intersection (Zo Nat (bp i m)).
have aux2 i m: natp i -> natp m -> n3 <=c i  -> bp i m (b i m).
  set Q:= (Zo Nat (bp i m)).
  have oQ: ordinal_set Q by move => x/Zo_S /OS_nat.
  move => ha hb hc; move: (aux _ _ ha hb hc) =>[n nn].
  have neQ: nonempty Q by exists n; apply:Zo_i => //; case: nn.
  by move: (least_ordinal0 oQ neQ) => /proj32/Zo_hi.
move: (cmax_p1 (CS_nat n1N) (CS_nat n3N)).
set n13 := cmax n1 n3; move => [n13_la n13_lb].
have n13N: natp n13  by rewrite/n13/cmax/Gmax; Ytac h.
pose ci := b n13 n0.
pose c :=  induction_term  (fun n => b (csucc (n +c n13))) ci.
have c0: c \0o  = ci by apply: induction_term0.
move: (aux2 n13 n0 n13N n0N n13_lb);  rewrite -/ci - c0 => c0p.
have crec i: natp i -> c (csucc i) = b (csucc (i +c n13)) (c i).
  by move => iN; apply: induction_terms.
have cic i: natp i -> bp (csucc (i +c n13)) (c i) (c (csucc i)).
  have qq:= (cleT n13_lb (cleS n13N)).
  move: i; apply: Nat_induction.
    rewrite (crec _ NS0) (csum0l  (CS_nat n13N)); apply: aux2; fprops.
    exact: (proj31 c0p).
  move => i iN /proj31 Hrec; rewrite (crec _ (NS_succ iN)).
  have ll := (cleT qq (cleSS (Nsum_Mle0 (csucc i) n13N))).  
  apply: aux2; fprops.
move: (proj32 c0p) => c0_la.
have c0_lb i: natp i -> (c i) <c c (csucc i) by move/cic; case.
have cN i: natp i -> natp (c i).
  move => iN; case: (equal_or_not i \0c) => nz.
    by move: (proj31 c0p); rewrite nz.
  by move: (cpred_pr iN nz) => [/cic /proj31 sa ->].
have c0_lc i: natp i ->  Vg f (Vf t (i +c n13)) <=o Vg f (c i).
  move => iN; case: (equal_or_not i \0c) => nz.
    by rewrite nz; move: (proj33 c0p); rewrite (csum0l (CS_nat n13N)).
  move: (cpred_pr iN nz) => [sa sb].
  by move: (proj33 (cic _ sa));  rewrite - (csum_Sn _ sa) - sb.
clear crec cic c0p.
move:Nat_order_wor => [wor sr].
have  or := proj1 wor.
pose fna := Lg Nat (fun i => Vg f (Vf t (i+c n13))).
pose fnb := Lg Nat (fun i => Vg f (c i)).
have fnag: fgraph fna by rewrite /fna; fprops.
have fnbg: fgraph fnb by rewrite /fnb; fprops.
have dfna: domain fna = substrate Nat_order by rewrite /fna sr; aw.
have dfnb:  domain fnb = substrate Nat_order  by rewrite /fnb sr; aw.
have fnab x: inc x (substrate Nat_order) -> Vg fna x <=o Vg fnb x.
  by rewrite /fna /fnb sr => xN; rewrite !LgV//; apply: c0_lc.
move: (isum_p8 wor fnag fnbg dfna dfnb fnab) => le1.
have fnax:  [/\ fgraph fna, domain fna = substrate Nat_order
     & allf fna ordinalp].
  by split => // x; rewrite dfna => /fnab /proj31.
have: ipartial_sum fna Nat_order (substrate Nat_order) =
      ipartial_sum (f_perm_t f t) Nat_order (Nat -s n13).
  set shift := Lf (fun i => n13 +c i) Nat (Nat -s n13).
  have sr1: sub  (Nat -s n13) (substrate Nat_order).
    by rewrite sr; apply: sub_setC.
  move: (iorder_osr or sr1).
  set r' := (induced_order Nat_order (Nat -s n13)).
  move => [or2 sr2].
  have axs: lf_axiom (csum2 n13) Nat (Nat -s n13).
    move => x xN; apply/setC_P; split; first by apply: NS_sum.
    by move => /(NltP n13N) /cltNge; case;  apply: csum_M0le; fprops.
  have bsh: bijection shift.
    apply: lf_bijective => //.
      by move => x y xN yhN; apply:csum_eq2l.
    move => y /setC_P [yN xl].
    case: (NleT_el n13N yN); last by move/(NltP n13N).
    move => xcp;  move: (cdiff_pr xcp); move: (NS_diff n13 yN) => av bv.
    exists (y -c n13) => //.
  have ois : order_isomorphism shift Nat_order r'.
    split => //; first  by split => //; rewrite/shift; aw. 
    hnf; rewrite /shift; aw => x y xN yN; rewrite !LfV//.
    move:(axs x xN) (axs y yN) => xs ys.
    split.
      move /Nat_order_leP =>[_ _ lexy]; apply/(iorder_gle0P _ xs ys).
      apply/Nat_order_leP; split => //; fprops.
      by apply: csum_Meqle.
    move/(iorder_gle0P _ xs ys)=> /Nat_order_leP/proj33 /(csum_le2l n13N xN yN).
    by move => kk; apply /Nat_order_leP.
  rewrite (@isum_p11 fna Nat_order r' shift wor ois fnax). 
  set w := Lg _ _.
  have ->: w = restr (f_perm_t f t) (substrate r').
    apply: Lg_exten; rewrite sr2 => x xs.
    have xts: inc x (target shift) by rewrite /shift; aw.
    move: (inverse_V bsh xts).
    move: (inverse_Vis bsh xts); rewrite {2}/shift; aw.
    set y :=  (Vf (inverse_fun shift) x) => yN.
    rewrite /shift LfV// => eqa.
    move/setC_P : xs => [xN _].
    by rewrite /fna /f_perm_t !LgV//  csumC eqa.
  have tt: sub (Nat -s n13) (Nat -s n13) by [].
  by rewrite /ipartial_sum sr2 (double_restr _ tt)/r' (iorder_trans _ tt).
rewrite -/(n_partial_sum (f_perm_t f t) _) -/(n_sum_from_n _ _).
rewrite (remtf _  n13N n13_la); move <-.
apply: (oleT le1).
clear le1 fnax fnab dfna fnag fna.
set E1 := fun_image Nat c.
have cmon1 i j: i <c j -> natp j -> c i <c c j.
  move => lij jN; move: j jN lij; apply: Nat_induction.
    by move/clt0.
  move => j jN Hrec; move/(cltSleP jN); move:(c0_lb j jN) => aux1.
  case/cle_eqVlt; first by move ->.
  move/Hrec => /proj1 xx. apply: (cle_ltT xx aux1).
have cmon2 i j: i <=c j -> natp j -> c i <=c c j.
  move => /cle_eqVlt cp jN; case: cp => h. 
    by rewrite h; apply: cleR; apply: CS_nat; apply: cN.
  by move: (proj1 (cmon1 i j h jN)).  
  have sa: sub E1 (Nat -s n0).
    move => x /funI_P [i iN ->]; move: (cmon2 _ _ (cle0n iN) iN) => la.
    move: (clt_leT   c0_la  la) => lb.
    apply/setC_P; split; first by apply: cN.
    move/(NltP n0N); apply cleNgt; exact: (proj1 lb).
suff ->:ipartial_sum fnb Nat_order (substrate Nat_order) = n_partial_sum f E1.
  rewrite - (remf n0 n0N (cleR (CS_nat n0N))).
  have sb: sub (Nat -s n0) (substrate Nat_order) by rewrite sr; apply:sub_setC.
  exact: (isum_p10 wor sa sb (nsum_p0 ax)).
rewrite /n_partial_sum.
pose cf := Lf c Nat E1.
have axcf: lf_axiom c Nat E1 by move => x xN; apply: funI_i.
have bcf: bijection cf.
  apply: lf_bijective => //; last by move => y /funI_P.
  move => u v uN vN eqa; case: (NleT_ell uN vN) => // lt.
    by move: (proj2 (cmon1 _ _  lt vN)).
  by move: (nesym (proj2 (cmon1 _ _  lt uN))).
have axb: [/\ fgraph fnb, domain fnb = substrate Nat_order & allf fnb ordinalp].
   split; fprops;hnf; rewrite /fnb; aw => x xN; rewrite LgV//.
   by apply: (proj33 ax); rewrite (proj32 ax); apply: cN.
have sb: sub E1 (substrate Nat_order).
  by rewrite sr => x /sa /setC_P/proj1.
move: (iorder_osr or sb). 
set r' := induced_order _ _; move =>[ort' sr'].
have is2: order_isomorphism cf Nat_order r'.
  split => //; first by rewrite sr sr'; split; rewrite /cf; aw.
  hnf; rewrite /cf; aw => x y xN yN; rewrite !LfV//.
  move:(axcf x xN) (axcf y yN) => xs ys.
  split.
    move /Nat_order_leP =>[_ _ lexy]; apply/(iorder_gle0P _ xs ys).
    apply/Nat_order_leP; split;fprops.
  move/(iorder_gle0P _ xs ys) => /Nat_order_leP/proj33 ll.
  apply /Nat_order_leP; split => //.
  case: (NleT_el xN yN) => // ly. 
  by move:(cltNge (cmon1 y x ly xN) ll).
have ww: sub E1 E1 by [].
rewrite (@isum_p11 fnb Nat_order r' cf wor is2 axb).
rewrite /ipartial_sum sr' /r' (iorder_trans  _ ww); f_equal.
apply: Lg_exten => x xe1; aw; rewrite /fnb.
have xs: inc x (target cf) by rewrite /cf; aw.
move: (inverse_Vis bcf xs) (inverse_V bcf xs); rewrite {2} /cf; aw.
by set y := Vf _ _ => yN; rewrite /cf ! LgV// LfV//;  move ->.
Qed.
                               
Lemma nsum_p12b f t: nat_ord_seq f ->
    inc t (permutations Nat) -> ~ finite_set (nsupport f) ->
    least_rem (n_sum (f_perm_t f t)) = least_rem (n_sum f).
Proof.
move => ha hb hc.
apply: (oleA (nsum_p12a ha hb hc)).
move/ (all_sume_p4b ha hb): hc => hc'.
move: (f_perm_t_ax ha hb) => ha'.
move:(permutation_Si hb) => hb'.
move: (nsum_p12a ha' hb' hc').
set h := f_perm_t _ _; have -> //: h = f.
move: ha =>[fgf df _].
rewrite /h/f_perm_t; apply: fgraph_exten; fprops; aw; first exact.
move/permutationsP: hb =>[bt st tt].
move => i iN /=.
have it: inc i (target t) by ue.
move: (inverse_Vis bt it)(inverse_V bt it); rewrite st ;  move=> ra rb.
rewrite !LgV//; ue.
Qed.  


Lemma nsum_p12c f t
  (g := f_perm_t f t)
  (rho := n_sum_rem f)
  (E := n_sum_small_idx f)
  (Eg := fun_image E (Vf (inverse_fun t))): 
  nat_ord_seq f -> inc t (permutations Nat) ->
  [/\  finite_set E, n_sum f = (n_partial_sum f E) +o rho &
    n_sum g = (n_partial_sum g Eg) +o rho ].
Proof.
move => axf pt.
set S:= nsupport f.
set S':= nsupport g.
move:(f_perm_t_ax axf pt) => axg.
move/permutationsP: (pt) => [bt st tt]; move: (proj1 (proj1 bt)) => ft.
have aux p: Zo Nat (fun i => p (Vg g i)) = 
    fun_image (Zo Nat (fun i => p (Vg f i)))  (Vf (inverse_fun t)).
  rewrite /g/f_perm_t; set_extens i.
    move => /Zo_P[iN]; rewrite LgV// => ha.
    have isf: inc i (source t) by ue.
    apply/funI_P; exists (Vf t i);first by  apply: Zo_i =>  //; Wtac. 
    by rewrite (inverse_V2 bt isf) .
  move/funI_P => [j /Zo_P [jN jv] ->].
  have tj: inc j (target t) by ue. 
  move:(inverse_Vis bt tj); rewrite st => ha.
  by apply (Zo_i ha);  rewrite LgV//  (inverse_V bt tj).
have aux2 p:
  finite_set (Zo Nat (fun i => p (Vg g i))) <->
  finite_set (Zo Nat (fun i => p (Vg f i))).
  apply:  (iff_trans(card_finite_setP _)).
  apply:  (iff_trans _ (iff_sym (card_finite_setP _))).
  have h:  {inc Zo Nat (fun i => p (Vg f i)) &,
                injective (Vf (inverse_fun t))}.
     move => x y /Zo_S xN /Zo_S yN sv.
     have xtt: inc x (target t) by ue.
     have ytt: inc y (target t) by ue.
     by rewrite - (inverse_V bt xtt) sv (inverse_V bt ytt).             
  by rewrite aux (cardinal_fun_image h). 
have eqa: S' = fun_image S (Vf (inverse_fun t)).
  apply: (aux (fun i => i <> \0o)).
have sfs: finite_set S' <-> finite_set S.
  apply: (aux2 (fun i => i <> \0o)).
have fsE: finite_set E by apply:  nsum_p10c.
have eqb: n_sum f = n_partial_sum f E +o rho by apply: (nsum_p10g axf).
split => //.
case: (p_or_not_p  (finite_set S)) => fs.
  move/sfs: (fs) => fs'.
  rewrite /rho /Eg /E/ n_sum_small_idx /n_sum_rem; Ytac0; Ytac0.
  by rewrite - eqa; apply: nsum_p10f.
move/sfs: (fs) => fs'.
rewrite  (nsum_p10g axg) -/g.
have rc: least_rem (n_sum f) = rho  by rewrite /rho /n_sum_rem;Ytac0.
rewrite /n_sum_small_idx; Ytac0. rewrite /Eg.
move: (nsum_p12b axf pt fs); rewrite rc -/g => ee.
rewrite /n_sum_rem /E /n_sum_small_idx /n_sum_small_idx1; Ytac0; Ytac0.
by rewrite ee rc - aux. 
Qed.


Lemma nsum_p13a f t:
  nat_ord_seq f -> inc t (permutations Nat) ->
  small_set (n_sum_small_idx f) -> n_sum f = n_sum (f_perm_t f t).
Proof.
move => ha hb hd.
move:Nat_order_wor => [wor sr].
move:(nsum_p12c ha hb) => [_ -> ->]; apply: f_equal2=> //.
rewrite /n_partial_sum.
case/small_set_pr: hd.
  by move ->; rewrite funI_set0 /n_partial_sum !isum_p2.
move => [n nE]; rewrite nE funI_set1.
have nN: natp n.
  move: (set1_1 n); rewrite - {1} nE.
  by rewrite/n_sum_small_idx; Ytac h; move/Zo_S.
have ns: inc n (substrate Nat_order) by ue.
move: (nsum_p0 ha) => axf.
move:(nsum_p0 (f_perm_t_ax ha hb)) => axg.
move/permutationsP: (hb) => [bt st tt].
have xst: inc n (target t) by ue.
move: (inverse_Vis bt xst); rewrite st  => yN.
move: (yN); rewrite - sr => ysr.
rewrite  /n_partial_sum (isum_p3 wor axf ns).
by rewrite (isum_p3 wor axg ysr) /f_perm_t LgV// (inverse_V bt xst).
Qed.


Theorem nsum_p13b f: nat_ord_seq f ->
  finite_set (n_all_sums f).
Proof.
move => axf.
move:(nsum_p10g axf).
set E := (n_sum_small_idx f); set rho := n_sum_rem f => sv.
have fse: finite_set E by apply: nsum_p10c.
have sEN: sub E Nat.
  by rewrite /E/n_sum_small_idx; Ytac h; apply: Zo_S.
move: (proj1 (sub_nat_isomorphism sEN) fse) =>[n nN [g1 is1]].
move: (nsum_p0 axf) => ax.
move:Nat_order_wor => [wor sr].
have ses: sub E (substrate Nat_order) by ue.
move: (induced_wor wor ses) (iorder_sr (proj1 wor) ses).
set rE := (induced_order Nat_order E) => worE srE.
set fE := restr f E.
have eq1: n_partial_sum f E = ipartial_sum fE rE (substrate rE).
  rewrite /n_partial_sum /ipartial_sum /rE srE (iorder_trans _ (@sub_refl E)).
  by rewrite /fE double_restr.
have axE: [/\ fgraph fE, domain fE = substrate rE & allf fE ordinalp].
  rewrite /fE Lgd; split; fprops; hnf; aw => t tE; rewrite LgV//.
  by apply:(proj33 axf); rewrite (proj32 axf); apply: sEN.
have sns: sub n (substrate Nat_order).
   rewrite sr => t tN; apply: (NS_inc_nat nN tN).
move: (induced_wor wor sns) (iorder_sr (proj1 wor) sns).
set rn := (induced_order Nat_order n) => worb srn.
move: (isum_p11 worE is1 axE); rewrite - eq1 -/rE -/rn srn.
set b := Lg _ _; move => eq2.
pose bpt t := Lg n (fun i => Vg b (Vf t i)).
set F1 := fun_image (permutations n) (fun t => ipartial_sum (bpt t) rn n).
set F2 := fun_image F1 (fun x => x +o rho).
suff h: sub (n_all_sums f) F2.
  have fs: finite_set F2.
    apply: finite_fun_image; apply: finite_fun_image. 
    apply/card_finite_setP; rewrite (card_permutations (finite_set_nat nN)).
    by rewrite (card_card (CS_nat nN)); apply: NS_factorial.
  exact: (sub_finite_set h fs).
move => v /funI_P [t pt ->].
rewrite (proj33 (nsum_p12c axf pt)); apply: funI_i.
move/permutationsP:pt => tprop.
rewrite -/E; set F := fun_image _ _.
have cF: F =c E. 
   apply: cardinal_fun_image => x y xs ye.
   move: (inverse_bij_bp tprop) =>[ [[_ hh] _] st _]. 
   by apply: hh; rewrite st; apply: sEN.
move:tprop =>[bt st tt].
have sFN: sub F Nat.
  move => x /funI_P [y yR ->]; rewrite - st.
  have yt: inc y (target t) by rewrite tt; apply: sEN.
  exact: (inverse_Vis  bt yt).
have sfs: sub F (substrate Nat_order) by ue.
move: (induced_wor wor sfs) (iorder_sr (proj1 wor) sfs).
set rF := (induced_order Nat_order F) => worF srF.
set fF := restr  (f_perm_t f t) F.
have ->: n_partial_sum (f_perm_t f t) F = ipartial_sum fF rF (substrate rF).
  rewrite /n_partial_sum /ipartial_sum /rF srF (iorder_trans _ (@sub_refl F)).
  by rewrite /fE double_restr.
have axF: [/\ fgraph fF, domain fF = substrate rF & allf fF ordinalp].
  rewrite /fF; aw; split; fprops; hnf; aw => x tF; rewrite LgV//.
  have xN: natp x by apply: sFN.
  rewrite /f_perm_t LgV//;  apply:(proj33 axf); rewrite (proj32 axf).
  Wtac; [ fct_tac |  ue ].
have fsf: finite_set F.
  by apply/card_finite_setP; rewrite cF; apply/card_finite_setP.
move: (proj1 (sub_nat_isomorphism sFN) fsf) =>[n1 n1N [g2 is2]].
have eq4: n1 = n.
  move: is1 is2 => [_ _ [ba sa ta] _] [_ _ [bb sb tb] _].
  move: (card_bijection ba)(card_bijection bb).
  have sms: sub n1 (substrate Nat_order).
   rewrite sr => x xN; apply: (NS_inc_nat n1N xN).
  move: (iorder_sr (proj1 wor) sms) => srm.
  rewrite sa ta sb tb srE srF srn srm cF (card_card (CS_nat nN)).
  by rewrite (card_card (CS_nat n1N)); move => <- <-.
rewrite eq4 in is2.  
rewrite (isum_p11 worF is2 axF) srn -/rn.
pose cv i := Vf g1 (Vf t (Vf (inverse_fun g2) i)).
move: is1 is2 => [_ _ [bg1 sg1 tg1]  _] [_ _ [bg2 sg2 tg2] _].
move: (proj1 (proj1 bg1))(proj1 (proj1 bg2)) => fg1 fg2.
move: sg1 tg1 sg2 tg2. rewrite srE srF srn => sg1 tg1 sg2 tg2.
have ha i: inc i n -> inc  (Vf (inverse_fun g2) i) F.
  by rewrite -tg2 - sg2 => it ;apply: (inverse_Vis bg2).
have hb i: inc i n -> inc (Vf t (Vf (inverse_fun g2) i)) E.
  move/ha => /funI_P [x xÊ ->]; rewrite (inverse_V bt) => //.
  by rewrite tt; apply: sEN.
have hc: lf_axiom cv n n by move => i /hb vE; rewrite/cv; Wtac.
set c := Lf cv n n.
have fpc:function_prop c n n.
  by rewrite /c/function_prop; saw; apply: lf_function.
have cp: inc c (permutations n).
  apply: (permutation_if_inj (finite_set_nat nN) fpc).
  apply: lf_injective => // x y xn yn; rewrite /cv.
  move: (hb _ xn) (hb _ yn); rewrite - sg1 => xa ya.
  move:  (sFN _ (ha _ xn)) (sFN _ (ha _ yn)); rewrite - st => xb yb.
  move/ (proj2 (proj1 bg1) _ _ xa ya).
  move/ (proj2 (proj1 bt) _ _ xb yb)=> eqxx.
  rewrite - tg2 in xn yn.
  by rewrite - (inverse_V bg2 xn) - (inverse_V bg2 yn) eqxx.
apply/funI_P; ex_tac; congr (ipartial_sum _ rn n).
apply: Lg_exten => i iE.
have ra:  inc (Vf (inverse_fun g2) i) F by apply: ha.
have rb:  inc (Vf (inverse_fun g2) i) Nat by apply: sFN; apply: ra.
have rc:  inc (Vf c i) n by  rewrite /c LfV//; apply:hc.
have rd: inc (Vf (inverse_fun g1) (Vf c i)) E.
  by rewrite - sg1; apply: (inverse_Vis bg1); rewrite tg1; apply: rc.
have re: inc (Vf t (Vf (inverse_fun g2) i)) (source g1).
  by rewrite sg1; apply: hb.
by rewrite /fF/f_perm_t /b /fE/c/cv !LgV// LfV// (inverse_V2 bg1 re).
Qed.


Section SierpinskiEx1.
Variables (a b c n: Set).
Hypothesis (ao: ordinalp a) (bo: ordinalp b)  (co: ordinalp c).
Hypothesis (nN: natp n).
Let f := Lg Nat (fun i => (Yo (i = \0c) a (Yo (i <=c n) b c))).

Lemma sier_ex1_p1:  nat_ord_seq f.
Proof.
rewrite/f; split; fprops;aw; hnf; aw; trivial.
by move => u iN; rewrite LgV//; Ytac h => //; Ytac h2.
Qed.

Lemma sier_ex1_p2:  (c = \0c) <-> finite_set (nsupport f).
Proof.
split => hyp.
  have ra: sub (nsupport f) (csucc n).
    move => t /Zo_P [iN]; rewrite /f LgV//; Ytac ha.
      by rewrite ha => _; apply/(NleP nN); apply: cle0n.
    by Ytac hb => // _;  apply/(NleP nN).
  exact: (sub_finite_set ra (finite_set_nat (NS_succ nN))).
have sn: sub  (nsupport f) Nat by apply: Zo_S.
move: (finite_subset_Nat_bis sn hyp) => [m] mN mp; ex_middle bad.
move: (Nmax_p1 (NS_succ nN) mN).
set k := cmax _ _; move => [kN /(cleSltP nN)  /cleNgt qb  /cleNgt qc].
case: (inc_or_not k (nsupport f)); first by  move/mp. 
case; apply:(Zo_i kN); rewrite /f LgV//; Ytac ha; last by Ytac hb.
by case: qb; rewrite ha; apply: cle0n.
Qed.
  
Lemma sier_ex1_p3: c <> \0c -> n_sum_rem f = c *o omega0.
Proof.
move => cnz.
have cp: \0o <o c by apply: ord_ne0_pos.
apply: (nsum_eventually_const sier_ex1_p1 cp).
exists (csucc n); first by apply: NS_succ.
move => t tN /(cleSltP nN)/cltNge h0; rewrite /f LgV//; Ytac h1.
 by case: h0;rewrite h1; apply: cle0n.
Ytac h2 => //.
Qed.

Lemma sier_ex1_p4: c <> \0c ->  sub (n_sum_small_idx f) (csucc n).
Proof.
move => cnz.
have cp: \0o <o c by apply: ord_ne0_pos.
move /sier_ex1_p2: (cnz) => fs.
move: (sier_ex1_p3 cnz).
rewrite /n_sum_rem /n_sum_small_idx; Ytac0; Ytac0 => rv.
move => i /Zo_P [iN]; rewrite rv /f LgV// =>  fv; apply/(NleP nN).
move: fv; Ytac ha; first by rewrite ha => _ ;  apply: cle0n.
Ytac hb => // le.
case: (oltNge (proj32 (indecomp_prod2 cp)) le).
Qed.
  
 
                                

  
End SierpinskiEx1.



  

  

End InfiniteOsum.
Export InfiniteOsum.
