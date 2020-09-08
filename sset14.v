(** * Theory of Sets : Ordinals
  Copyright INRIA (2011-2013 2018) Marelle Team (Jose Grimm).
*)

(* $Id: sset14.v,v 1.5 2018/09/04 07:57:59 grimm Exp $ *)


Set Warnings "-notation-overridden".
From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Warnings "notation-overridden".

Require Export sset13b.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Ordinals4.




(** ** Epsilon ordinals *)

(* Noter *)

Lemma oopow_normal: normal_ofs oopow.  
Proof. exact (opow_normal ole_2omega). Qed.

Definition epsilonp x := ordinalp x /\ oopow x = x.

Lemma ord_eps_p1 x: ordinalp x -> x <=o (oopow x).
Proof.
move=> ox. 
exact: (oleT (oprod_M1le olt_0omega ox) (opow_Mspec2 ox ole_2omega)).
Qed.

Lemma ord_eps_p2 a b c (x := ((oopow a) *o b) +o c) :
  ordinalp a ->  \0o <o b -> ordinalp c ->
  (a <=o x /\ (x = a -> [/\ c = \0o, b = \1o & epsilonp x])).
Proof.
move=> oa bp oc.
have oo:= OS_omega.
have ob:= proj32_1 bp.
have op:= OS_pow oo oa.
have ot:= OS_prod2 op ob.  
have ox:= (OS_sum2 (OS_prod2 op ob) oc).
have le1:= (ord_eps_p1 oa).
have le2:= (oprod_Mle1 op bp).
have le3:= (osum_Mle0 ot oc).  
have le4:=(oleT le1 le2). 
have le5:=(oleT le4 le3).
split => // xa; rewrite xa; rewrite -/x in le3.
have pa: a = ((oopow a) *o b) by apply: (oleA le4); rewrite - {2} xa. 
have c0: c = \0c by  apply: (osum2_a_ab oa oc); rewrite -{2}  xa /x -pa.
case: (oone_dichot bp) => b1.
  by split => //; split => //; rewrite {2} pa b1 oprod1r.
by move: (oprod_Meq1lt b1 (oopow_pos oa)); rewrite - pa => /(oleNgt le1).
Qed.

Lemma ord_eps_p3 x: epsilonp x -> omega0 <o x.
Proof.
move: oopow1 => o1 [ox oex]; move: (proj2 (olt_1omega)); rewrite - o1.
move:(oopow_pos ox); rewrite oex => xp.
case: (oone_dichot xp) => xo; first by rewrite - xo oex.
move => _; rewrite - oex; exact: (opow_Mo_lt xo).
Qed.

Lemma ord_eps_p4: iclosed_collection epsilonp.
Proof.
by move: (iclosed_fixpoints oopow_normal) => []. 
Qed.

Lemma expilon_prop x: \0o <o x ->(odegree x = x <-> epsilonp x).
Proof.
move => xp; split; last by move => [ox {1} <-]; rewrite (odegree_opow ox).  
move:(the_cnf_split xp) =>  [ bp bf /proj31_1 oc]  eq1 dxx.
move:(proj2 (ord_eps_p2 (OS_degree (proj32_1 xp)) bp oc)). 
by rewrite - eq1 => h; move: (proj33 (h (esym dxx))).
Qed.

  

Definition epsilon_fct := the_least_fixedpoint_ge oopow.
Definition epsilon_fam := first_derivation oopow.


Lemma epsilon_fct_pr0 x: ordinalp x ->
  least_fixedpoint_ge oopow x (epsilon_fct x).
Proof. exact: (normal_ofs_fix (oopow_normal)). Qed.

Lemma epsilon_fct_pr1 x: ordinalp x -> 
  epsilonp (epsilon_fct x).
Proof.
by move/epsilon_fct_pr0 => [/proj32 pa pb _].
Qed.

Lemma epsilon_fct_pr2 C (E:= cnext C): infinite_c C ->
  (forall x, inc x E -> inc (epsilon_fct x) E).
Proof.
move => iC.
apply:next_fix_point_small => //.
  apply:oopow_normal.
move:(cnext_pr1 (proj1 iC)); rewrite -/E; move=> [pa pb pc].
move => x xe; apply:cnext_pow => //. 
exact :(cnext_leomega iC (oleR OS_omega)).
Qed.

Lemma epsilon_fct_pr3 (e:= epsilon_fct \1o) :
  epsilonp e /\ 
  forall x, epsilonp x -> e <=o x.
Proof.
move: (epsilon_fct_pr0 OS1) => [/proj32 pa pb pc]; split; first  exact.
move => x h; move: (ole_ltT (ole0x OS_omega) (ord_eps_p3 h)) => x1.
by move: h => [ox oex]; apply: pc => //; apply/oge1P.
Qed.

Lemma epsilon_fam_pr0 x: ordinalp x -> 
  epsilonp (epsilon_fam x).
Proof.
move: (iclosed_fixpoints oopow_normal) => [pa pb].
by move:(ordinals_col_p1 (proj1 pa) pb) => [na _ _ _ _]; move /na.
Qed.

Lemma epsilon_fam_pr1 y: epsilonp y ->
  exists2 x, ordinalp x & y = epsilon_fam x.
Proof.
move: (iclosed_fixpoints oopow_normal) => [pa pb].
move:(ordinals_col_p1 (proj1 pa) pb) => [_ na _ _ _];apply:na.
Qed.

Lemma epsilon_fam_pr2: epsilon_fam \0o = epsilon_fct \1o.
Proof.
apply:first_derivation_p2; first by apply:oopow_normal.
apply: oopow_nz; fprops.
Qed.

Lemma epsilon_fam_pr2': epsilon_fam \0o = epsilon_fct \0o.
Proof.
apply:first_derivation_p1; by apply:oopow_normal.
Qed.

Lemma epsilon_fam_pr2'': epsilon_fam \0o = epsilon_fct (osucc omega0).
Proof.
rewrite epsilon_fam_pr2' /epsilon_fct.
move: oopow_normal => nf.
move: (normal_ofs_fix nf OS0).
set u := the_least_fixedpoint_ge _ _; move => [[_ sa _] sb sc].
move: (normal_ofs_fix nf (OS_succ OS_omega)).
set v := the_least_fixedpoint_ge _ _; move => [[_ sa' _] sb' sc'].
apply: (oleA (sc _ (ole0x sa') sb')).
apply: sc' => //; apply /oleSltP; exact : (ord_eps_p3 (conj sa sb)).
Qed.

Lemma epsilon_fam_pr3 x y: ordinalp x ->
  epsilon_fam x <o y -> y <=o epsilon_fam (osucc x) ->
  epsilon_fct y =  epsilon_fam (osucc x).
Proof.
move => ox.
move: (iclosed_fixpoints oopow_normal) => pa.
move: (iclosed_col_fs pa ox). 
rewrite /epsilon_fam/first_derivation.
set fx := (ordinalsf _ x); set fy := (ordinalsf _ (osucc x)). 
move => [fxy ex [ofy ey] etc] l1 l2.
move: (epsilon_fct_pr0 (proj31 l2)); set z :=  (epsilon_fct y).
move => [sa sb sc]; apply:oleA; first by apply: sc.
have oz:= proj32 sa; have cc1:= (olt_leT l1 sa).
by apply: etc.
Qed.

Lemma epsilon_fam_pr4 x: ordinalp x ->
  epsilon_fam (osucc x) = epsilon_fct (osucc (epsilon_fam x)).
Proof.
apply: first_derivation_p3;apply: oopow_normal.
Qed.

Lemma epsilon_fam_pr5: normal_ofs epsilon_fam.
Proof.
exact:  (ordinals_col_p2 (iclosed_fixpoints oopow_normal)).
Qed.

Lemma epsilon_fam_pr6 C (E := cnext C)  (F:= Zo E epsilonp) : infinite_c C ->
   order_isomorphism (Lf epsilon_fam E F) (ordinal_o E) (ole_on F).
Proof.
move => ic.
have aux:forall x,inc x (cnext C) -> inc (oopow x) (cnext C).
  move => x xe; apply:cnext_pow => //. 
  exact: (cnext_leomega ic (oleR OS_omega)).
move: (first_derivation_p4 ic oopow_normal aux).
have -> //: (Zo E (fun z => omega0 ^o z = z)) = F.
apply: Zo_exten1 => x xE; split; [move => h; split => // | by move => []].
by move/(cnextP (proj1 ic)):xE => [].
Qed.


Lemma epsilon_fam_pr7 C (E := cnext C)
   (F:= Zo E epsilonp) : infinite_c C -> cardinal E = cardinal F.
Proof.
move /epsilon_fam_pr6; rewrite -/F -/E; move => [_ _ [bf _ _] _].
apply /card_eqP; exists (Lf epsilon_fam E F); saw.
Qed.

Lemma countable_epsilon x: ordinalp x ->
  (countable_ordinal x <-> countable_ordinal (epsilon_fam x)).
Proof.
move: CIS_omega aleph_oneP => h T.
move: (epsilon_fam_pr6 h) => [_ _ [bf _ _] _].
set E := (cnext omega0) in T bf.
set f :=  (Lf epsilon_fam E (Zo E epsilonp)).
have ff: function f by move: bf => [[]].
have sf: source f = E by rewrite /f; aw.
have tf: target f = (Zo E epsilonp) by rewrite /f; aw.
have H: lf_axiom epsilon_fam E (Zo E epsilonp).
  move => s sE; move: (sE); rewrite - {1} sf => / (Vf_target ff).
  by rewrite tf /f /Lf /Vf /graph pr1_pair LgV.
move => ox; split; first by  move /T /H /Zo_S/T.
move /T => h1; apply /T.
have wa: inc (epsilon_fam x) (target f).
 by rewrite tf; apply /Zo_P; split => //; apply: epsilon_fam_pr0.
move: (proj2 (proj2 bf) _ wa); aw; move => [a ae]; rewrite LfV// => eq.
move/(cnextP (proj1 h)):(ae) => [oa _].
move: epsilon_fam_pr5 => [ii _].
by case:(oleT_ell ox oa); first (by move => ->); move /ii =>[]; rewrite eq.
Qed.


Definition Cantor_Omega := aleph_one -s omega0.


Lemma Cantor_omega_pr x: 
  inc x Cantor_Omega <-> (countable_ordinal x /\ omega0 <=o x).
Proof.
split.
  move /setC_P => [/aleph_oneP pa pb]; split => //.
  by case: (oleT_el OS_omega (proj1 pa)) => // /oltP0 [_ _].
move => [pa pb]; apply/setC_P; split; first by apply /aleph_oneP.
by move => xo; move: (proj33 pb _ xo)(ordinal_irreflexive (proj32 pb)).
Qed.

Lemma Cantor_omega_pr2: cardinal Cantor_Omega = aleph_one.
Proof.
move: CIS_omega => h.
move: (cnext_pr1 (proj1 h)); rewrite - /aleph_one; move => [pa pb pc].
move:(oclt pb) => pd.
by move:(cardinal_indecomposable1 (cle_inf_inf h (proj1 pb)) pd) => [].
Qed.

Lemma critical_productP
   (CP := critical_ordinal \1o oprod2)
   (p1 := fun y => (exists2 n, ordinalp n & y = oopow (oopow n)))
   (p2 := fun y => omega0 <=o y /\ 
       (forall z, \1o <o z -> z <=o y ->
          exists t, [/\ ordinalp t, indecomposable t & y = z ^o t])):
  forall y, (p1 y <-> p2 y) /\ (CP y <-> p1 y).
Proof.
move: olt_01 olt_1omega OS_omega OS1=> l01 lt1o oo o1.
have auxP: forall y, ordinalp y -> (infinite_o y <-> (omega0 <=o y)).
  move=> y oy; split; first by move/(omega_P1 oy) => h; split => //. 
  by move => [_ _ ] /(omega_P1 oy).
have p21: forall y, p2 y -> p1 y.
  move=> y [iy yp]. 
  move: (yp _ lt1o iy) => [t [ot oit yv]].
  move: (indecomp_prop3 oit) => [n on tb]; exists n => //;ue.
have p02: forall y, CP y -> p2 y.
  move=> y [pa pc pd]; split => //.
  move=> z z1 lezy; case: (equal_or_not z y) => zy.
    exists \1o; rewrite zy (opowx1 (proj32 pa)).
    split => //; apply: indecomp_one.
  have ltzy: z <o y by split.
  move: (olt_leT olt_0omega pa) => y1.
  have z2: \2o <=o z by rewrite - osucc_one ; apply /oleSltP.
  have oz:= proj32 z2.
  move: (ord_ext_div_exists z2 y1)
     => [a [b [c [oa ob oc [bv ltc ltv bnz]]]]].
  set x1:= (z ^o a) *o b.
  have le1: (z ^o a) <=o x1 by rewrite /x1; apply: oprod_Mle1; fprops.
  have cx1 := olt_leT ltc le1.
  have co:=ole0x oc.
  have za1: \1o <=o  (z ^o a) by move /oge1P: (ole_ltT co ltc).
  have le2:= oleT za1 le1.
  have ox1:= proj32 le1.
  have oza:= proj32 za1.
  case: (equal_or_not x1 y) => yx1; last first.
    have ltx1y: x1 <o y by split => //; rewrite bv; apply: osum_Mle0.
    move: (pd _ le2 ltx1y).
    move: (ord_rev_pred  y1); set u := (y -o \1o); move =>  [ou yv].
    rewrite {1} yv bv -/x1 (oprodD OS1 ou ox1) (oprod1r ox1).
    move=> aux1; move: (osum2_simpl (OS_prod2 ox1 ou) oc ox1 aux1) => e1.
    case: (ozero_dichot ou) => uz.
      by move: pc; rewrite yv uz (osum0r OS1); case. 
    by move: (oprod_Mle1 ox1 uz); rewrite e1 => /(oltNge cx1) [].
  case: (equal_or_not  (z ^o a) y) => zay; last first.
    have lt1: (z ^o a) <o y by split=> //; rewrite - yx1.
    move: (pd _ za1 lt1); rewrite -{2} yx1 /x1 => aux1.  
    have zaz: \0o <o z ^o a by apply/oge1P.
    case:(oleNgt lezy). 
    by rewrite (oprod2_simpl (proj32 pa) ob zaz aux1). 
  rewrite - zay; exists a;split => //.
  case: (ozero_dichot oa) => az.
    by move: pc=> [_ xx]; case: xx;rewrite - zay az opowx0.
  apply /indecompP => // d da.
  have od:= proj31_1 da.
  have znz: \0o <o z by exact: (olt_leT bnz (proj1 ltv)). 
  have ad1: \1o <=o (z ^o d) by apply /oge1P;apply: opow_pos.
  move: (opow_Meqlt z2 da); rewrite zay => p4.
  move: (pd _ ad1 p4); rewrite - zay - opow_sum => //.
  apply: opow_regular => //; fprops.
suff p10: forall y, p1 y -> CP y.  
    move=> y; split; split => h.
    - by apply:p02; apply: p10.
    - by apply: p21.
    - by apply: p21; apply: p02.
    - by apply:p10.
move=> y [n on yv].
have yif: omega0 <=o y.
   rewrite yv - {1} oopow1; apply: opow_Mo_le.
   apply: (oge1 (OS_pow oo on) (oopow_nz on)).
have oy:= (proj32 yif).
split; [ exact  | exact:(olt_leT lt1o yif) | ].
by rewrite yv => x x1 x2; exact:  (oprod_crit_aux on x1 x2).
Qed.

Lemma ord_epsilon_p9 x a: epsilonp x -> a <o x->
  [/\ a +o x = x,
  (\1o <=o a -> a *o x = x) &
  (\2o <=o a -> a ^o x = x) ].
Proof.
move=> oex lax.
have oox:=(ord_eps_p3 oex).
have [ox xx] := oex.
have pa: forall n,  \1o <=o n -> n <o x -> n *o x = x. 
  move: (critical_productP x) => [_ pb].
   have: (exists2 n, ordinalp n & x = oopow (oopow n)).
    by exists x => //;rewrite xx xx.
  move /pb => [_ _  pd] //.
split.
   by apply: indecomp_prop1 lax; rewrite -xx; apply: indecomp_prop4.
  by move=> a1;apply: pa a1 lax.
move: OS_omega => oo a2.
have oa:= proj32 a2.
have [lt1o _] := olt_1omega.
have oxx:= (pa _ lt1o oox).
rewrite - {1} oxx (opow_prod oa oo ox).
case: (oleT_el oo oa) => coa; last first.
  by rewrite (opow_int_omega a2 coa).
  have ap:=(olt_leT olt_02 a2). 
rewrite - xx in lax.
move: (the_cnf_p6 ox ap lax) => h2.
have od:=(proj31_1 h2).
move/oge1P:(odegree_infinite  coa) => gd1.
rewrite  (CNF_pow_pr3 coa) - (opow_prod oo (OS_prod2 od oo) ox).
by rewrite -(oprodA od oo ox) (pa _ lt1o oox) (pa _ gd1 h2).
Qed.

Lemma ord_epsilon_p10 x: 
  epsilonp x -> critical_ordinal \2o opow x.
Proof.
move=> oex;move: (oex) => [ox _]; move: (ord_eps_p3 oex) => xo.
split => //.
    exact: (proj1 xo).
  exact: (olt_ltT olt_2omega xo).
move=> a a2 ax; move: (ord_epsilon_p9 oex ax) => [_ _ p]; apply: (p a2).
Qed.

Lemma ord_epsilon_p11 x: ordinalp x -> (\2o ^o x = x) -> 
  x = omega0  \/ epsilonp x.
Proof.
move=> ox hx.
move: (oquoremP ox olt_0omega).
set q := oquo _ _; set r := orem _ _ ; move=> [oq or av bv].
have le22:=oleR (OS2).
have oo:= OS_omega.
case: (equal_or_not r \0o) => rnz; last first.
  have rN: natp r by apply /olt_omegaP.
  move: (cpred_pr rN rnz) => [pb pv].
  have op := (OS_nat pb).
  move: av; rewrite pv (succ_of_nat  pb) - (osum2_succ (OS_prod2 oo oq) op).
  set v := (omega0 *o q) +o cpred r => xs.
  have ov: ordinalp v by rewrite /v; fprops.
  case: (ozero_dichot ov) => vz.
    by case: (proj2  olt_12); move: hx; rewrite xs vz osucc_zero (opowx1 OS2). 
  have o2v: ordinalp (\2o ^o v) by fprops.
  move: hx; rewrite xs (opow_succ OS2 ov) (ord_double o2v) => h.
  move: (osum_Mlele (opow_Mspec le22 ov) (opow_Meqle1 olt_02 vz)).
  rewrite h - (osucc_pr ov). 
  by move/(osum_Meqler OS2 OS1 ov) => /(oltNge olt_12).   
move: av; rewrite rnz (osum0r (OS_prod2 oo oq)).
move => xq; case: (ozero_dichot oq) => qz.
  move: hx; rewrite xq qz oprod0r opowx0 => h1.
  by symmetry in h1;  move: olt_01 => [_] h2.
case: (equal_or_not \1o q) => qo.
  by left;rewrite xq -qo (oprod1r); fprops.
right.
have o2:= olt_2omega.
move: hx;  rewrite xq (opow_prod OS2 oo oq)  (opow_int_omega le22 o2).
move: (ord_rev_pred qz); set y:= (q -o \1o); move => [yo yv].
rewrite  yv (opow_sum oo OS1 yo) (opowx1 oo) => pa.
have ooy: ordinalp (omega0 ^o y) by fprops.
have o1y: ordinalp (\1o +o y) by rewrite - yv.
move: (oprod2_simpl ooy o1y olt_0omega pa).
move: (opow_Mspec ole_2omega yo) => pc res1.
symmetry in res1.
case: (indecomp_pr OS1 yo (indecomp_prop4 yo) res1); rewrite /oopow => eq1.
  by move: qo; rewrite yv res1  -eq1.
by rewrite res1- {1} [omega0] (opowx1 oo) -(opow_sum oo OS1 yo) res1 -eq1 -eq1.
Qed.

Lemma ord_epsilon_p12 x: ordinalp x -> (\2o ^o x = x) -> 
  critical_ordinal \2o opow x.
Proof.
move => ox ex; case: (ord_epsilon_p11 ox ex); last by apply: ord_epsilon_p10.
move: (oleR OS_omega) olt_2omega => ha hn.
by move ->; split => // a a2 au; apply: opow_int_omega.
Qed.

Lemma ord_epsilon_p13 a x: ordinalp a -> ordinalp x -> (a ^o x = x) -> 
  ( (a <o omega0 -> ((a = \1o /\ x = \1o) \/  (\2o ^o x = x)))
  /\ (omega0 <=o a -> (epsilonp x /\ a <o x))).
Proof.
move => oa ox h.
have pa: \2o <=o a -> \2o ^o x = x.
  move => a2; apply: oleA.
    by move: (opow_Mleeq card2_nz a2 ox); rewrite h.
  by move: (opow_Mspec (oleR OS2) ox).
case: (equal_or_not x \0o) => xnz.
  by case:(proj2 olt_01); move: h; rewrite  xnz opowx0.
split => ao.
  case: (ord2_trichotomy oa) => az.
  - by move: h; rewrite az opow0x => h0; case: xnz.
  - by left;split => //; rewrite -h az opow1x.
  - by right; apply: pa.  
have a2:=(oleT (ole_2omega) ao).
have h1:= (pa a2).
have x2 : \1o <o x.
  split; first by apply:oge1.
  move => x1; move: h1; rewrite - x1 (opowx1 OS2); exact (nesym(proj2 olt_12)).
move: (opow_Meqlt a2 x2); rewrite (opowx1 oa) h => ax.
move: (proj2(ole_ltT ao ax)) => xo.
split; last by exact.
case:(ord_epsilon_p11 ox h1); [ by move => xno; case: xo | exact].
Qed.


Lemma pow_fix_enumeration1 a: \2o <=o a -> a <o omega0 ->
  forall x, ordinalp x -> first_derivation (opow a) x =
    Yo (x = \0o) omega0 (epsilon_fam (x -o \1o)).
Proof.
move => age2 ao.
have npa:= (opow_normal age2).
have npb:= oopow_normal.
have pa := (iclosed_fixpoints npa).
have na :=(ordinals_col_p2 pa).
have oa:= proj31_1 ao.
move: OS_omega => oo.
have aux: forall x, ordinalp x -> a ^o x = x -> x = omega0 \/ epsilonp x.
  move => x ox h; apply: (ord_epsilon_p11 ox).
  move: (proj1 (ord_epsilon_p13 oa ox h)) => h1; case: (h1  ao); last by exact.
  by move=> [a1 _]; case :(oltNge olt_12); rewrite - a1.
have aux1 : forall x, ordinalp x -> a ^o x = x -> omega0 <=o x.
  move => x ox xv; case: (aux _ ox xv); first by move => ->; apply:(oleR oo).
  by move /ord_eps_p3 => [].
have aux2: forall x, ordinalp x -> oopow x = x -> a ^o x = x.
  move => x ox oox; move: (conj ox oox) => xox.
  have ax:= (olt_leT ao (proj1 (ord_eps_p3 xox))).
  by apply: (proj33 (ord_epsilon_p9 xox ax)).
have npc:=(first_derivation_p0 npa).
have sd0:(first_derivation (opow a) \0o) = omega0. 
  rewrite (first_derivation_p1 npa).
  move: (normal_ofs_fix npa OS0) => [sa sb sc]; apply: oleA.
    exact: (sc _ (ole0x oo) (opow_int_omega age2 ao)).
  exact: (aux1 _ (proj32 sa) sb).
apply:(normal_ofs_uniqueness (p:= fun z => (epsilon_fct (osucc z)))).
- exact: npc.
- have aa: forall x,ordinalp x -> omega0 <o epsilon_fam x.
    by move => x /epsilon_fam_pr0 /ord_eps_p3.
  move:epsilon_fam_pr5 => [sa sb].
  split.
    move => u v uv /=.
    case: (equal_or_not v \0o) => vnz; first by case: (@olt0 u); ue.
    Ytac0;Ytac uz; first by apply: aa;apply: (OS_diff OS1 (proj32_1 uv)).
    apply: sa; apply:oprec_Mlt => //; exact:(ord_ne0_pos (proj31_1 uv) uz).
  move => x lx; move: (limit_nz lx) => xnz; Ytac0.
  move: (lx) => [ox zix lxx].
  rewrite (odiff_1inf (limit_ge_omega lx)) (sb _ lx).
  have oe: forall z, inc z x -> ordinalp (epsilon_fam (z -o \1o)).
    move=> z /(Os_ordinal ox) h;apply: (ofs_sincr sa); apply: (OS_diff OS1 h).
  apply: ord_sup_1cofinal; first split.
  * move => s /funI_P [z zx ->]; apply /funI_P.
    have oz:= Os_ordinal ox zx.
     case: (oleT_el OS_omega oz) => czo.
       exists z => //; rewrite (odiff_1inf czo); Ytac zz; last by exact.
      by case: (oltNge olt_0omega); rewrite - zz.
     exists (osucc z); first by apply: lxx.
     move: (@osucc_nz z) => zz; Ytac0; case: (ozero_dichot oz) => zz1.
       by rewrite zz1  osucc_zero (odiff_wrong (oleR OS1)). 
     by rewrite (oprec_nat2 zz1 czo) - (oprec_nat zz1 czo).
  * move => s /funI_P [z zx ->]; Ytac zp.
      exists (epsilon_fam \0o); first by apply/funI_P; ex_tac; ue.
      exact: (proj1 (aa _ OS0)).
    move: (oleR (oe _ zx)) => l1.
    have ssx: inc (z -o \1o) x. 
      move: (odiff_Mle OS1 (Os_ordinal ox zx)) => h1.
      by move/(oltP ox): zx => h;apply/(oltP ox); apply: (ole_ltT h1 h).
    exists (epsilon_fam (z -o \1o)) => //; apply/funI_P; ex_tac.
  * move => s /funI_P [z za ->]; Ytac zz;[ exact | by apply: oe].
- move => x ox; rewrite (first_derivation_p3 npa ox) /epsilon_fct.
  move: (sincr_incr (proj1 npc) (ole0x ox)); rewrite sd0.
  move /oltSleP; set t := osucc _ => oot.
  have ot:= proj32_1 oot.
  move: (normal_ofs_fix npa ot) (normal_ofs_fix npb ot).
  move => [sa sb sc][sd se sf]; apply: oleA.
     apply: (sc _ sd); apply: (aux2 _ (proj32 sd) se).
  apply: (sf _ sa) ; case: (aux _ (proj32 sa) sb); last by move => [].
  move => e1; rewrite e1 in sa; case:(oltNge oot sa).
- move => x ox; move: (@osucc_nz x)=> snz; Ytac0.
  case: (oleT_el oo ox) => cox.
    rewrite (odiff_1inf cox). 
    rewrite (odiff_1inf (oleT cox (proj1(oltS ox)))).
    Ytac xz; first by move: olt_0omega; rewrite - xz => /(oleNgt cox).
    by apply:epsilon_fam_pr4.
  case: (ozero_dichot ox) => xz.
    Ytac0; rewrite xz osucc_zero (odiff_wrong (oleR OS1)). 
    apply: epsilon_fam_pr2''.
  move: (xz) => [_ xnz]; Ytac0; rewrite (oprec_nat2 xz cox).
  by apply: epsilon_fam_pr4; apply: (OS_diff OS1 ox).
- Ytac0; exact sd0.
Qed.

Definition inverse_epsilon := 
   ordinalr (fun x y => [/\ epsilonp x, epsilonp y & x <=o y]). 

Lemma inverse_epsilon_pr x (y := inverse_epsilon x):
  epsilonp x -> (ordinalp y /\ epsilon_fam y = x).
Proof. by apply:ordinalrsP => t []. Qed.

Lemma least_critical_pow a (b := inverse_epsilon (epsilon_fct (osucc a))):
  omega0 <=o a -> least_fixedpoint_ge (opow a) \0o (epsilon_fam b).
Proof.
move => ooa.
have oa:= (OS_succ (proj32 ooa)).
move:(epsilon_fct_pr1 oa) => oeea; move:(oeea) => [ooeea _].
move: (inverse_epsilon_pr oeea); rewrite -/b; move => [ob eb].
move:(epsilon_fct_pr0 oa); rewrite eb; move => [sa sb sc].
have a2:= (oleT (ole_2omega) ooa).
split; first by apply:(ole0x ooeea).
  have lt1: a <o epsilon_fct (osucc a) by apply /oleSltP.
  by move: (ord_epsilon_p9 oeea lt1)=> [_ _]; apply.
move => z zp h;  move: (ord_epsilon_p13 (proj32 ooa) (proj32 zp) h) => [_ h1].
by move: (h1 ooa) => [[_ ta] tb]; apply: sc => //; apply /oleSltP.
Qed.

Lemma pow_fix_enumeration2 a (b := inverse_epsilon (epsilon_fct (osucc a))):
   omega0 <=o a ->
  forall x, ordinalp x -> first_derivation (opow a) x =
     (epsilon_fam (b +o x)).
Proof.
move => ao.
have age2:= (oleT ole_2omega ao).
move: (least_critical_pow ao); rewrite -/b; move => bp.
have oa:=proj32 ao.
move:(inverse_epsilon_pr (epsilon_fct_pr1 (OS_succ oa))). 
rewrite -/b; move => [ob eb].
have npa:= (opow_normal age2).
have npb:= oopow_normal.
have npc:= (first_derivation_p0 npa).
move:(ordinals_col_p2 (iclosed_fixpoints npa)) => na. 
move: OS_omega => oo.
have aux2: forall x, a <o x -> omega0 ^o x = x -> a ^o x = x.
  move => x ax oox; move:  (conj (proj32 (proj1 ax)) oox) => xox.
  by move:(ord_epsilon_p9 xox ax)  => [_ _]; apply.
have aux0: the_least_fixedpoint_ge [eta opow a] \0o = epsilon_fam b.
  move: (normal_ofs_fix npa OS0) => [sa sb sc].
  move: bp => [sa' sb' sc'].
  apply: oleA; [by apply:sc | by apply:sc'].
apply:(normal_ofs_uniqueness (p:= fun z => (epsilon_fct (osucc z)))).
- exact: npc.
- exact: (normal_ofs_compose epsilon_fam_pr5 (osum_normal ob)).
- move => x ox; rewrite (first_derivation_p3 npa ox) /epsilon_fct.
  have hh:= (ole0x ox).
  move: (sincr_incr (proj1 npc) hh) => /oltSleP.
  rewrite (first_derivation_p1 npa) aux0.
  set t := osucc _; rewrite eb  => sa1.
  move:(epsilon_fct_pr0 (OS_succ oa)); move => [sa2 _ _].
  move: (ole_ltT sa2 sa1) => [] /oleSltP lat _.
  have ot:=proj32_1 lat.
  move: (normal_ofs_fix npa ot) (normal_ofs_fix npb ot).
  move => [sa sb sc][sd se sf]; apply: oleA.
     apply: (sc _ sd); apply: (aux2 _ _ se); apply:(olt_leT lat  sd).
  apply: (sf _ sa).
  move: (ord_epsilon_p13 oa (proj32 sa) sb) => [_ h1].
  move: (h1 ao) => [[_ h2] _]; exact h2.
- move => x ox; rewrite - (osum2_succ ob ox); apply: epsilon_fam_pr4; fprops.
- rewrite (osum0r ob) - aux0 (first_derivation_p1 npa); reflexivity.
Qed.

Lemma all_der_sum_aux c (f:= osum2 c)
   (b:= fun x i => cnext (card_max (omax c x) i)):
  ordinalp c ->  normal_ofs f /\ all_der_bound f b.
Proof.
move => oc; split; first by apply:osum_normal.
move => x i ox oi.
have om:= (OS_omax oc ox).
move: (omax_p3 om oi); rewrite -/(card_max _ _) -/(b x i).
move => [sa sb sc]. 
have ec: exists2 C, infinite_c C & b x i = cnext C.
  by exists (card_max (omax c x) i). 
move:(omax_p1 oc ox) => [sd se].
have ha: ordinalp (b x i) by exact: (proj1 (CS_cnext (proj1 sa))). 
move/(oltP ha): sb  => sf.
have pa: inc x (b x i) by  apply /(oltP ha); apply: (ole_ltT se sf).
have pb: inc c (b x i) by  apply /(oltP ha); apply: (ole_ltT sd sf).
have pc: forall y, inc y (b x i) -> inc (c +o y) (b x i).
    move => y ye;apply: cnext_sum => //.
split => //.
Qed.

Lemma all_der_prod_aux c (f:= oprod2 c)
   (b:= fun x i => cnext (card_max (omax c x) i)):
  \0o <o c ->  normal_ofs f /\ all_der_bound f b.
Proof.
move => cp; split; first by apply:oprod_normal.
move => x i ox oi.
have oc:= (proj32_1 cp).
have om:= (OS_omax oc ox).
move: (omax_p3 om oi); rewrite -/(card_max _ _) -/(b x i).
move => [sa sb sc]. 
have ec: exists2 C, infinite_c C & b x i = cnext C.
  by exists (card_max (omax c x) i). 
move:(omax_p1 oc ox) => [sd se].
have ha:= (proj1 (CS_cnext (proj1 sa))). 
move/(oltP ha): sb  => sf.
have pa: inc x (b x i) by apply /(oltP ha); apply:(ole_ltT se sf).
have pb: inc c (b x i) by apply /(oltP ha); apply:(ole_ltT sd sf).
have pc: forall y, inc y (b x i) -> inc (c *o y) (b x i).
    move => y ye;apply: cnext_prod => //.
done.
Qed.

Lemma all_der_pow_aux
   (b:= fun x i => cnext (card_max x i)):
  normal_ofs oopow /\ all_der_bound oopow b.
Proof.
split; first by exact: oopow_normal.
move => x i ox oi.
move: (omax_p3 ox oi) => [sa sb sc]; split => //.
  by exists  (card_max x i).
move => t tb; apply/cnext_pow => //.
apply/(cnextP (proj1 sa)); split; fprops.
apply:ocle1 (proj2 (omax_p1 (OS_omax ox oi) OS_omega)).
Qed.

Lemma all_der_sum c x i (f:= osum2 c)
   (b:= fun x i => cnext (card_max (omax c x) i)):
  ordinalp c ->  ordinalp x -> ordinalp i  ->
  all_der f b x i = c *o omega0 ^o i +o x.
Proof.
move => oc ox oi0.
move: (all_der_sum_aux oc); rewrite -/b; move => [ha hb].
pose p i := forall x, ordinalp x -> all_der f b x i = c *o omega0 ^o i +o x.
move: x ox; rename i into i0.
apply: (least_ordinal2 (p := p)) oi0 => y oy etc.
case: (ordinal_limA oy) => ly.
    move => x ox; rewrite ly (all_der_p2 ha hb ox) opowx0 oprod1r//.
  move:ly => [i oi si].
  move => x ox.
  have liy: i <o y by rewrite si;apply:oltS.
  have na: normal_ofs ((all_der f b)^~ i) by apply: all_der_p6.
  move:(first_derivation_exten  (etc _ liy) na) => eq1.
  move:(all_der_p14 ha hb oi ox); rewrite - si => <- /=.
  have oo1:= (OS_pow OS_omega oi).
  have oo:=(OS_prod2 oc oo1).
  rewrite (eq1 x ox) (add_fix_enumeration oo ox) si (opow_succ OS_omega oi).
  by rewrite (oprodA oc oo1 OS_omega).
have nf:= (all_der_p6 ha hb oy).
have ooy := (OS_pow OS_omega oy).
have ov := OS_prod2 oc ooy.
have ng:= (osum_normal ov).
apply:(sincr_ofs_exten  (proj1 nf) (proj1 ng)) => x ox.
  set g :=  all_der (osum2 c) b.
  set s := g x y.
  have os: ordinalp s by apply:(OS_all_der ha hb).
  case (ozero_dichot oc) => cp.
    by exists s => //;rewrite cp oprod0l (osum0l os).
  move:(normal_ofs_compose (oprod_normal cp) oopow_normal).
  move => [sa sb]; move: (sb y ly) => /=.
  set F := fun_image _ _.
  have osF: (ordinal_set F).
    move => t /funI_P [i iy ->]; apply:(ofs_sincr sa (Os_ordinal oy iy)).
  have ub: ordinal_ub F s.
    move => t tF; move:(osF _ tF); move /funI_P: tF => [i iy ->] ot.
    have liy: i <o y by apply/(oltP oy).
    move:(all_der_p7 ha hb ox liy).
    by rewrite (etc _ liy s os) -/g -/s; move => <-;apply: osum_Mle0. 
  move:(ord_ub_sup os ub) => pa pb; rewrite - pb in pa.
  by move:(odiff_pr pa) => [ra rb]; exists (s -o c *o omega0 ^o y).
set g :=  all_der (osum2 c) b.
set a := c *o omega0 ^o y +o x.
have yp: \0o <o y by move/limit_ordinal_P:ly => [p2 p3].
have osa:=(OS_sum2 ov ox).
have hc: (forall i, i <o y ->  all_der (osum2 c) b a i = a). 
  move => i iy; rewrite (etc _ iy a osa).
  have oi:= proj31_1 iy.
  have ooi := (OS_pow OS_omega oi).
  have ow := OS_prod2 oc ooi.
  by rewrite /a (osumA ow ov ox) - (oprodD ooi ooy oc) (ord_negl_p4 iy).
by move:(all_der_p8 ha hb osa yp hc) => [u ua ub]; exists u.
Qed.

Lemma all_der_ident x i (f:= @id Set)
   (b:= fun x i => cnext (card_max x i)):
  ordinalp x -> ordinalp i -> all_der f b x i = x.
Proof.
set f1:= osum2 \0o.
set b1 := fun x i => cnext (card_max (omax \0o x) i).
have ha: forall x i, ordinalp x -> ordinalp i -> b1 x i = b x i.
  by rewrite /b /b1;move => x' i' ox oi; rewrite (omax_xy (ole0x ox)).
move: (all_der_sum_aux OS0); rewrite -/b1 -/f1; move => [hb hc].
have sv: f1 =1o f by move => x' ox; rewrite /f1 (osum0l ox).
have sb: all_der_bound f b.
   move => x' i' ox oi; rewrite - (ha _ _ ox oi).
   by move: (hc _ _ ox oi) => [ua ub uc ud].
move:OS0 => oz  ox oi.
rewrite - (all_der_unique hb hc sb sv ox oi) all_der_sum //.
by rewrite oprod0l (osum0l ox).
Qed.

Lemma all_der_prod c x i (f:= oprod2 c)
   (b:= fun x i => cnext (card_max (omax c x) i)):
  \0o <o c ->  ordinalp x -> ordinalp i  ->
  all_der f b x i = c ^o (omega0 ^o i) *o x.
Proof.
move => cp ox oi0.
have oc:= proj32_1 cp.
move: (all_der_prod_aux cp); rewrite -/b; move => [ha hb].
pose p i := forall x, ordinalp x -> all_der f b x i = c ^o (omega0 ^o i) *o x.
move: x ox; rename i into i0.
apply: (least_ordinal2 (p := p)) oi0 => y oy etc.
case: (ordinal_limA oy) => ly.
    move => x ox; rewrite ly (all_der_p2 ha hb ox) opowx0 opowx1 //.
  move:ly => [i oi si] x ox.
  have liy: i <o y by rewrite si;apply:oltS.
  have na: normal_ofs ((all_der f b)^~ i) by apply: all_der_p6.
  have eq1:= (first_derivation_exten  (etc _ liy) na).
  move:(all_der_p14 ha hb oi ox); rewrite - si => <- /=.
  have oo1:= (OS_pow OS_omega oi).
  have oo:= (opow_pos cp oo1).
  rewrite (eq1 x ox) (mult_fix_enumeration oo ox) si (opow_succ OS_omega oi).
  by rewrite (opow_prod oc oo1 OS_omega).
have nf:= (all_der_p6 ha hb oy).
have ooy := (OS_pow OS_omega oy).
have ov := opow_pos cp ooy.
have ng:= (oprod_normal ov).
apply:(sincr_ofs_exten  (proj1 nf) (proj1 ng)) => x ox.
  set g :=  all_der (oprod2 c) b.
  set s := g x y.
  have os: ordinalp s by exact:(OS_all_der ha hb ox oy).
  case: (ord2_trichotomy oc) => c2.
      by move: cp => [];rewrite c2.
    by exists s => //; rewrite c2 opow1x (oprod1l os).
  case: (oquoremP os ov); set q := oquo _ _; set r := orem _ _=> oq or sv rp.
  have op1:= (proj32_1 rp).
  have op2:= (OS_prod2 op1 oq).
  case: (ozero_dichot or) => snz.
    by exists q => //; rewrite sv snz (osum0r op2).
  have pc: forall i, i <o y ->  c ^o (omega0 ^o i) *o r = r.
    move => i iy.
    have oi:= proj31_1 iy.
    have ooi:= (OS_pow OS_omega oi).
    have op3 := (OS_pow oc ooi).
    move:(all_der_p7 ha hb ox iy). 
    rewrite (etc _ iy s os) -/g -/s sv (oprodD op2 or op3).
    rewrite (oprodA op3 op1 oq) - (opow_sum oc ooi ooy)  (ord_negl_p4 iy) => h.
    exact: (osum2_simpl (OS_prod2 op3 or) or op2 h).
  move:(normal_ofs_compose (opow_normal c2)  oopow_normal).
  move => [sa sb]; move: (sb y ly) => /=.
  set F := fun_image _ _.
  have osF: (ordinal_set F).
    move => t /funI_P [i /(Os_ordinal oy) iy ->]; apply:(ofs_sincr sa iy).
  have ub: ordinal_ub F r.
    move => t tF; move:(osF _ tF); move /funI_P: tF => [i iy ->] ot.
    move /(oltP oy): iy => /pc <-.
    apply: oprod_Mle1 => //.
  move => pb; case:(oltNge rp); rewrite pb; exact:(ord_ub_sup or ub). 
set g :=  all_der (oprod2 c) b.
set a := c ^o (omega0 ^o y) *o x.
have ovv:= (proj32_1 ov).
have yp: \0o <o y by move/limit_ordinal_P:ly => [p2 p3].
have osa: ordinalp a by move: (OS_prod2 ovv ox).
have hc: (forall i, i <o y ->  all_der (oprod2 c) b a i = a). 
  move => i iy; rewrite (etc _ iy a osa).
  have oi:=proj31_1 iy.
  have ooi := (OS_pow OS_omega oi).
  have ow := OS_pow oc ooi.
  by rewrite /a (oprodA ow ovv ox) -(opow_sum oc ooi ooy) (ord_negl_p4 iy).
by move:(all_der_p8 ha hb osa yp hc) => [u ua ub]; exists u.
Qed.


Lemma all_der_prod_cor c: \2o <=o c -> 
   normal_ofs (fun i => c ^o (oopow i)).
Proof.
move => cp.
move: (ord2_trichotomy1 cp) => [sa sb].
have oc:=proj32 cp.
have sc: c *o \0o = \0o by rewrite oprod0r.
have sd: c *o \1o <> \1o by rewrite (oprod1r oc).
have se:= (olt_leT olt_02 cp).
have os1:= OS1.
move: (all_der_prod_aux se)=> [ha hb].
move:(all_der_p13_ter ha hb sc sd).
apply:normal_ofs_from_exten => x ox; rewrite all_der_prod // oprod1r;fprops.
Qed.

Definition Sphi x y :=
  all_der oopow (fun x i => cnext (card_max x i)) y x.

Lemma OS_Sphi x y: ordinalp x -> ordinalp y ->
  ordinalp (Sphi x y).
Proof.
move: (all_der_pow_aux) => [ha hb] ox oy.
exact: (OS_all_der ha hb oy ox).
Qed.

Lemma Sphi_bounded C (E :=cnext C) x y:
   infinite_c C -> inc x E -> inc y E -> inc (Sphi y x) E.
Proof.  
move => ic xe ye.
have [ha hb]:= (all_der_pow_aux).
have oE:= (proj1 (CS_cnext (proj1 ic))).
have ox:= Os_ordinal oE xe.
have oy:= Os_ordinal oE ye.
have h: card_max x y <=c C.
  rewrite /card_max /omax/Gmax; Ytac pa; last Ytac pb.
  + by rewrite cardinal_Nat; apply/infinite_c_P2.
  + by move/(cnextP (proj1 ic)): ye => [].
  + by move/(cnextP (proj1 ic)): xe => [].
move: (omax_p2 (OS_omax ox oy)) => []; rewrite -/(card_max x y) -/C1 => sa _.
move: (proj1 (CS_cnext (proj1 sa))) => oF.
have sc: sub (cnext (card_max x y)) E.
  move => t /(cnextP (proj1 sa)) [sa' sb]; apply/(cnextP (proj1 ic)). 
  split => //; exact: (cleT sb h).
by move:(all_der_p3 ha hb ox oy) => /sc.
Qed.

Lemma Sphi_countable x y:
    countable_ordinal x -> countable_ordinal y ->
    countable_ordinal (Sphi x y).
Proof.
move => /aleph_oneP xa /aleph_oneP ya; apply/aleph_oneP.
by apply:Sphi_bounded => //; apply: CIS_omega.
Qed.

Lemma Sphi_p0 x: ordinalp x ->  Sphi \0o x = oopow x.
Proof.
move: (all_der_pow_aux) => [ha hb].
move => ox; exact: (all_der_p2 ha hb ox).
Qed.


Lemma Sphi_p1 x: ordinalp x -> normal_ofs (Sphi x).
Proof.
move: (all_der_pow_aux) => [ha hb].
move => ox; exact: (all_der_p6 ha hb ox).
Qed.

Lemma Sphi_p2 x: ordinalp x ->
  first_derivation (Sphi x) =1o (Sphi (osucc x)). 
Proof.
move: (all_der_pow_aux) => [ha hb].
move => ox; exact: (all_der_p14 ha hb ox).
Qed.

Lemma Sphi_p3  x i j: ordinalp x -> i <o j ->
   Sphi i (Sphi j x) = Sphi j x.
Proof.
move: (all_der_pow_aux) => [ha hb] ox ij.
exact: (all_der_p7 ha hb ox ij).
Qed.

Lemma Sphi_p4 y j: ordinalp y -> \0o <o j ->
   (forall i, i <o j ->  Sphi i y = y) ->
   (exists2 x, ordinalp x & y = Sphi j x).
Proof.
move: (all_der_pow_aux) => [ha hb] oy jp h.
exact:(all_der_p8 ha hb oy jp h).
Qed.

Lemma Sphi_p5 : normal_ofs (Sphi ^~ \0o).
Proof.
move: (all_der_pow_aux) => [ha hb]. 
have hc: omega0 ^o \0o <> \0o by apply: oopow_nz; fprops.
exact:(all_der_p13 ha hb hc).
Qed.

Lemma Sphi_p6 x y i j: 
  ordinalp x -> ordinalp y -> ordinalp i -> ordinalp j ->
  (Sphi i x = Sphi j y <->
   [/\ i <o j -> x = Sphi j y, 
       i = j -> x = y & 
      j <o i -> y = Sphi i x]).
Proof.
move: (all_der_pow_aux) => [ha hb] ox oy oi oj.
exact: (all_der_p9 ha hb ox oy oi oj ).
Qed.

Lemma Sphi_p7 x y i j: 
  ordinalp x -> ordinalp y -> ordinalp i -> ordinalp j ->
  (Sphi i x <o Sphi j y <->
   [/\ i <o j -> x <o Sphi j y, 
       i = j -> x <o y & 
      j <o i -> Sphi i x <o y]).
Proof.
move: (all_der_pow_aux) => [ha hb] ox oy oi oj.
exact: (all_der_p10 ha hb ox oy oi oj ).
Qed.


Lemma Sphi_p8 x y i j: 
  ordinalp x -> ordinalp y -> ordinalp i -> ordinalp j ->
  (Sphi i x <=o Sphi j y <->
   [/\ i <o j -> x <=o Sphi j y, 
       i = j -> x <=o y & 
      j <o i -> Sphi i x <=o y]).
Proof.
move: (all_der_pow_aux) => [ha hb] ox oy oi oj.
exact: (all_der_p10' ha hb ox oy oi oj ).
Qed.




Definition Schutte_Cr a b := exists2 x, ordinalp x & b = Sphi a x.

Lemma Schutte_Cr_p1 a: ordinalp a ->
  iclosed_proper (Schutte_Cr a).
Proof.
move => oa; move: (Sphi_p1 oa) => sa.
by apply: iclosed_normal_ofs.
Qed.

Lemma Schutte_Cr_p2 a: ordinalp a ->
   ordinalsf (Schutte_Cr a) =1o Sphi a.
Proof.
move => oa.
have sa :=(Schutte_Cr_p1 oa).
have sc := (ordinals_col_p2 sa).
have sd := (Sphi_p1 oa).
move: (ordinals_col_p1 (proj1 (proj1 sa)) (proj2 sa)) => [ha hb _ _ _].
apply: (sincr_ofs_exten  (proj1 sc) (proj1 sd)) => x ox.
  exact (ha _ ox).
by apply: hb;  exists x.
Qed.

Lemma Schutte_Cr_p3 b: ordinalp b -> 
  (Schutte_Cr \0o b <-> indecomposable b).
Proof.
move => ob; split.
  by move => [x ox ->]; rewrite (Sphi_p0 ox); apply:indecomp_prop4.
move /indecomp_prop3 => [y oy ->]; rewrite - (Sphi_p0 oy).
by exists y.
Qed.

Lemma Schutte_Cr_p4 a b: \0o <o a -> ordinalp b -> 
  (Schutte_Cr a b <-> (forall c, c <o a -> Sphi c b = b)).
Proof.
move => ap ob; split.
   by move => [x ox ->] c ca; apply: Sphi_p3.
by move /(Sphi_p4 ob ap).
Qed.

Lemma Schutte_Cr_p5 a b: limit_ordinal a -> ordinalp b -> 
  (Schutte_Cr a b <-> (forall c, c <o a -> Schutte_Cr c b)).
Proof.
move => ap ob; split.
   move => [x ox ->] c ca; exists (Sphi a x).
     apply: (OS_Sphi (proj32_1 ca) ox).
  by symmetry; apply: Sphi_p3.
move /limit_ordinal_P: ap => [sa sb sc].
apply:Sphi_p4 => //.
move => i ia; move:(sc _ (sb _ ia)) => [x ox xv].
move:(Sphi_p3 ox (oltS (proj31_1 ia))).
by rewrite - xv.
Qed.

Lemma Schutte_Cr_p6 a b: ordinalp a -> ordinalp b -> 
  (Schutte_Cr (osucc a) b <-> Sphi a b = b).
Proof.
move => oa ob.
have osa := OS_succ oa.
have sa: \0o <o osucc a by apply: ord_ne0_pos => //;apply: osucc_nz.
have asa:= (oltS oa).
split; first by move/(Schutte_Cr_p4 sa ob) => h; exact: (h a asa).
move => aux.
apply/(Schutte_Cr_p4 sa ob) => c /oltSleP ca.
case: (equal_or_not c a) => eca; first by rewrite eca.
by rewrite - aux; apply: Sphi_p3.
Qed.

Lemma Schutte_Cr_p7 a a' b:  a <=o a' -> ordinalp b -> 
   Schutte_Cr a' b ->  Schutte_Cr a b.
Proof.
move => aa ob pa.
case: (equal_or_not a a') => h; first by rewrite  h.
move: pa => [x ox ->]; exists (Sphi a' x)  => //.
  apply: (OS_Sphi (proj32 aa) ox).
by symmetry; apply:Sphi_p3.
Qed.

Lemma Schutte_Cr_p8 a  b: ordinalp a  -> ordinalp b -> 
   Schutte_Cr a b -> indecomposable b.
Proof.
move => oa ob h.
have ap:= ole0x oa.
by move: (Schutte_Cr_p7 ap ob h); move /(Schutte_Cr_p3 ob).
Qed.
  
Lemma Schutte_Cr_p8' a b: ordinalp a  -> ordinalp b -> 
  indecomposable (Sphi a b).
Proof. 
by move => oa ob; apply (Schutte_Cr_p8 oa (OS_Sphi oa ob)); exists b.
Qed.

Lemma Sphi_p9 x: ordinalp x ->  x <=o Sphi x \0o.
Proof.
move => ox; move: (Sphi_p5) => h; exact:(osi_gex (proj1 h) ox).
Qed.

Lemma Schutte_Cr_p9 x y: ordinalp x -> ordinalp y ->  Schutte_Cr x y ->
   x <=o y.
Proof.
move => ox oy [z oz ->]. 
move: (Sphi_p9 ox) => h.
case (ozero_dichot oz) => eq; first by rewrite eq.
by move: (proj1 (Sphi_p1 ox) _ _ eq) => [/(oleT h) le _].
Qed.


Lemma Sphi_p10a a b a' b' x: 
   ordinalp a -> b <o x -> x = Sphi a b ->
   ordinalp a' -> b' <o x -> x = Sphi a' b' ->
   (a = a' /\ b = b').
Proof.
move => oa p2 p3 oa' q2 q3.
rewrite p3 in q3.
move/ (Sphi_p6 (proj31_1 p2) (proj31_1 q2) oa oa'): (q3).
move => [sa sb sc].
case: (oleT_ell oa oa') => h; first by split => //; apply: sb.
  by move: (sa h) p2; rewrite - q3 - p3 => ->; move => [].
by move: (sc h) q2; rewrite - p3 => ->; move => [].
Qed.

Lemma Sphi_p10b x: indecomposable x -> 
  (exists a b, [/\ a <=o x, b <o x & x = Sphi a b]).
Proof.
move => ix; move: (ix) => [xp _].
have ox:= proj32_1 xp.
have sa:= (proj1 (Sphi_p1 ox) _ _ xp).
have sb:= (ole_ltT (Sphi_p9 ox) sa).
pose p a:= Sphi a x = x. 
have npa: not (p x) by move => h; move: sb => []; rewrite  h.
move: (least_ordinal3 ox npa (p := p)).
set a := least_ordinal _ x; move => [oa nn etc].
case: (oleT_el oa ox); [move => ax | by move => /etc px].
have [b ob xv]: exists2 b,  ordinalp b & x = Sphi a b.
  case: (ozero_dichot oa) => az. 
  by rewrite az;move/(Schutte_Cr_p3 ox): ix.
   apply:(Sphi_p4 ox az etc).
have ica := (proj1 (Sphi_p1 oa)).
have xaxx := (osi_gex ica ox).
have h: x <o Sphi a x by split => // eq; case nn.
exists a,b ; split => //.
case: (oleT_ell ox ob).
+ by move => eq; move: (proj2 h); rewrite {2} eq.
+ by move => xb; case: (oltNge h); move: (proj1(ica _ _ xb)); rewrite - xv. 
+ done.
Qed.

Definition strong_critical x :=  Schutte_Cr x x.

Lemma strong_criticalP x: ordinalp x ->
  (strong_critical x  <-> Sphi x \0o = x).
Proof.
move => ox;split; last by move => h; exists \0o; fprops.
move => [y oy yb]; move: (Sphi_p9 ox); rewrite {1} yb => h.
case: (ozero_dichot oy); first by move => <-.
by move / (proj1 (Sphi_p1 ox)) => /(oleNgt h).
Qed.

Lemma strong_critical_closed_proper:
  iclosed_proper (fun z => ordinalp z /\ strong_critical z).
Proof.
move: Sphi_p5;set f := (Sphi^~ \0o) => nf.
move: (iclosed_fixpoints nf) => [[pa pb] pc].
have aux z: (ordinalp z /\ strong_critical z) <->  (ordinalp z /\ f z = z).
   split. 
     by move => [oz] /(strong_criticalP oz).
   by move => [oz] /(strong_criticalP oz). 
split => //; first split.
+ by move => x [].
+ by move => g pF nef; apply /aux; apply: pb => // x/pF => /aux w.
+ by move => [E ev]; case:pc; exists E => x; split; [move/ev/aux| move/aux/ev].
Qed.

Definition Gamma_0 := the_least_fixedpoint_ge (Sphi ^~ \0o) \0o.

Lemma Gamma0_p :
   Sphi Gamma_0 \0o = Gamma_0 /\
   forall x, ordinalp x -> Sphi x \0o = x -> Gamma_0 <=o x.
Proof.
move: (normal_ofs_fix Sphi_p5 OS0); rewrite -/Gamma_0.
by move => [sa sb sc]; split => // x ox; apply: sc; apply:ole0x.
Qed.

Lemma countable_Gamma_0: countable_ordinal Gamma_0.
Proof.
have sa:= CIS_omega.
have sb:= Sphi_p5.
have sc:= (cnext_zero sa).
have sd: (forall x, inc x aleph_one -> inc ((Sphi^~ \0o) x) aleph_one).
  by move => x xa; apply:Sphi_bounded. 
by move /aleph_oneP: (next_fix_point_small sa sb sd sc). 
Qed.

Lemma OS_Gamma_0: ordinalp Gamma_0.
Proof. exact: (proj1 countable_Gamma_0). Qed.


Lemma Gamma0_s x y: x <o Gamma_0 -> y <o Gamma_0 -> Sphi x y <o Gamma_0.
Proof.
move => sa sb.
have [sc sd]:= Gamma0_p.
have ox := (proj31_1 sa).
have oy:= (proj31_1 sb).
have og :=(proj32_1 sb).
rewrite - sc.
apply/(Sphi_p7 oy OS0 ox og); split.
+ by rewrite sc.
+ by move: (proj2 sa).
+ by move => [/(oltNge sa)].
Qed.

Lemma Gamma0_limit: limit_ordinal Gamma_0.
Proof.
have h:= (proj1 Gamma0_p). 
have og:= OS_Gamma_0.
case:(indecomp_limit (Schutte_Cr_p8' og OS0)); rewrite  h// => h2.
move: h; rewrite h2 => h3.
move: (Sphi_p3 OS0 (olt_01)). 
rewrite h3 (Sphi_p0 OS1) oopow1 => <-; exact omega_limit.
Qed.

Lemma Gamma0_epsilon: oopow Gamma_0 = Gamma_0.
Proof.
have [g1 g2] := Gamma0_p.
have sa := (limit_pos (Gamma0_limit)).
by move: (Sphi_p3 OS0 sa); rewrite g1 (Sphi_p0 (proj32_1 sa)).
Qed.

Definition Szeta := 
   induction_term (fun (n:Set) v => Sphi v \0o) \1o.

Lemma Szeta_0: Szeta \0c = \1o.
Proof. exact: induction_term0. Qed.

Lemma Szeta_1: Szeta \0c = Sphi \0o \0o.
Proof. by rewrite Szeta_0 (Sphi_p0 OS0) oopow0. Qed.

Lemma Szeta_2 n: natp n ->  Szeta (csucc n) = Sphi (Szeta n) \0o.
Proof.
apply: (induction_terms (fun (n:Set) v => Sphi v \0o) \1o).
Qed.

Lemma OS_Szeta n: natp n -> ordinalp (Szeta n). 
Proof.
move:n;apply: Nat_induction. 
  rewrite Szeta_0; fprops.
move => n nb Hrec; rewrite (Szeta_2 nb); apply:OS_Sphi; fprops.
Qed.

Lemma Szeta_3 n: natp n -> Szeta n <o Gamma_0.
Proof.
move: n; apply:Nat_induction.
  move: Gamma0_limit (olt_1omega) => /limit_ge_omega ha hb.
  rewrite Szeta_0; apply: olt_leT hb ha.
move => n nb Hrec; rewrite (Szeta_2 nb).
by rewrite -(proj1 (Gamma0_p)); move: (proj1 (Sphi_p5) _ _ Hrec).
Qed.

Lemma Szeta_4 k: natp k -> Szeta k <o Szeta (csucc k).
Proof.
move => kb; rewrite (Szeta_2 kb); move:(OS_Szeta kb) => ox.
split; first exact:(Sphi_p9 ox).
move => eq. 
case: (oleNgt (proj2 (Gamma0_p) _ ox (sym_eq eq)) (Szeta_3 kb)). 
Qed.

Lemma Szeta_5 n m: natp n -> natp m -> n <c m ->
  Szeta n <o Szeta m.
Proof.
move => nN mN nm.
have pa: forall k, natp k -> k <> \0c -> Szeta n <o Szeta (n +c k).
apply: Nat_induction => //.
  move => k kN Hrec _; rewrite (csum_nS _ kN).
  have hh:  Szeta (n +c k) <o Szeta (csucc (n +c k)).
     apply:Szeta_4; fprops.
  case (equal_or_not k \0c) => kz.
    move: hh; rewrite {1} kz csum0r //; fprops.
  exact: (ole_ltT (proj1 (Hrec kz)) hh).
rewrite - (cdiff_pr (proj1 nm)).
apply: pa; [ by apply:NS_diff | exact: (cdiff_nz nm) ].
Qed.

Lemma Szeta_6 x: ordinalp x ->
   (forall n, natp n -> Szeta n <=o x) -> Gamma_0 <=o x.
Proof.
move => ox pa.
move: (induction_defined_pr (Sphi^~ \0o) \0o).
rewrite /Gamma_0 /the_least_fixedpoint_ge.
set f := induction_defined _ _.
move => [sf sjf f0 fsn].
have f1: Vf f (csucc \0c) = Szeta \0o.
  by rewrite (fsn _ NS0) f0 - Szeta_1.
have pb: forall n, natp n -> (Vf f (csucc n)) = Szeta n.
  apply: Nat_induction => // n nN hr.
  by rewrite (fsn _ (NS_succ nN)) hr (Szeta_2 nN).
have aux: forall t, inc t (target f) -> t = \0o \/
   (exists2 n, natp n & t = Szeta n).
  move => i /(proj2 sjf) [n]; rewrite sf => nN ->.
  case (equal_or_not n \0o) => nz; [by rewrite nz f0; left | right].
  move: (cpred_pr nN nz) => [qa qb]; exists (cpred n) => //.
  by rewrite {1} qb pb.
apply:ord_ub_sup => //.
move => i /aux  [-> | [n nb ->]]; [apply:ole0x ox | apply: pa nb].
Qed.


(* direct  proof *)

Lemma Schutte_14_16' x:  x <o Gamma_0 -> 
   exists2 n, natp n & x <o Szeta n.
Proof.
move => h; ex_middle bad.
have ox:= (proj31_1 h).
have: (forall n, natp n -> Szeta n <=o x).
  move => n nN; ex_middle b; case bad; exists n => //.
  case: (oleT_el (OS_Szeta nN) ox) => //.
by move/(Szeta_6 ox) => /(oltNge h).
Qed.


(* Schutte proof: *)
Lemma Schutte_14_16 x:  x <o Gamma_0 -> 
   exists2 n, natp n & x <o Szeta n.
Proof.
move => h.
pose p x :=x <o Gamma_0 -> exists2 n, natp n & x <o Szeta n.
apply:(least_ordinal2 (p := p))  (proj31_1 h) h => y oy Hr yg.
case (ozero_dichot oy).
   move => ->; exists \0o; first by apply:NS0.
   rewrite Szeta_0; apply:olt_01.
move=> yp.
move: (omega_log_p1 yp) => [z [oz pa pb]].
move: (Sphi_p10b (indecomp_prop4 oz)) => [a [b [az bz etc]]].
move: (proj31_1 bz) (proj31 az) => ob oa.
have gp:=(proj2 Gamma0_p).
have ag0:= (ole_ltT (oleT az pa) yg).
have bg0:=(ole_ltT (oleT (proj1 bz) pa) yg).
have az': a <o oopow z.
  split => //; rewrite etc => e1.
  case (ozero_dichot ob) => bez.
     have eq2: Sphi a \0o = a by rewrite - bez.
     exact: (oltNge ag0 (gp _ oa eq2)).
  move: (proj1 (Sphi_p1 oa) _ _ bez); rewrite - e1 => ga.
  case: (oltNge ga (osi_gex (proj1(Sphi_p5)) oa)).
have lby:= (olt_leT bz pa).
have lay:= (olt_leT az' pa).
move: (Hr _ lby bg0)  (Hr _ lay ag0)=> [n nN nb] [m mN ma].
set nm :=cmax n m. 
have nmN: natp nm by apply:Gmax_E.
have laS: a <o Szeta nm.
  rewrite /nm/cmax/Gmax; Ytac w => //.
  case: (cleT_el (CS_nat nN) (CS_nat mN)) => // lmn.
  exact: (olt_ltT ma (Szeta_5 mN nN lmn)). 
have lbS: b <o Szeta nm.
  rewrite /nm/cmax/Gmax; Ytac w => //; case (equal_or_not n m) => ee; try ue.
  exact: (olt_ltT nb (Szeta_5 nN mN (conj w ee))).
have lt1: oopow z <o Szeta (csucc nm).
  rewrite etc (Szeta_2 nmN).
  apply/(Sphi_p7 ob OS0 oa (proj32_1 laS)); split.
  +  move: (Szeta_4 nmN); rewrite (Szeta_2 nmN).
     move => sa sb; exact: olt_ltT lbS sa.
  + by move => e1; move: (proj2 laS); rewrite - e1.
  + by move => [/(oltNge laS) e1 _].
exists (csucc nm); first by apply:NS_succ.
have [u ou uv]: exists2 u, ordinalp u & Szeta (csucc nm) = omega0 ^o u.
  move: (proj32_1 laS) OS0 => o1 o2.
  by apply: indecomp_prop3;rewrite (Szeta_2 nmN); apply:Schutte_Cr_p8'. 
move: lt1; rewrite uv => hb.
case: (oleT_el ou oz); first by move/opow_Mo_le => ha; case: (oleNgt ha hb).
by move/(oleSltP) => /opow_Mo_le;apply: olt_leT.
Qed.


Definition maximal_critical a x :=
   Schutte_Cr a x /\ forall a', a <o a' -> ~ Schutte_Cr a' x. 

Lemma maximal_criticalP a x: ordinalp a -> ordinalp x ->
  (maximal_critical a x <-> exists2 b, b<o x & x = Sphi a b).
Proof.
move => oa ox; split.
   move=> [[c oc cv] pb]; exists c => //.
   have ica:= (proj1 (Sphi_p1 oa)).
   move:(osi_gex ica oc); rewrite - cv => cx; split => // ecx.
   rewrite ecx in cv.
   by case:(pb _ (oltS oa)); apply/(Schutte_Cr_p6 oa ox).
move => [b bx bv]; split; first by exists b => //; exact (proj31_1 bx).
move => c ac [d od dv].
rewrite dv in bv.
move/(Sphi_p6 od (proj31_1 bx) (proj32_1 ac) oa): bv.
by move => [_ _ h]; move: (h ac) (proj2 bx); rewrite - dv.
Qed.

Lemma maximal_critical_p1 x: indecomposable x ->
  exists2 a, ordinalp a & maximal_critical a x.
Proof.
move => ix; move: (Sphi_p10b ix) => [a [b [pa pb pc]]].
have oa:=proj31 pa.
by exists a => //; apply/(maximal_criticalP oa (proj32 pa)); exists b.
Qed.

Definition Spsi_aux a b := 
  exists n c, [/\ n <o omega0, ordinalp c, b = c +o n & Sphi a c = c].
Definition Spsi a b :=
  Sphi a (Yo (Spsi_aux a b)  (osucc b) b).

Lemma OS_Spsi a b: ordinalp a -> ordinalp b ->  ordinalp (Spsi a b).
Proof.
move => oa ob; apply: (OS_Sphi oa); Ytac h;fprops.
Qed.

Lemma Spsi_p0 a: ordinalp a ->  Spsi a \0o = Sphi a \0o.
Proof.
move => oa; rewrite /Spsi; Ytac h => //.
move: h => [n [c [on oc eq1]]].
move: (osum2_zero oc (proj31_1 on) (sym_eq eq1)) => [-> _] eq2.
by move:(proj2(proj1 (Schutte_Cr_p8' oa OS0))); rewrite eq2.
Qed.

Lemma Gamma0_s_psi a b: a <o Gamma_0  -> b <o Gamma_0 ->
  Spsi a b <o Gamma_0.
Proof.
move => pa pb; rewrite /Spsi; Ytac h; apply:Gamma0_s => //.
by move /limit_ordinal_P: Gamma0_limit => [_ ]; apply.
Qed.

Lemma Spsi_p1 a b b':
  ordinalp a -> ordinalp b -> ordinalp b' ->  
  (Spsi a b = Sphi a b') -> b' <o Sphi a b'.
Proof.
move => oa ob ob'; rewrite /Spsi => sa.
have ica:= (proj1 (Sphi_p1 oa)).
have pa:= (osi_gex ica ob).
have oy: ordinalp (Yo (Spsi_aux a b) (osucc b) b) by Ytac h; fprops.
move/(Sphi_p6 oy ob' oa oa): sa => [_ h _]; move: (h (erefl a)).
Ytac h0 => eq2.
  move:(ole_ltT pa (ica _ _ (oltS ob)));rewrite -{1} eq2 {1} eq2.
  case:(indecomp_limit (Schutte_Cr_p8' oa ob')).
    move => -> /olt1 bz.
    move: h0 => [n [c [qa qb qc]]].
    have cnz: c +o n = \0o by rewrite - bz.
    move: (osum2_zero qb (proj31_1 qa) cnz) => [-> _] e2.
    by move: (Schutte_Cr_p8' oa OS0) => [] []; rewrite e2 => _; case.
  move => /limit_ordinal_P [_]; apply.
rewrite - eq2;split => // eq1; case h0; exists \0o, b; rewrite (osum0r ob).
split => //;exact:olt_0omega.
Qed.

Lemma Spsi_p1' a b (b' := (Yo (Spsi_aux a b)  (osucc b) b)):
  ordinalp a -> ordinalp b -> b' <o Sphi a b'.
Proof.
move => oa ob.
have ob':ordinalp b' by  rewrite /b'; Ytac h; fprops.
by apply: (Spsi_p1 oa ob ob').
Qed.

Lemma Spsi_p2 a b: ordinalp a -> ordinalp b ->   b <o Spsi a b.
Proof.
move => oa ob.
move: (Spsi_p1' oa ob).
rewrite /Spsi; set c := Yo _ _ _ => e1.
suff bc : b <=o c by apply:(ole_ltT bc e1).
rewrite /c; Ytac h; [ apply: (proj1(oltS ob)) | fprops].
Qed.

Lemma Spsi_p3 a b b':
  ordinalp a -> b <o b' -> (Spsi a b <o Spsi a b').
Proof.
move => oa bb'; rewrite /Spsi.
have sbb: osucc b <o osucc b' by move /oltSSP: bb'.
apply: (proj1 (Sphi_p1 oa)).
Ytac pa; Ytac pb => //.
  split; first by  move/oleSltP: bb'.
  move => h; move: pa => [n [c [qa qb qc qd]]]; case: pb.
  exists (osucc n), c; split => //.
     by move: omega_limit => /limit_ordinal_P [_]; apply.
  rewrite -h qc osum2_succ //; exact (proj31_1 qa).
exact:(olt_ltT bb' (oltS (proj32_1 bb'))). 
Qed.

Lemma Spsi_p4 a a' b b':
  ordinalp a -> ordinalp a' -> ordinalp b -> ordinalp b' ->
  (Spsi a b = Spsi a' b') ->
  (a = a' /\ b = b').
Proof.
move=> oa oa' ob ob' eq.
move: (Spsi_p1' oa ob); set c := Yo _ _ _.
move: (Spsi_p1' oa' ob'); set c' := Yo _ _ _.
move => sa sb.
move /(Sphi_p6 (proj31_1 sb) (proj31_1 sa) oa oa') : (eq).
move => [qa qb qc].
have eq0:Sphi a c = Sphi a' c' by [].
case: (oleT_ell oa oa') => h.
+ case: (oleT_ell ob ob') => h'; first by split.
   move:(Spsi_p3  oa h') => [_]; rewrite eq h; case; reflexivity.
  move:(Spsi_p3  oa h') => [_]; rewrite eq h;case; reflexivity.
+ by move: (qa h); move: sb => [_ hu]; rewrite - eq0 => hv; case: hu.
+ by move: (qc h); move: sa => [_ hu]; rewrite  eq0 => hv; case: hu.
Qed.


Lemma Spsi_p5 a b: ordinalp a -> ordinalp b ->
  (a <o Spsi a b <-> ~ (strong_critical (Spsi a b))).
Proof.
move => oa ob; set c := Spsi a b. 
have oc: ordinalp c by apply: OS_Spsi.
case (equal_or_not (Sphi c \0o) c) => eq1.
  split; last by  move => h; move/(strong_criticalP oc): eq1.
  move:(Spsi_p0 oc); rewrite eq1; move/(Spsi_p4 oc oa OS0 ob).
  by move => [-> _] [_]. 
split; first by move => _ h; move/(strong_criticalP oc): eq1.
move => _.
have: c <o Sphi c \0o. 
  split; [ exact:(osi_gex (proj1 (Sphi_p5)) oc) | by apply:nesym].
rewrite{1}/c /Spsi; set d := Yo _ _ _.
have od: ordinalp d.
  rewrite /d; Ytac h; fprops.
move/(Sphi_p7 od OS0 oa oc) => [qa qb qc].
case: (oleT_ell oa oc) => h.
- by move: (qb h) => /olt0.  
- exact h.
- by move: (qc h) => /olt0.  
Qed.

Lemma Spsi_p6 a b: a <o Gamma_0  -> b <o Gamma_0 ->
  a <o Spsi a b.
Proof.
move => pa pb.
have oa:= proj31_1 pa.
have ob:= proj31_1 pb.
have oc:= (OS_Spsi oa ob).
move: (Gamma0_s_psi pa pb) => h.
apply/(Spsi_p5 oa ob) => /(strong_criticalP oc) h1.
by case: (oleNgt(proj2 Gamma0_p _ oc h1)).
Qed.


Lemma Spsi_p7 x: indecomposable x -> 
  (exists a b, [/\ a <=o x, b <o x  & x = Spsi a b]).
Proof.
move => oix.
move:(Sphi_p10b oix) => [a [b [pa pb pc]]].
move: (pb) => [[ob ox _] _].
case: (p_or_not_p (Spsi_aux a b)); last first.
  by move => h; exists a,b ; split => //; rewrite /Spsi; Ytac0.
move => [n [c [oi oc pd pe]]].
have on:= proj31_1 oi.
case: (ordinal_limA on) => nz.
+ have bc: b = c by move: pd; rewrite nz (osum0r oc).
  move: pe (proj2 pb); rewrite - bc - pc => -> //.
+ move: (predo_K nz); set m := opred n => sm.
  have om: ordinalp m by apply:OS_sup => t /(Os_ordinal on).
  have ocm:= OS_sum2 oc om.
  have le1: c +o m <o x.
     have: c +o m <=o c +o n. 
       apply:osum_Meqle => //; rewrite - sm; exact: (proj1 (oltS om)).
    rewrite - pd => l2; exact:(ole_ltT l2 pb).
  have spa: (Spsi_aux a (c +o m)).
     exists m, c; split => //; move: (oltS om); rewrite sm=> h. 
     exact (olt_ltT h oi).
  exists a, (c +o m); split => //;rewrite /Spsi; Ytac0.
  by rewrite osum2_succ // sm - pd.
case:(oltNge oi (limit_ge_omega nz)). 
Qed.

Lemma Spsi_p2' a b: ordinalp a -> ordinalp b ->
  a <=o Spsi a b.
Proof.
move => oa ob.
have: indecomposable (Spsi a b).
  rewrite /Spsi; Ytac h; apply:Schutte_Cr_p8'; fprops.
move/ (Spsi_p7) => [a' [b' [p1 p2 p3]]].
move: (Spsi_p4 oa (proj31 p1) ob (proj31_1 p2) p3). 
by move => [e1 e2]; rewrite {1} e1.
Qed.

Definition Spsip p := Spsi (P p) (Q p).

Definition inv_psi_omega x:=
  select (fun z => Spsip z = oopow x)
    (coarse (osucc (oopow x))). 

Lemma inv_psi_omega_p x (z:= oopow x) (y:= inv_psi_omega x) : 
   ordinalp x ->
  [/\ pairp y, (P y) <=o z, (Q y) <o z & Spsip y = z].
Proof.    
move => ox.
pose p z:=  (Spsip z = oopow x).
set E := (coarse (osucc (oopow x))).
have oo:= OS_oopow ox.
have osx:= (OS_succ oo).
have pb:singl_val2 (inc^~ E) p.
  move => y1 y2 /setX_P [ra rb rc] e1 /setX_P [ra' rb' rc'].
  rewrite /p - e1 => e2.
  move: (Os_ordinal osx rb) (Os_ordinal osx rc) => o1 o3.
  move: (Os_ordinal osx rb') (Os_ordinal osx rc') => o2 o4.
  move:(Spsi_p4 o2 o1 o4 o3 e2) => [rd re].
  by apply: pair_exten.
move: (Spsi_p7 (indecomp_prop4 ox)) => [a [b [p1 p2 p3]]].
have p4: (inc (J a b) E).
   move:(p2) =>[p2' _];  apply/setX_P; aw; split; fprops; by apply/oleP.
have p5: p (J a b) by rewrite /p/Spsip; aw. 
move: (select_uniq pb p4 p5);  rewrite /y /inv_psi_omega; move => <-; aw.
rewrite p5; split;fprops.
Qed.

Lemma Spsi_p8 a b:
  ordinalp a -> ordinalp b -> (maximal_critical a (Spsi a b)).
Proof.
move => oa ob.
have[c oc h]: exists2 c, ordinalp c & Spsi a b = Sphi a c.
  by rewrite /Spsi; Ytac h; [  exists (osucc b); fprops | exists b].
apply/ (maximal_criticalP oa (OS_Spsi oa ob)); rewrite h.
exists c; [ exact: (Spsi_p1 oa ob oc h) | reflexivity].
Qed.


Lemma odegree_psi a b: ordinalp a -> ordinalp b -> 
  oopow (odegree (Spsi a b)) =  (Spsi a b).
Proof.
move => oa ob.
have: indecomposable (Spsi a b).
  rewrite /Spsi; Ytac h; apply:Schutte_Cr_p8'; fprops.
by move/indecomp_prop3 => [y oy ->]; rewrite(odegree_opow oy).
Qed.

Lemma Spsi_p9 a b: ordinalp a -> ordinalp b ->
  (maximal_critical a b <-> (exists2 c, ordinalp c & b = Spsi a c)).
Proof.
move => oa ob; split; last by move => [c oc ->]; apply:Spsi_p8.
move => /(maximal_criticalP oa ob) [c ca eq].
have oc:= proj31_1 ca.
case: (p_or_not_p (Spsi_aux a c)); last first.
  by move => h; exists c  => //; rewrite /Spsi; Ytac0.
 move => [n [d [oi od pd pe]]].
have on: ordinalp n:= proj31_1 oi.
case: (ordinal_limA on) => nz.
+ have bc: c = d by move: pd; rewrite nz (osum0r od).
  by move: pe (nesym (proj2 ca)); rewrite - bc - eq.
+ move: (predo_K nz); set m := opred n => sm.
  have om: ordinalp m by apply:OS_sup => t /(Os_ordinal on).
  have ocm:= OS_sum2 od om.
  have spa: (Spsi_aux a (d +o m)).
     exists m, d; split => //; move: (oltS om); rewrite sm =>h.
     exact (olt_ltT h oi).
  exists (d +o m) => //;rewrite /Spsi; Ytac0.
  by rewrite osum2_succ // sm - pd.
case:(oltNge oi (limit_ge_omega nz)).
Qed.


Lemma Spsi_p10 a: ordinalp a -> ~(normal_ofs (Spsi a)).
Proof.
move => oa [pa pb].
set x := Sphi (osucc a) \0o.
case:(indecomp_limit (Schutte_Cr_p8' (OS_succ oa) OS0)).
  move: (oltS oa)=> lt1 e1.
  move: (Sphi_p3 OS0 lt1); rewrite e1 => e2.
  have ica:= (proj1 (Sphi_p1 oa)).
  move: (ica _ _  olt_01); rewrite e2;move/olt1 => e3.
  by move:(Schutte_Cr_p8' oa OS0) => [][]; rewrite e3.
rewrite -/x => limx; move: (proj31 limx ) => ox.
move:(Sphi_p1 oa)=> [pa' pb'].
have pc: forall t, t<o x -> Sphi a t <> t.
  move => t tx eq.
  have ot:=proj31_1 tx.
  move: (oltS oa)=> lt1.
  move /(Schutte_Cr_p6 oa ot):(eq) => [y oy yb].
  have : Sphi a t <o x.
    apply/(Sphi_p7 ot OS0 oa (OS_succ oa)); split => //.
      by move => e2; move: (proj2 lt1); rewrite - e2.
    by move /(oleNgt (proj1 lt1)).
  rewrite eq yb /x => eq2.
  case (ozero_dichot oy) => yz; first by move: (proj2 eq2); rewrite yz.
  case: (oltNge eq2 (proj1 (proj1 (Sphi_p1 (OS_succ oa)) _ _ yz))).
have pd: forall t, t<o x -> Sphi a t = Spsi a t.
  move => t tx.
  rewrite /Spsi; Ytac H => //.
  move: H => [n [c [/proj31_1 on oc tv eq]]].
  have cx: c<o x. 
     apply: ole_ltT tx; rewrite tv; apply: osum_Mle0 => //.
  by case (pc _ cx).
have: \osup (fun_image x (Sphi a)) = \osup (fun_image x (Spsi a)).
  by apply: ord_sup_2funI => t tx; apply: pd; apply /oltP.
rewrite - (pb _ limx) - (pb' _ limx).
move: (Sphi_p3 OS0 (oltS oa)); rewrite -/x => -> h.
by move:(proj2 (Spsi_p2 oa ox)); rewrite - h.
Qed.

Lemma Spsi_limit a b: ordinalp a -> ordinalp b ->
   (a <> \0o \/ b <> \0o) -> limit_ordinal (Spsi a b).
Proof.
move => oa ob ha.
have:Spsi a b <> \1o. 
   move:(Spsi_p0 OS0);rewrite (Sphi_p0 OS0) oopow0 => <-.
   by move/(Spsi_p4 oa OS0 ob OS0) => [sa sb];case: ha.
rewrite /Spsi; set c := Yo _ _ _.
have oc: ordinalp c by rewrite /c; Ytac h; fprops.
case: (indecomp_limit(Schutte_Cr_p8' oa oc)) => //.
Qed.

Lemma Spsi_p11 x y : ordinalp x -> ordinalp y ->
  Spsi x y <=o Sphi x (osucc y).
Proof.
move => ox oy;rewrite /Spsi; Ytac h3. 
  apply: oleR; apply:OS_Sphi; fprops.
by move:((proj1 (Sphi_p1 ox) _  _ (oltS oy))) => [].
Qed.

Lemma Spsi_p12 i j x y : 
  ordinalp i -> ordinalp j -> ordinalp x -> ordinalp y ->
  (Spsi i x <o Spsi j y <->
   [/\ i <o j -> x <o Spsi j y, 
       i = j -> x <o y & 
      j <o i -> Spsi i x <=o y]).
Proof.
move =>  oi oj ox oy.
have aux: forall i' j' x' y', i' <o j' -> ordinalp x' -> ordinalp y' ->
  x' <o Spsi j' y' -> Spsi i' x' <o Spsi j' y'.
  move => i' j' x' y' pa ox' oy' sa.
  move: (pa) => [[oi' oj' _] _].
  have: limit_ordinal (Spsi j' y'). 
    apply:(Spsi_limit oj' oy'); left. 
    move => jz; rewrite jz in pa; case: (olt0 pa).
  move/(limit_ordinal_P) => [_ h1]; move: (h1 _ sa) => h2.
  have ha:= (Spsi_p11 oi' ox').
  move: (ole_ltT ha ((proj1 (Sphi_p1 oi') _ _ h2))).
  rewrite {2 4} /Spsi; set c := Yo _ _ _.
  have oc: ordinalp c by rewrite /c; Ytac h4; fprops.
  by rewrite (Sphi_p3 oc pa).
case (oleT_ell oi oj) => ij.
- have bad: i <o i -> False by  move => [].
  rewrite - ij; split. 
    move => h; split => h1; try (by case: bad).
    case: (oleT_ell ox oy) => // h2.
       by move: (proj2 h); rewrite h2.     
       case: (oltNge h (proj1 (Spsi_p3 oi h2))).
    move => [_ h _]; exact: (Spsi_p3 oi (h (erefl i))).
- split.
    move => h; split.
      + move => _; case (oleT_el (OS_Spsi oj oy) ox) => // h1.
        exact: (ole_ltT (proj1 (Spsi_p2 oi ox)) h).
      + by move => eq; move: (proj2 ij); case.
      + by move=> [/(oltNge ij)].
    by move => [h _ _]; move: (h ij) => sa; by apply: aux.
- split.
    move => h; split. 
      + by move=> [/(oltNge ij)].
      + by move => eq; move: (proj2 ij); case.
      + move => _. 
        case (oleT_el (OS_Spsi oi ox) oy) => // h1.
        case: (oleNgt (proj1 (aux _ _ _ _ ij oy ox h1)) h).
    move => [_ _ h]; move: (h ij) => sa.
    exact: (ole_ltT sa (Spsi_p2 oj oy)).
Qed.

(** CNF below Gamma0 via psi *)


Definition CNF_from_psi (p: fterm) z := odegree (Spsip (p z)).


Definition CNF_psi_ax p n :=
  (forall i, i <c n -> ordinal_pair (p i)) /\ 
  (forall i, natp i -> csucc i <c n -> 
   Spsip (p i) <=o  Spsip (p (csucc i))).

Definition CNF_psi_ax2 p n :=
  CNF_psi_ax p n /\
     (forall i, i <c n -> P (p i) <o Gamma_0  /\ Q (p i) <o Gamma_0).

Definition CNF_psiv p n :=CNFrv (CNF_from_psi p) n.

Lemma CNF_psi_p0 p n: CNF_psi_ax p n -> natp n ->
  CNF_psiv p n =  osumf (fun i => (Spsip (p i))) n.
Proof.
move => [a1 a2] nN.
apply: (osumf_exten nN) => i lin.
move: (a1 _ lin) => [_ pb pc];exact (odegree_psi pb pc).
Qed.

Lemma CNF_psi_p1 p n: CNF_psi_ax p n -> CNFr_ax (CNF_from_psi p) n.
Proof.
move => [ax1 ax2]; split.
  move => i lin; move: (ax1 _ lin) => [_ qa qb]. 
  apply:(OS_degree (OS_Spsi qa qb)).
move => i iB lin.
move: (ax1 _ (cle_ltT (cleS iB) lin)) => [_ qc qd].
move: (ax1 _ lin) => [_ qa qb]; rewrite /CNF_from_psi.
move: (odegree_psi qa qb) (odegree_psi qc qd) => eq1 eq2.
move:(ax2 i iB lin); rewrite /Spsip -{1} eq1 - {1} eq2 => h.
move:(OS_degree (OS_Spsi qa qb)) (OS_degree (OS_Spsi qc qd)) => o1 o2.
by move/(opow_Mo_leP o2 o1):h.
Qed.

Lemma CNF_psi_unique p1 n p2 m:
  natp n ->natp m -> CNF_psi_ax p1 n -> CNF_psi_ax p2 m ->
  CNF_psiv p1 n = CNF_psiv p2 m ->
  n = m /\  same_below p1 p2 n.
Proof.
move => nN mN sa sb sc.
move: (CNFr_unique  (CNF_psi_p1 sa)  (CNF_psi_p1 sb) nN mN sc) => [sd se].
split; [ exact | move => i lin].
move: (lin); rewrite sd => lim.
move: (proj1 sa _ lin) (proj1 sb _ lim) => [{3}<- o1 o2] [{3}<- o3 o4].
move:(f_equal oopow (se _ lin)). rewrite /CNF_from_psi.
rewrite {1}(odegree_psi o1 o2) (odegree_psi o3 o4).
by move/ (Spsi_p4 o1 o3 o2 o4) =>[-> ->].
Qed.

Lemma CNF_psi_exists x: ordinalp x -> 
  exists p n, [/\ natp n, CNF_psi_ax p n & x = CNF_psiv p n].
Proof.
move => ox; move:(CNFr_exists ox) => [f [n [nN [ax1 ax2] xv]]].  
pose g i := inv_psi_omega (f i).
have ha:forall i, i <c n -> ordinal_pair (g i).
  move => i lin; move:(inv_psi_omega_p (ax1 i lin)).
  by move => [ha /proj31 hb /proj31_1 hc].
have ax:CNF_psi_ax g n.
  split; [exact | move => i iN lin].
  have lin':=(cle_ltT (cleS iN) lin).
  move: (ax2 _ iN lin) => sa.
  move:(inv_psi_omega_p (proj31 sa)) => [_ _ _ ->].
  move:(inv_psi_omega_p (proj32 sa)) => [_ _ _ ->].
  by apply:opow_Mo_le.
exists g, n; split; [ exact | exact |].
rewrite xv;apply: (osumf_exten nN) => i lin.
rewrite /CNF_from_psi; move:(inv_psi_omega_p (ax1 _ lin)) => [_ _ _ ->].
by rewrite (odegree_opow (ax1 _ lin)).
Qed.

Lemma CNF_psi_lt_Gamma0 p n: natp n -> CNF_psi_ax2 p n  ->
   CNF_psiv p n <o Gamma_0.
Proof.
rewrite /CNF_psiv/CNFrv. 
have gl:= Gamma0_limit.
move: n; apply: Nat_induction.
  by move => _; rewrite osum_f0; move/limit_pos: gl.
move => n nN Hrec [[h1 h2] h3].
have nn:=(cltS nN).
move: (indecomp_prop4 (proj31 gl)); rewrite Gamma0_epsilon.
rewrite  /CNF_psiv /CNFrv (osum_fS _ nN).
have: CNF_psi_ax2 p n.
  split; first split. 
  + move => i lin; apply: h1 (clt_ltT lin nn).
  + move => i iN slin; apply: h2 iN (clt_ltT slin nn). 
  + move => i lin; apply:h3  (clt_ltT lin nn).
move /Hrec; apply: indecomp_prop2.
move: (h3 _ nn) => [sa sb].
move: (Gamma0_s_psi sa sb); rewrite /CNF_from_psi.
by rewrite (odegree_psi (proj31_1 sa) (proj31_1 sb)).
Qed.

Lemma CNF_psi_exists_Gamma0 x: x <o Gamma_0 -> 
  exists p n, [/\ natp n, CNF_psi_ax2 p n & x = CNF_psiv p n].
Proof.
move => h; move: (CNF_psi_exists (proj31_1 h)) => [p [n [nN pb xv]]].
exists p,n => //; split => //; split; first by exact.
move => i idf.
move: (CNFr_p3 nN (CNF_psi_p1 pb) idf).
rewrite /CNF_from_psi.
move:(proj1 pb _ idf) => [ _ pd pe].
rewrite (odegree_psi pd pe).
rewrite -/(CNF_psiv p n) - xv => l1; move: (ole_ltT l1 h) => ha.
split.
  exact: (ole_ltT (Spsi_p2' pd pe) ha).
exact: (ole_ltT (proj1 (Spsi_p2 pd pe)) ha).
Qed.

Definition epsilon0 := epsilon_fam \0o.

Lemma epsilon0p: epsilonp epsilon0. 
Proof.  apply: (epsilon_fam_pr0 OS0). Qed.

Lemma sum_lt_eps0 a b: a <o  epsilon0 -> b <o epsilon0 -> 
  a +o b <o epsilon0. 
Proof.
move => ae be.
have h: indecomposable epsilon0.
  by move: epsilon0p => [pa <-]; apply: indecomp_prop4. 
apply:(indecomp_prop2 ae be h).
Qed.

Lemma prod_lt_eps0 a n: a <o epsilon0 ->  natp n -> a *o n <o epsilon0.
Proof.
move => ae nN; move:(proj31_1 ae) => oa.
move: n nN; apply:Nat_induction.
   rewrite oprod0r; exact: (ole_ltT (ole0x oa) ae).
move => n nN Hrec. 
rewrite (succ_of_nat nN) (oprod2_succ oa  (OS_nat nN)).
apply: (sum_lt_eps0 Hrec ae).
Qed.

Lemma pow_lt_eps0 a: a <o epsilon0 -> oopow a <o epsilon0.
Proof. by move /opow_Mo_lt; move:epsilon0p => [_ ->]. Qed.

Definition CNF_simple_ax a n b x :=
  [/\ ordinalp a, ordinalp b, natp n, x = oopow a *o (csucc n) +o b &
      b <o  omega0 ^o a].

Lemma CNF_simple_p1 a n b x: CNF_simple_ax a n b x ->
  ord_ext_div_pr  omega0 x a (csucc n) b.
Proof.
move: OS_omega => oo [pa pb pc pd pe].
have csn := NS_succ pc.
have osn:= OS_nat csn.
split => //; split => //; first by apply/(oltP oo).
apply: (ord_ne0_pos osn); apply: succ_nz.
Qed.

Lemma CNF_simple_p2 a n b x: CNF_simple_ax a n b x -> 
 [/\ a <=o x, b <o x & oopow a <=o x].
Proof.
move => hx; move:(CNF_simple_p1 hx) => [ha hb hc [hd he hf hg]].
move:(proj1 (ord_eps_p2 ha hg hc)); rewrite - hd => ax.
move: hx => [_ _ nN _ _].
have oa:=(proj32_1 he).
have on:=(OS_nat nN).
have ob:=(OS_prod2 oa on).
have pa: omega0 ^o a *o csucc n = omega0 ^o a +o omega0 ^o a *o n. 
   rewrite (Nsucc_rw nN) csumC - (osum2_2int NS1 nN)  (oprodD OS1 on oa). 
   rewrite oprod1r //. 
have hi: omega0 ^o a <=o x. 
  rewrite hd pa -(osumA oa ob hc); apply: (osum_Mle0 oa (OS_sum2 ob hc)).
split => //;exact:olt_leT he hi.
Qed.

Lemma CNF_simple_bnd a n b x: CNF_simple_ax a n b x ->
  inc (J a (J n b)) (osucc x \times (Nat \times x)).
Proof.
move => hx; move:(CNF_simple_p1 hx) => [ha hb hc [hd he hf hg]].
move:(proj1 (ord_eps_p2 ha hg hc)); rewrite - hd => ax.
move:(CNF_simple_p2 hx) => [_ bx1 _].
have bx: inc b x by apply/(oltP (proj32 ax)). 
move/ (oleP (proj32 ax)): ax => asx.
move: hx => [_ _ nN _ _].
apply: (setXp_i asx); apply:(setXp_i nN bx).
Qed.

Lemma CNF_simple_unique a n b a' n' b' x:
  CNF_simple_ax a n b x -> CNF_simple_ax a' n' b' x ->
  [/\ a = a', b = b' & n = n'].
Proof.
move => ha1 hb1.
move: (ha1)(hb1) => / CNF_simple_p1 ha / CNF_simple_p1 hb.
have osx : ordinalp x by move:ha => [oa ob oc [-> _ _ _]]; fprops.
move: (ord_ext_div_unique ole_2omega osx ha hb) => [hd he hf].
move: ha1 hb1 => [ _ _ /CS_nat cn _ _] [ _ _ /CS_nat cn' _ _].
by split => //; apply:csucc_inj. 
Qed.

Lemma CNF_simple_exists x: \0o <o x -> 
  exists a n b, CNF_simple_ax a n b x.
Proof.
move => xp.
move: (ord_ext_div_exists ole_2omega xp) => [a [c [b [oa oc ob]]]].
move => [-> ha hb hc]; exists a, (cpred c), b.
move /(oltP OS_omega): hb => cN.
move: (cpred_pr cN (nesym (proj2 hc))) => [hd he]. 
by hnf; rewrite -he.
Qed.

Definition the_CNF_simpl x := 
   select (fun z => (CNF_simple_ax (P z) (P (Q z)) (Q (Q z)) x))
     (osucc x \times (Nat \times x)).

Lemma the_CNF_simplP x (z := the_CNF_simpl x):
   \0o <o x -> CNF_simple_ax (P z) (P (Q z)) (Q (Q z)) x.
Proof.
move => xp.
set E :=  (osucc x \times (Nat \times x)).
set p := (fun z => (CNF_simple_ax (P z) (P (Q z)) (Q (Q z)) x)).
have ha: (exists2 z, inc z E & p z).
  move:(CNF_simple_exists xp) => [a [n [b h]]].
  move: (CNF_simple_bnd h) => h'; exists (J a (J n b)) => //.
  by rewrite /p; aw.
have hb:singl_val2 (inc^~ E) p.
  move => z' z'' /setX_P [qa qb /setX_P [qc qd qe]] az za' az'.
  move: za' => /setX_P [qa' qb' /setX_P [qc' qd' qe']].
  move:(CNF_simple_unique az az') => [e1 e2 e3].
  by rewrite - qa - qa' - qc - qc' e1 e2 e3.
exact: (proj1 (@select_pr p E ha hb)).
Qed.

Lemma ord_eps_p2_bis a b c (x := oopow a *o b +o c):
  ordinalp a -> \0o <o b -> ordinalp c -> x <o epsilon0 -> a <o x.
Proof.
move => pa pb pc pd.
move:(ord_eps_p2 pa pb pc); rewrite -/x; move => [sa sb]; split => // eax.
move: (sb (esym eax)) => [_ _ h].
move: (proj2(epsilon_fct_pr3)); rewrite -epsilon_fam_pr2 -/epsilon0 => ha.
case: (oltNge pd (ha _ h)).
Qed.

Lemma CNF_simple_bdn2 x (z := the_CNF_simpl x): \0o <o x ->
  x <o epsilon0 -> ( P z <o x /\ (Q (Q z)) <o x).
Proof.
move => h hx.
move: (the_CNF_simplP h). 
set a :=(P (the_CNF_simpl x)).
set b:= (P (Q (the_CNF_simpl x))).
set c:= (Q (Q (the_CNF_simpl x))).
move => h1.
move:(CNF_simple_bnd h1) => /setX_P [_ _ /setX_P[_ _]]; aw.
move/(oltP (proj32_1 h)) => cx; split => //.
move/CNF_simple_p1: h1 =>[ha hb hc [hd he hf hg]].
by move:(ord_eps_p2_bis ha hg hc);rewrite - hd; apply.
Qed.


Lemma Gamma0_p1: Spsi Gamma_0 \0o = Gamma_0.
Proof. by rewrite (Spsi_p0 OS_Gamma_0) (proj1 Gamma0_p). Qed.

Lemma Spsi_indecomposable a b: 
  ordinalp a -> ordinalp b -> indecomposable (Spsi a b).
Proof.
move => oa ob.
rewrite /Spsi;apply:(Schutte_Cr_p8' oa); Ytac h=> //; fprops.
Qed.

Lemma Spsi_pos a b: ordinalp a -> ordinalp b -> 
   \0o <o (Spsi a b).
Proof. move => oa ob; exact: (proj1 (Spsi_indecomposable oa ob)). Qed.

Lemma Spsi_nz a b: ordinalp a -> ordinalp b -> 
  (Spsi a b) <> \0o.
Proof. move => oa ob;  exact (nesym (proj2 (Spsi_pos oa ob))). Qed.

Lemma Spsi_indecomp_rec u v a b n (x := Spsi u v):
  ordinalp u -> ordinalp v ->
  a <o x -> b <o x -> a *o csucc (nat_to_B n) +o b <o x.
Proof.
move => ou ov ax bx.
move:(Spsi_indecomposable ou ov); rewrite -/x => Ha.
have Hb: forall a' b', a' <o x -> b' <o x -> a' +o b' <o x.
  move => a' b' a'x b'x;apply:(indecomp_prop2 a'x b'x Ha).
apply: (Hb _ _ _ bx). move:(proj31_1 ax) => oa.
have Hc: forall m, natp m -> a *o m <o x.
   apply: Nat_induction.
     rewrite oprod0r; exact: (ole_ltT (ole0x oa) ax).
   move => m mN Hrec. 
   by rewrite (succ_of_nat mN) (oprod2_succ oa  (OS_nat mN)); apply: Hb.
apply: Hc; apply: (NS_succ (nat_to_B_Nat n)).
Qed.

Lemma T2_to_bourbaki_small a b c n:
   a <o Gamma_0 -> b <o Gamma_0 -> c <o Gamma_0 ->
   Spsi a b  *o csucc (nat_to_B n) +o c <o Gamma_0.
Proof.
move => ha hb hc.
move: (Gamma0_s_psi ha hb) => hd.
move: Gamma0_p1 => h; rewrite -h in hc hd  |- *.
exact: (Spsi_indecomp_rec n OS_Gamma_0 OS0 hd hc).
Qed.

Lemma inv_psi_omega_p2 x (z:= oopow x) (y:= inv_psi_omega x) : 
   ordinalp x ->x <o Gamma_0 ->
  [/\ pairp y, (P y) <o z, (Q y) <o z & Spsi (P y) (Q y) = z].
Proof.
move => pa pb; move:(inv_psi_omega_p pa).
rewrite -/z -/y; move => [sa sb sc sd]; split => //.
have zg: z <o Gamma_0 by rewrite - Gamma0_epsilon /z; apply:opow_Mo_lt.
rewrite - sd;apply:(Spsi_p6 (ole_ltT sb zg) (olt_ltT sc zg)).
Qed.

Lemma  CNF_simple_bdn3 x (v := (P (the_CNF_simpl x))) (y:= inv_psi_omega v):
   \0o <o x -> x <o Gamma_0 ->
   [/\ pairp y, (P y) <o x, (Q y) <o x & 
     Spsi (P y) (Q y) = omega0 ^o v ].
Proof.
move => pa pc.
move:(the_CNF_simplP pa) => ha.
move:(CNF_simple_p2 ha) =>[hb hc hd].
move:(inv_psi_omega_p2 (proj31 hb) (ole_ltT hb pc)) => [qa qb qc qd].
split; [exact | exact: (olt_leT qb hd) | exact: (olt_leT qc hd) | exact].
Qed.


Lemma Spsi_cpa a a' b b':
  ordinalp b' -> 
  a <o a' -> b <o Spsi a' b' -> Spsi a b <o Spsi a' b'.
Proof.
move => ob' pa pb.
have [[oa oa' _] _] := pa.
have ob:= proj31_1 pb.
apply/(Spsi_p12 oa oa' ob ob'); split => //.
  by move => h; case (proj2 pa).
by move => [/(oltNge pa)].
Qed.

Lemma Spsi_cpb a a' b b':
  ordinalp a ->
  a = a' -> b <o b' -> Spsi a b <o Spsi a' b'.
Proof.
move => oa pa pb.
have [[ob ob' _] _] := pb.
have oa': ordinalp a' by rewrite - pa.
by apply/(Spsi_p12 oa oa' ob ob'); rewrite - pa;split => // [] []. 
Qed.

Lemma Spsi_cpc a a' b b':
  ordinalp b ->
  a' <o a -> Spsi a b <=o b' -> Spsi a b <o Spsi a' b'.
Proof.
move => ob pa pb.
have [[oa' oa _] hh] := pa.
have ob':= proj32 pb.
apply/(Spsi_p12 oa oa' ob ob'); split => // ha; last by case: hh.
case: (oltNge pa (proj1 ha)).
Qed.
  
(** ** Initial ordinals *)

Lemma iclosed_non_coll_infinite_c:
  iclosed_proper infinite_c. 
Proof.
have H: ordinal_prop infinite_c by move => x [[oc _]_].
split; first split => //.
  move => F iF [y yF].
  have cs: cardinal_set F by move =>  z /iF [].
  exact: (cle_inf_inf (iF _ yF)  (card_sup_ub cs yF)).
apply: unbounded_non_coll => //.
move => x ox; case: (oleT_ee ox OS_omega) => cxo.
   exists omega0 => //; apply: CIS_omega. 
have aux: cardinal x <c  \2c ^c x by rewrite - cpowcr; apply: cantor; fprops.
move /infinite_setP:(infinite_set_pr3 cxo) => hh.
move:  (cle_inf_inf hh (proj1 aux)) => aux2.
move /(ocle2P (proj1 aux2) ox): aux => [aux3 _].
by exists (\2c ^c x).
Qed.

Definition omega_fct := ordinalsf infinite_c.
Definition ord_index:= 
    ordinalr (fun x y => [/\ infinite_c x, infinite_c y & x <=o y]).

Notation "\omega" := omega_fct.
Notation "\aleph" := omega_fct (only parsing).
Definition omega1 :=  \omega \1o.
Definition aleph1 :=  \aleph \1o.
Definition omega2 :=  \omega \2o.
Definition aleph2 :=  \aleph \2o.

Lemma aleph_normal: normal_ofs \omega.
Proof. 
have [icx nbx]:= iclosed_non_coll_infinite_c;exact:ordinals_col_p2.
Qed.

Lemma aleph0E: \omega \0o = omega0.
Proof. 
have icx:= iclosed_non_coll_infinite_c.
have [ir lr]:=(iclosed_col_f0 icx).
exact: (extensionality (proj33 (lr _ CIS_omega)) (omega_limit3 ir)).
Qed.

Lemma cnextE n: ordinalp n ->
   cnext (\aleph n) = \aleph (osucc n).
Proof.
have ilx:= iclosed_non_coll_infinite_c.
move/ (iclosed_col_fs ilx) => [xy icx icy h]. 
move: (icx)(icy) => [cx _] [cy _].
move: (cnext_pr1 cx)=> [ua ub uc]; apply: cleA.
  apply: uc; apply:(oclt3 cx cy xy). 
have sa:=(cle_inf_inf icx (proj1 ub)).
exact:(ocle3 cy ua  (h _ sa (oclt ub))).
Qed.

Lemma Cantor_omega_pr3: aleph1 = aleph_one.
Proof. by rewrite /aleph1 - osucc_zero - (cnextE OS0) aleph0E. Qed.

Lemma CIS_aleph x: ordinalp x -> infinite_c (\aleph x).
Proof.
move: iclosed_non_coll_infinite_c => [ [pa _] pb].
by move:(ordinals_col_p1 pa pb) => [h _ _ _ _]; apply: h.
Qed.

Lemma CS_aleph x: ordinalp x -> cardinalp (\aleph x).
Proof. by move=> /CIS_aleph []. Qed.

Hint Resolve CS_aleph: fprops.

Lemma OS_aleph x: ordinalp x -> ordinalp (\omega x).
Proof. by move=> /CS_aleph []. Qed.
 
Lemma aleph_pr5 x: ordinalp x -> omega0 <=o (\omega x).
Proof. by move => /CIS_aleph /infinite_c_P2 /ocle. Qed.

Lemma aleph_lt_lto x y: x <o y ->  \omega x <o \omega y.
Proof. exact:(proj1 aleph_normal). Qed.

Lemma aleph_le_leo x y: x <=o y -> \omega x <=o \omega y.
Proof. 
move => xy; case: (equal_or_not x y) => nxy.
  rewrite - nxy; exact: (oleR(OS_aleph (proj31 xy))).
by move: (aleph_lt_lto  (conj xy nxy)) => [ok _].
Qed.

Lemma aleph_leo_le x y: ordinalp x -> ordinalp y ->
  \omega x <=o \omega y -> x <=o y.
Proof.
move=> oa ob lef.
case: (oleT_el oa ob) => // aux.
case: (oleNgt lef (aleph_lt_lto aux)).
Qed.
   
Lemma aleph_inj x y: ordinalp x -> ordinalp y ->
  \omega x = \omega y -> x = y.
Proof.
move=> oa ob lef.
by case: (oleT_ell oa ob) => // /aleph_lt_lto []; rewrite lef.
Qed.

Lemma aleph_lto_lt x y: ordinalp x -> ordinalp y ->
  \omega x <o \omega y -> x <o y.
Proof.
move => ox oy lt1.
case: (oleT_el oy ox) => // h.
case:(oltNge lt1 (aleph_le_leo h)).
Qed.

Lemma aleph_pr6 x: ordinalp x -> x <=o \omega x.
Proof. apply: (osi_gex aleph_lt_lto). Qed.

Lemma aleph_le_lec x y: x <=o y -> \aleph x <=c \aleph y.
Proof.
move=> xy.
apply /(ocle3 (CS_aleph (proj31 xy))(CS_aleph (proj32 xy)));exact:aleph_le_leo.
Qed.

Lemma aleph_lt_ltc x y: x <o y -> \aleph x <c \aleph y.
Proof.
move=> xy; move: (xy) => [[ox oy _] _].
apply /(oclt3 (CS_aleph ox)(CS_aleph oy));exact:aleph_lt_lto.
Qed.

Lemma aleph_lec_le x y: ordinalp x -> ordinalp y ->
  \aleph x <=c \aleph y -> x <=o y.
Proof. 
by move => ox oy le; apply: aleph_leo_le => //; apply:ocle.
Qed.

Lemma aleph_ltc_lt x y: ordinalp x -> ordinalp y ->
  \aleph x <c \aleph y -> x <o y.
Proof. 
by move => ox oy lt; apply: aleph_lto_lt => //; apply:oclt.
Qed.

Lemma aleph_nz x: ordinalp x -> \aleph x <> \0c.
Proof.
move=> ox; exact: (infinite_nz (CIS_aleph ox)). 
Qed.

Lemma aleph_nz1 x: ordinalp x -> \0c <c \aleph x.
Proof.
move=> ox; exact:(clt_fin_inf finite_0 (CIS_aleph ox)).
Qed.

Lemma ord_index_pr1 x: infinite_c x -> 
   (ordinalp (ord_index x) /\ \aleph (ord_index x) = x).
Proof. by move =>icx; apply: ordinalrsP => // t [[]]. Qed.

Lemma ord_index_pr n: ordinalp n ->
   ord_index (\aleph n) = n.
Proof.
move => on; move: (CIS_aleph on) => /ord_index_pr1 [h1 h2].
exact: (aleph_inj h1 on h2).
Qed.

Definition ContHypothesis:= cnext omega0 = \2c ^c omega0.
Definition GenContHypothesis:= forall x, infinite_c x -> cnext x = \2c ^c x.

Lemma aleph_pr10a x y: ordinalp x ->
   y <c \aleph (osucc x) -> y <=c \aleph x.
Proof.
move => ox lt1; move: (lt1) => [[cy cso _] _].
case: (cleT_el cy (CS_aleph ox)) => // pc.
have iy := (cle_inf_inf (CIS_aleph ox) (proj1 pc)).
move: (ord_index_pr1 iy) lt1 => [ox' <- /(aleph_ltc_lt ox' (OS_succ ox))].
by move /oltSleP/aleph_le_lec.
Qed.

Lemma aleph_pr10b x y: ordinalp x ->
  \aleph x <c y -> \aleph (osucc x) <=c y.
Proof.
move=> ox h.
case: (cleT_el (CS_aleph (OS_succ ox)) (proj32_1 h)) => // pc.
case: (cltNge h (aleph_pr10a ox pc)).
Qed.

Lemma aleph_pr10c x: ordinalp x ->
  \aleph x <c \aleph (osucc x).
Proof. by move=> ox; exact: (aleph_lt_ltc (oltS ox)). Qed.

Lemma aleph_limit x: ordinalp x -> limit_ordinal (\omega x).
Proof. by move => ox; apply: (infinite_card_limit2 (CIS_aleph ox)). Qed.

Lemma aleph_pr12b x z :  
  ordinalp x -> ordinalp z -> \aleph x <c cardinal z -> 
  \aleph (osucc x) <=o z.
Proof.
move=> ox oz ycz.
exact: (oleT (ocle (aleph_pr10b ox ycz))  (card_ord_le oz)).
Qed.

Lemma aleph_pr12c x z:  
  ordinalp x -> ordinalp z -> cardinal z <=c \aleph x -> 
  z <o \aleph (osucc x).
Proof.
move=> ox oz p1; move: (p1) => [_ cy _].
rewrite - (cnextE ox); apply /(oltP (proj1 (CS_cnext cy))). 
by apply/cnextP. 
Qed.

Lemma aleph_pr12d x z:
  ordinalp x -> z <o (\aleph (osucc x)) -> 
  cardinal z <=c (\aleph x).
Proof. 
move => ox lt1.
have oz:= proj31_1 lt1.
case: (cleT_el (CS_cardinal z) (CS_aleph ox)) => // h.
case: (oltNge lt1 (aleph_pr12b ox oz h)).
Qed.

Lemma aleph_pr12e x: ordinalp x ->
  \aleph (osucc x) <c \2c ^c (\2c ^c (\aleph x)).
Proof.
move => ocx;move: (CIS_aleph ocx); set E:= \aleph x => ife.
suff: \omega (osucc x) <=c  (\2c ^c E).
   move => h; apply: (cle_ltT h); apply: (cantor (proj32 h)).
rewrite - (cnextE ocx); apply:cnext_pr3; apply:(CS_aleph ocx).
Qed.

Lemma aleph_pr12f a: ordinalp a -> \aleph (osucc a) <=c \2c ^c (\aleph a).
Proof.
move => oa; apply: (aleph_pr10b oa (cantor (CS_aleph oa))).
Qed.

(** ** cardinal cofinality *)

Definition csum_of_small0 x f:=
  fgraph f /\ allf f (fun z => z <=c x).
Definition csum_of_small1 x f:=
  fgraph f /\ allf f (fun z => z <c x).

Lemma csum_commutative1 f x:
  csum_of_small1 x f -> exists g,
   [/\ csum_of_small1 x g, domain g = cardinal (domain f),
     csum f = csum g & range g = range f].
Proof.
move=> [fgf pb].
move: (CS_cardinal (domain f)) => [ocy cyp].
set z1 := cardinal (domain f).
have /card_eqP [g [bg sg tg]]: z1 =c (domain f) by rewrite /z1; aw.
set h := Lg z1 (fun i => Vg f (Vf g i)).
have dh: domain h = z1 by rewrite /h; aw.
have fgh: fgraph h by rewrite /h; fprops.
have sh: forall i, inc i (domain h) -> Vg h i <c x.
  rewrite /h; aw => i id; rewrite LgV//; apply: pb. 
  rewrite - tg; apply: Vf_target; try fct_tac; ue.
have ch: cardinal_fam h by move =>  a ay; exact: (proj31_1 (sh _ ay)).
have fg: function g by fct_tac.
have rh: range h = range f.
  rewrite /h; set_extens t.
    move/(range_gP fgh); rewrite dh; move => [u p1 ->]; rewrite /h LgV //.
    apply /(range_gP fgf); exists (Vf g u)=> //; rewrite -tg; Wtac. 
  move /(range_gP fgf) =>  [u p1 ->]; apply/(range_gP fgh).
  rewrite - tg in p1; move: ((bij_surj bg) _ p1) => [w usg ww]. 
  rewrite /h; rewrite dh - sg; ex_tac; rewrite LgV// ; ue.
exists h => //; split => //.
have ->: h = f \cf (graph g).
  rewrite /composef /h /Vf.
  have -> //: domain (graph g) = z1 by rewrite domain_fg.
apply: csum_Cn => //. 
Qed.

Lemma csum_of_small_b1 x f: csum_of_small0 x f ->
  csum f <=c (x *c (domain f)).
Proof.
move=> [p1 p2];rewrite - csum_of_same.
by apply:csum_increasing; aw => //; fprops => a adf; rewrite LgV//; apply: p2. 
Qed.

Lemma csum_of_small_b2 x f: csum_of_small1 x f ->
  csum f <=c (x *c (domain f)).
Proof.
by move=> [p1 p2]; apply: (csum_of_small_b1); split => // i /p2 [].
Qed.

Lemma csum_of_small_b3 x f:
  csum_of_small1 x f ->
  (exists2 n, ordinalp n & x = \aleph (osucc n)) -> 
  (cardinal (domain f)) <c x ->  (csum f) <c x.
Proof.
move=> [pa pb] [n on xv] zx.
rewrite xv in zx.
move: (aleph_pr10a on zx) => le1.
have pe: (allf f (cardinal_le ^~ (\omega n))).
  move=> i /pb; rewrite xv; apply: (aleph_pr10a on).
move: (csum_of_small_b1 (conj pa pe)) => le2.
move: (cprod_inf1 le1 (CIS_aleph on)); rewrite cprod2cr => le3.
rewrite xv; exact (cle_ltT (cleT le2 le3) (aleph_pr10c on)).
Qed.

Lemma csum_of_small_b4 f (s:= \csup (range f)) :
   fgraph f -> cardinal_fam f -> infinite_c s ->
   (cardinal (domain f) <=c s) -> csum f = s.
Proof.
move=> pa1 pa pb pc.
have csr: cardinal_set (range f).
  by move=> t /(range_gP pa1) [u ua ->]; apply: pa.
have pe: s *c domain f = s.
   rewrite - cprod2cr; apply: cprod_inf => //.
   apply: card_nonempty1.
   case: (emptyset_dichot (domain f)) => // de.
   move: (clt_fin_inf finite_0 pb) => [_]; rewrite /s.
   have -> :(range f = emptyset) by apply /range_set0_P; apply/domain_set0_P.
   by rewrite setU_0;case.
apply: cleA.
  have pd: (allf f (cardinal_le ^~  s)).
    move=> i idf; apply: (card_sup_ub csr); apply /(range_gP pa1); ex_tac.
    by rewrite - pe; apply:(csum_of_small_b1 (conj pa1 pd)).
apply: card_ub_sup => //; first by rewrite /csum; fprops.
move => a /(range_gP pa1) [x xdf ->]; apply: csum_increasing6 =>//.
by apply:pa.
Qed.

Lemma csum_of_small_b5 f (s:= \csup (range f)) :
   fgraph f -> cardinal_fam f -> 
   (exists i, [/\ inc i (range f), infinite_c i & cardinal (domain f) <=c i])
   -> csum f = s.
Proof.
move => pa pa2 [i [ir l1 l2]].
have csr: cardinal_set (range f)
  by move=> t /(range_gP pa) [u ua ->]; apply: pa2.
have pb:=(card_sup_ub csr ir).
have pc := (cleT l2 pb).
apply: csum_of_small_b4 => //. apply: (cle_inf_inf l1 pb).
Qed.

Definition cofinality_c_ex x z :=
   exists f, [/\ csum_of_small1 x f, domain f = z & csum f = x].
Definition cofinality_c x:= 
  least_ordinal (cofinality_c_ex x) x.
Definition regular_cardinal x :=
  infinite_c x /\ cofinality_c x = x.

Lemma cofinality_c_of0: cofinality_c \0c = \0c.
Proof.
rewrite /cofinality_c /least_ordinal; set E := Zo _ _.
case: (emptyset_dichot E) => h; first by rewrite h; exact setI_0.
apply/set0_P => t tiE; move: h => [y ye];move:(setI_hi tiE  ye).
move/Zo_P:ye => [_] [f [[_  ha] hb hc]].
rewrite - hb;case: (emptyset_dichot (domain f)); first by move  => -> /in_set0.
by move => [i /ha /clt0].
Qed.


Lemma cofinality_c_of1: cofinality_c \1c = \0c.
Proof.
rewrite /cofinality_c /least_ordinal; set E := Zo _ _.
case: (emptyset_dichot E) => h; first by rewrite h; exact setI_0.
move: h => [y /Zo_P [_ [f[[fgf ha] hb]]]].
have ->:csum f = (csumb (domain f) (fun i =>\0c)).
  rewrite - csum_gr; apply: csumb_exten => i idf.
  by move: (clt1 (ha _ idf)).
by rewrite csum_of_same cprod0l => lt; case: card1_nz.
Qed.



Lemma cofinality_c_rw x (y:= cofinality_c x): \2c <=c x ->
  [/\ y <=c x,
      cofinality_c_ex x y 
     & (forall z, ordinalp z -> (cofinality_c_ex x z) -> y <=o z)].
Proof.
move=> x2.
have cx:= proj32 x2.
move: (cx) => [ox _]. 
have x1:=(clt_leT clt_12 x2).
pose p := cofinality_c_ex x.
have px: p x. 
  exists (cst_graph x \1c); split.
  - split;[ fprops | hnf; aw=> a ax; rewrite LgV//]. 
  - by aw.
  - by rewrite [csum _](csum_of_ones x); apply: card_card.
move: (least_ordinal1 ox px) => [].
rewrite -/(cofinality_c x) -/y; move=> oy py pb.
have pa: forall z, ordinalp z -> p z -> y <=o z.
  by move => z oz pz; move: (pb _ oz pz)=> yz.
split => //.
move: py => [f [qa qb qc]].
move: (csum_commutative1 qa)=> [g [ga gb gc gd]].
have pcy: p (cardinal y) by  exists g; rewrite gb qb - gc qc.
move: (oleA (pa _ (proj1 (CS_cardinal y)) pcy) (card_ord_le oy)) => H.
split => //; [ rewrite H; fprops | exact: (pb _ ox px)].
Qed.

Lemma cofinality_c_pr2 x: \2c <=c x -> 
 exists f, [/\ csum_of_small1 x f, domain f = (cofinality_c x), csum f = x
       & (allf f (fun z => z <> \0c)) ].
Proof.
move=> h; move: (cofinality_c_rw h) => [pa pb pc].
move: pb => [f [[pd pe] pf pg]].
set j := Zo (domain f) (fun z => Vg f z <> \0c).
have sj: sub j (domain f) by apply: Zo_S.
have qa: (forall i, inc i ((domain f) -s j) -> Vg f i = \0c).
  move=> i /setC_P [r1] /Zo_P r2; ex_middle h0; case: r2; split => //.
move: (csum_zero_unit sj qa) => h1; rewrite h1 in pg.
have h2: csum_of_small1 x (Lg j (Vg f)).
  split; [ fprops | by hnf; aw;move=> a ad; rewrite LgV//;apply: pe; apply: sj].
move: (csum_commutative1 h2) => [g []]; aw => ga gb gc gd.
have xsg: csum g = x by rewrite - gc. 
set z :=  (cardinal j).
have oz: ordinalp z by apply: OS_cardinal; apply: CS_cardinal.
have h3: cofinality_c_ex x z by exists g. 
move: (pc _  oz h3) => le2.
have le3: z <=c  cofinality_c x.
  move : (sub_smaller sj); rewrite pf -/z  card_card //; exact: (proj31 pa).
rewrite (oleA le2 (ocle le3)).
exists g; split => // i idg bad.
have : inc \0c (range (Lg j (Vg f))). 
  rewrite - gd;apply/(range_gP (proj1 ga)); ex_tac.
rewrite Lg_range => /funI_P [u uj]. 
by move: uj => /Zo_hi pdd pw; case: pdd.
Qed.


Lemma cofinality_c_pr3 x: infinite_c x -> 
 exists f, [/\ csum_of_small1 x f, domain f = (cofinality_c x), csum f = x
       & (allf f (fun z => \2c <=c z)) ].
Proof.
move => icx; move: (infinite_ge2 icx) => x1.
move: (cofinality_c_rw x1) => [pa pb pc].
move: pb => [f [[pd1 pd2] pe pf]].
move: (sum_of_sums (Vg f) (fun _:Set => \2c) (domain f)).
rewrite  csum_of_same csum_gr pf pe.
have ->: x +c \2c *c cofinality_c x = x.
  move: (csum_inf pa icx) => xx.
  by rewrite - csum_nn csumA xx xx.
move=> xv.
exists (Lg (cofinality_c x) (fun i => Vg f i +c \2c)); split.
- split; [ fprops | hnf; aw => i idf; rewrite LgV//].
  rewrite -pe in idf;move: (pd2 _ idf) => lt1.
  apply:csum_inf5 => //; apply: (clt_fin_inf finite_2 icx).
- by aw.
- done.
- hnf; aw; move=> i ic; rewrite LgV//; apply: csum_Mle0; fprops.
Qed.

Lemma cofinality_c_small x: cardinalp x -> (cofinality_c x) <=c x.
Proof.
move => cx.
case: (equal_or_not x \0c) => x0.
  by rewrite x0 cofinality_c_of0; apply:(cleR CS0).
case: (equal_or_not x \1c) => x1.
  by rewrite x1 cofinality_c_of1; apply cle_01.
by case: (cofinality_c_rw (cge2 cx x0 x1)).
Qed.

Lemma CS_cofinality_c x: cardinalp x -> 
  cardinalp (cofinality_c x).
Proof. by case /cofinality_c_small. Qed.

Lemma cofinality_c_finite x: \2c <=c x -> finite_c x ->
   cofinality_c x = \2c.
Proof.
move=> x1 fcx.
move: (cofinality_c_rw  x1) => [p3 p4 p5].
set y:= cofinality_c x.
have xnz :=(proj2 (clt_leT (clt_02) x1)).
move: p4 => [f [[q1 q2] df q3]].
case: (ord2_trichotomy (proj1 (proj31 p3))) => h.
    have dfe: domain f = emptyset by rewrite df h.
    by case: xnz; rewrite -q3 (csum_trivial dfe).
  have df1: domain f = singleton \0c by rewrite df h.
  have zc: inc \0c (domain f) by rewrite df1; fprops.
  move: (q2 _ zc); rewrite -q3 (csum_trivial1 df1). move =>[le1].
  by rewrite (card_card (proj31 le1)).
apply: (oleA) => //; apply: p5; first by apply: OS2.
have xB: natp x by apply /NatP.
move: (cpred_pr xB (nesym xnz)) => []; set p:= cpred x; move => p4 p5.
have lpx: p <c x by rewrite p5; apply: cltS.
have cp:= (proj31_1 lpx).
move: (esym p5); rewrite (csucc_pr4 cp).
rewrite (csum2_pr (doubleton_fam_variant p \1c C1_ne_C0)).
set g:=  (variantL _ _ _ _) => p7.
have dg : \2c = domain g by rewrite /g/variantL; aw.
have p6: forall i, inc i (domain g) -> Vg g i <c x.
   have aux:= (clt_leT clt_12 x1).
   by move => i; rewrite /g {1} /variantL; aw; case /set2_P => ->; aw.
exists g;split => //; split => //; rewrite /g/variantL; fprops.
Qed.


Lemma cofinality_infinite x: infinite_c x -> infinite_c (cofinality_c x).
Proof.
move=> icx; move: (infinite_ge2 icx) => x1.
move: (cofinality_c_rw x1) => [pc pd pe].
have cs:=proj31 pc.
case: (finite_or_infinite cs) => // cf.
move: (cf); rewrite - (card_card cs) -/(finite_set _) => fs.
move: pd => [f [[fa fb] fc fd]].
set E := fun_image (domain f) (fun z => Vg f z).
have fe: finite_set E by apply: finite_fun_image; ue.
have nee: nonempty E.
  apply:funI_setne; apply/nonemptyP => dfe.
  case: (infinite_nz icx);rewrite - fd; exact: (csum_trivial dfe). 
have cse: cardinal_set E.
  move=> t /funI_P [z zdf ->]; exact: (proj31_1 (fb _ zdf)).
move: (wordering_cle_pr cse) => [qa qb].
move: (finite_set_torder_greatest (worder_total qa)); rewrite qb => aux.
move: (aux fe nee)=> [t []]; rewrite qb => qc qd.
have tx: t <c x by move: qc => /funI_P [z0 /fb zd ->]. 
have  tx1: (allf f (cardinal_le^~ t)).
   move=> i idf; have vE: inc (Vg f i) E by apply /funI_P; ex_tac.
   by move: (qd _ vE) => /graph_on_P1 [_ _].
move: (csum_of_small_b1 (conj fa tx1)); rewrite fc => sc.
have ct:=proj31_1 tx.
case: (finite_or_infinite ct) => // fct.
  have fp: finite_c (t *c cofinality_c x).
    by  apply /NatP; apply: NS_prod; apply/NatP.
  by move: (clt_fin_inf fp icx); rewrite - {2} fd=> /(cleNgt sc).
move: (clt_fin_inf cf fct) => [le1 _].
move: (cprod_inf1 le1 fct) => sb.
by move: (cleT sc sb); rewrite fd => /(cltNge tx).
Qed.

Lemma infinite_regularP x: infinite_c x ->
  (regular_cardinal x <->
   forall f, csum_of_small1 x f -> cardinal (domain f) <c x -> csum f <c x).
Proof.
move => ix.
have ox: ordinalp x by move: ix => [[ok _] _].
have x2: \2c <=c x by apply: infinite_ge2.
move: (cofinality_c_rw x2) => [p3 [f [f1 f2 f3] p5]].
have cc:= proj31 p3.
split => h; last first.
  split;[exact | case:(cle_eqVlt p3) => //; rewrite -(card_card cc) -f2 => lt].
  by case: (proj2 (h f f1 lt)); rewrite f3.
move: h=> [_ rx] g gp [le1 ba].
move: (csum_commutative1 gp) => [h [h1 h2 h3 h4]].
split.
  move: (csum_of_small_b2 h1); rewrite - h3 h2  => p6.
  exact: (cleT p6 (cprod_inf1 le1 ix)).
move => cs; rewrite cs in h3; case: ba; apply: oleA.
  by move: (ocle le1).
rewrite - rx; apply: p5; [ by apply: OS_cardinal; fprops | by exists h].
Qed.


Lemma regular_alt_prop X x:
  fgraph X -> allf X (fun z => z <o x) -> (domain X) <o x ->
  regular_cardinal x ->
  osum (ordinal_o (domain X)) X <o x.
Proof.
move => fgX Xb dxb reg.
have icx := proj1 reg.
have H t: t <o x -> cardinal t <c x.
  by move => tx; apply/(ocle2P (proj1 icx) (proj31_1 tx)).
have od := proj31_1 dxb.
set r := (ordinal_o (domain X)).
have ha: worder_on r (domain X).
   split; [exact (ordinal_o_wor od) | by rewrite ordinal_o_sr ].
have ofX: ordinal_fam X by move => i /Xb [[]].
have os: ordinalp (osum r X) by apply: OS_sum.
apply/(ocle2P (proj1 icx) os); rewrite (osum_cardinal_gen ha ofX).
set f := (Lg (domain X) (fun z => cardinal (Vg X z))).
have : cardinal (domain f) <c x by rewrite /f; aw; apply:H.
have :csum_of_small1 x f. 
  by rewrite/f;split; fprops; hnf; aw => i idx; rewrite LgV//; apply:(H _ (Xb _ idx)).
by move /(infinite_regularP icx): reg; apply.
Qed.


Lemma regular_sup X b: 
   regular_cardinal b -> cardinal X <c b -> 
   (forall i, inc i X -> i <c b) -> \csup X <c b.
Proof.
move => ha hb hc.
have ic := proj1 ha.
set f := Lg X id.
have ra:csum_of_small1 b f. 
  by rewrite /f;split; fprops; hnf;aw; move => i ix; rewrite LgV//; apply: hc.
have cd: cardinal (domain f) <c b by rewrite /f; aw.
move /(infinite_regularP ic): ha => rb;  move: (rb _ ra cd); apply: (cle_ltT).
have CX: cardinal_set X by move => i /hc [[]].
move: (csum_pr1 f).
have ->: csumb (domain f) (fun a => cardinal (Vg f a)) = csum f.
   rewrite /f /csumb Lgd;apply:csumb_exten => i idx /=; rewrite LgV//.
   exact:(card_card (CX _ idx)).
by rewrite setUb_identity  (card_card (CS_sup CX)).
Qed.

Lemma regular_cardinal_omega: regular_cardinal omega0.
Proof.
move: CIS_omega => ico; split => //.
move: (cofinality_c_small (proj1 ico)) => [_ _ pa].
move: (omega_limit3 (cofinality_infinite ico)) => pb.
by apply: extensionality.
Qed.

Lemma regular_initial_successor x: ordinalp x ->
   regular_cardinal (\aleph (osucc x)).
Proof.
move => ox.
have osx:= (OS_succ ox).
have iy:= (CIS_aleph osx).
have y2:= (infinite_ge2 iy).
move: (cofinality_c_rw y2) =>  [pc [f [fa fb fc] _]]. 
split => //; case:(cle_eqVlt pc) => //.
rewrite - (card_card (CS_cofinality_c (proj1 iy))) - fb => h.
have en: (exists2 n, ordinalp n& \aleph (osucc x) = \aleph (osucc n))
  by exists x.
by case: (proj2(csum_of_small_b3 fa en h)). 
Qed.


Lemma regular_cnext x: infinite_c x ->
   regular_cardinal (cnext x).
Proof.
move/ord_index_pr1 => [sa <-].
rewrite (cnextE sa); exact:regular_initial_successor.
Qed.

Lemma regular_cardinal_aleph1: regular_cardinal aleph1.
Proof.
rewrite /aleph1 - osucc_zero; apply:(regular_initial_successor OS0).
Qed.

Definition aleph_succ_comp x := 
   (\aleph (osucc x)) -s (\aleph x).

Lemma aleph_succ_P1 x: ordinalp x ->
  (forall t, inc t  (aleph_succ_comp x) <->
     ((\aleph x) <=o t /\ t <o (\aleph (osucc x)))).
Proof.
move => ox t.
move: (aleph_lt_lto (oltS ox)) => lt1.
move: (lt1) => [[oy oy' _] _].
split.
  move /setC_P => [ta tb].
  have ot:= (Os_ordinal oy' ta).
  split; last by apply /oltP0;split => //.
  by case: (oleT_el oy ot) => //;move/oltP0 => [_ _].
move => [[p1 p2 p3] p4]; apply /setC_P; split => //.
  by move /(oltP0) : p4 => [_ _].
move => p5; exact:(ordinal_irreflexive p2 (p3 _ p5)).
Qed.

Lemma aleph_succ_pr2 x: ordinalp x ->
  cardinal (aleph_succ_comp x) = \aleph (osucc x).
Proof.
move => ox.
move:(CIS_aleph (OS_succ ox)) (aleph_lt_lto (oltS ox)) => sa sb.
exact (proj2 (cardinal_indecomposable1 sa sb)).
Qed.

Lemma aleph_succ_pr3 x y: ordinalp x -> ordinalp y -> 
  x = y \/ disjoint (aleph_succ_comp x) (aleph_succ_comp y).
Proof.
move=> ox oy.
case: (equal_or_not x y); [by left | move => h0; right;apply /set0_P => t]. 
move /setI2_P => [] /(aleph_succ_P1 ox) [pa pb] /(aleph_succ_P1 oy) [pc pd].
case: h0; apply: oleA; apply /oltSleP.
  by move: (aleph_lto_lt ox (OS_succ oy) (ole_ltT pa pd)).
by move: (aleph_lto_lt oy (OS_succ ox) (ole_ltT pc pb)). 
Qed.

Lemma aleph_sum_pr1 x: ordinalp x ->
  inc x omega0 \/ exists2 y, ordinalp y &  inc x (aleph_succ_comp y).
Proof.
move=> ox.
case: (normal_ofs_bounded ox aleph_normal) => h.
  by left; move: h;  rewrite -aleph0E; move /oltP0; move=> [_ _].
by move: h => [y [pa pb pc]]; right; exists y => //; apply /(aleph_succ_P1 pa).
Qed.

Lemma aleph_sum_pr2 x: ordinalp x ->
  \aleph x = omega0 +c csumb  x (fun z => \aleph (osucc z)).
Proof.
move=> ox.
have /cardinal_setC: sub omega0 (\aleph x).
  by move: (aleph_pr5 ox) => [_ _].
rewrite (card_card (CS_aleph ox)) (card_card (CS_omega)).
move => <-; congr (_ +c _); rewrite /cdiff.
have oa := OS_aleph ox.
have ->: ((\aleph x) -s omega0) = unionb (Lg x aleph_succ_comp).
  set_extens t.
    move /setC_P;move=> [pa pb]; move: (Os_ordinal oa pa) => ot.
    case: (aleph_sum_pr1 ot) => // [] [y oy ta].
    move /(aleph_succ_P1 oy): (ta) => [pc pd].
    suff yx: inc y x by  apply /setUb_P;  exists y; aw;trivial; rewrite LgV.
    have le1: t <o (\aleph x) by apply /oltP.
    by move:(aleph_lto_lt oy ox (ole_ltT pc le1)) => /oltP0[_ _].
  move=> /setUb_P; aw; move => [y yx]; rewrite (LgV yx).
  move/(oltP ox): yx => yx.
  have oy:=proj31_1 yx.
  move/(aleph_succ_P1 oy) => [p1 p2]; apply /setC_P; split.
    move /oleSltP: yx => /(aleph_le_leo) ca.
    by move: (olt_leT p2 ca) => /oltP0 [_ _].
  move: (oleT (aleph_pr5 oy) p1) =>  [q1 q2 q3] q4.
  exact: (ordinal_irreflexive q2 (q3 _ q4)).
apply: Eqc_disjointU; last by fprops.
  hnf; rewrite /disjointU_fam; split;aww.
  move=> i ix; rewrite !LgV//; aw.
  have oi:= (Os_ordinal ox ix).
  rewrite (aleph_succ_pr2 oi) card_card //. exact:(CS_aleph (OS_succ oi)).
red; aw; move=> i j ix jx; rewrite !LgV//.
by apply:  aleph_succ_pr3; apply: (Os_ordinal ox).
Qed.

Lemma aleph_sum_pr3 x: ordinalp x ->
  \aleph x = csumb (osucc x) \aleph.
Proof.
move=> ox.
set f:= (Lg (osucc x) \aleph).
have fgf: fgraph f by rewrite /f; fprops.
have tdf: (x +s1 x) = (domain f) by rewrite /f; aw.
have sd: sub (x +s1 x) (domain f) by rewrite tdf; apply: sub_refl.
have ni: not (inc x x) by apply: (ordinal_irreflexive ox).
move: (induction_sum0 f ni); rewrite /csumb.
have ->: restr f (x +s1 x) = f by rewrite tdf restr_to_domain //.
move=> ->; rewrite {2} /f LgV//; last by rewrite /osucc; fprops.
suff: (csum (restr f x)) <=c  (\aleph x).
   move=> h; symmetry; rewrite csumC; apply: csum_inf => //.
   by apply: CIS_aleph.
rewrite (aleph_sum_pr2 ox) /csumb.
set A := csum _; set B := csum _.
suff ab: A <=c B.
  apply: (cleT ab); apply: (csum_Mle0 _ (proj32 ab)).
have s1: sub x (osucc x) by  rewrite /osucc; fprops.
have sxd: sub x (domain f) by rewrite - tdf; fprops.
have dr: (domain (restr f x)) = x by aw.
apply: csum_increasing; aw; fprops.
move=> y yx; rewrite /f !LgV//; last by apply: s1.
by apply: aleph_le_lec; move: (oltS (Os_ordinal ox yx)) => [].
Qed.

Lemma aleph_sum_pr4 x E: limit_ordinal x ->
  sub E x -> \csup E = x ->
  \aleph x = csumb E \aleph.
Proof.
move=> [pa pb pc] Ex sE.
rewrite /csumb;set f := (Lg E \aleph); set y := csum f.
have Ep: forall i, inc i E -> \aleph i <c \aleph x.
  by move=> i ie; apply:aleph_lt_ltc ;apply /(oltP pa) /Ex.
have cf: cardinal_fam f.
  rewrite /f; hnf; aw; move=> i id; rewrite LgV//;exact: (proj31_1(Ep _ id)).
apply: cleA; last first.
  have pd: csum_of_small1 (\aleph x) f.
    rewrite /f;split;fprops; hnf; aw => i id; rewrite LgV//; exact (Ep _ id).
  move: (csum_of_small_b2 pd); rewrite {2} /f Lgd - cprod2cr.
  move: (sub_smaller (sub_trans Ex (proj33 (aleph_pr6 pa)))).
  rewrite (card_card (CS_aleph pa)).
  move=> qa qb; exact: (cleT qb(cprod_inf1 qa (CIS_aleph pa))).
have yg: forall t, inc t E ->  \aleph t <=c y.
  move=> t tE; have tdf: inc t (domain f) by rewrite /f Lgd.
  move: (csum_increasing6 (cf _ tdf) tdf); rewrite /f LgV//.
have osE: ordinal_set E by move=> t tE; exact (Os_ordinal pa (Ex _ tE)).
have iy: infinite_c y.
  case: (emptyset_dichot E).
    move=> ee; move: pb; rewrite - sE ee setU_0; case; case.
  move=> [t tE]; move: (yg _ tE) => le2.
  exact: (cle_inf_inf (CIS_aleph (osE _ tE)) le2).
move: (ord_index_pr1 iy) => [];set z := (ord_index y) => oz yv.
rewrite - yv; apply: aleph_le_lec.
rewrite - sE; apply: ord_ub_sup => //.
move=> t te; move: (yg _ te); rewrite -yv=> h; move: (ocle h).
apply: aleph_leo_le => //; exact  (osE _ te).
Qed.

Lemma aleph_sum_pr5 x: limit_ordinal x ->
  \aleph x = csumb x \aleph.
Proof.
by move => lx; apply:aleph_sum_pr4 => //;rewrite -[union _](limit_nonsucc lx).
Qed.

Definition fg_Mle_lec X := 
  (forall a b, inc a (domain X) -> inc b (domain X) -> a <=o b ->
    Vg X a <=c Vg X b).
Definition fg_Mle_leo X := 
  (forall a b, inc a (domain X) -> inc b (domain X) -> a <=o b ->
    Vg X a <=o Vg X b).
Definition fg_Mlt_lto X := 
  (forall a b, inc a (domain X) -> inc b (domain X) -> a <o b ->
    Vg X a <o Vg X b).
Definition fg_Mlt_ltc X := 
  (forall a b, inc a (domain X) -> inc b (domain X) -> a <o b ->
    Vg X a <c Vg X b). 

Definition ofg_Mlt_lto X := [/\ fgraph X, ordinal_fam X & fg_Mlt_lto X].
Definition ofg_Mle_leo X := [/\ fgraph X, ordinal_fam X & fg_Mle_leo X].

Lemma ofg_Mle_leo_os X: fgraph X -> ordinal_fam X -> ordinal_set (range X).
Proof. by move => h1 h2 t; move /(range_gP h1) => [x xd ->]; apply: h2. Qed.

Lemma ofg_Mle_leo_p1 X:
    fgraph X -> fg_Mle_leo X -> ordinalp (domain X) ->  ofg_Mle_leo X.
Proof.
move => pa pb pc; split => //.
move=> x xi; move: (oleR (Os_ordinal pc xi)) => xx.
apply: (proj31 (pb _ _ xi xi xx)).
Qed.

Lemma ofg_Mlt_lto_p1 X:
 fgraph X -> fg_Mlt_lto X -> limit_ordinal (domain X) -> 
  forall u, inc u (domain X) -> 
    (inc (osucc u) (domain X) /\ Vg X u <o Vg X (osucc u)).
Proof.
move=> pa pb [pc pd pe] u ud.
have lt1:= (oltS (Os_ordinal pc ud)).
move: (pe _ ud) => sb.
move: (pb _ _ ud sb lt1) => lt2; split => //.
Qed.

Lemma ofg_Mlt_lto_p2 X:
 fgraph X -> fg_Mlt_lto X -> limit_ordinal (domain X) ->  ofg_Mle_leo X.
Proof.
move => p1 p2 p3; move: (ofg_Mlt_lto_p1 p1 p2 p3) => p5.
have p51: (forall u, inc u (domain X) -> ordinalp (Vg X u)).
  by move => u ud; move: (p5 _ ud) => [_ [[ok _] _]].
split  => // u v ud vd uv.
case: (equal_or_not u v) => nuv.
- by move: (p51 _ ud) => h; rewrite -nuv; apply: oleR.
- exact (proj1 (p2 _ _ ud vd (conj uv nuv))).
Qed.

Lemma ofg_Mlt_lto_p3 X: 
  ofg_Mlt_lto X -> limit_ordinal (domain X) -> ofg_Mle_leo X.
Proof. by move=> [pa pb pc] pd; apply: ofg_Mlt_lto_p2. Qed.

Lemma increasing_sup_limit1 X (a:= \osup (range X)):
  ofg_Mle_leo X -> nonempty (domain X) ->
  (allf X (fun t => t <> a)) ->
  limit_ordinal a.
Proof.  
move=> [fgX pb pc] [x xd] pd.
move: (ofg_Mle_leo_os fgX pb) => osx.
have ner: nonempty (range X) by exists (Vg X x); apply /(range_gP fgX); ex_tac.
case: (ord_sup_inVlimit osx ner) => //.
by rewrite -/a; aw; move /(range_gP fgX)=> [t td av]; case: (pd _ td).
Qed. 

Lemma increasing_sup_limit2 X:
  ofg_Mlt_lto X -> limit_ordinal (domain X) ->
  limit_ordinal (\osup (range X)).
Proof.
move => pa pb.
have p9:=(ofg_Mlt_lto_p3 pa pb).
move: (p9) => [xa xb xc].
have osx:= (ofg_Mle_leo_os xa xb).
have ned: nonempty (domain X) by move: pb => [_ ok _]; ex_tac.
apply: (increasing_sup_limit1 p9 ned).
move: pa pb =>  [q1 q2 q3] [qa qb qc].
move => t td bad.
have lt1:= (oltS (Os_ordinal qa td)).
move: (qc _ td) => sb.
move: (q3 _ _ td sb lt1) => lt2.
have vr: inc (Vg X (osucc t)) (range X) by apply /(range_gP q1); ex_tac.
by move: (ord_sup_ub osx vr); rewrite - bad =>/(oltNge lt2). 
Qed.


Lemma sup_range_aleph X:
  fgraph X -> ordinal_fam X -> nonempty (domain X) ->
  \osup (range (Lg (domain X) (fun z => \aleph (Vg X z)))) =
    \aleph  (\osup (range X)).
Proof.
move => ha hb ned.
move /normal_ofs_equiv1: aleph_normal => [_ na].
have Ha: (forall x, inc x (range X) -> \0o <=o x).
  move => x /(range_gP ha) [i idx ->]; apply:(ole0x (hb _ idx)).
have Hb: nonempty (range X). 
  by case: ned => [x xd]; exists (Vg X x); apply: inc_V_range.
rewrite - (na (range X) Ha Hb);congr union; rewrite  Lg_range.
set_extens t.
  move=>/funI_P [z zdf ->]; apply/funI_P; exists (Vg X z) => //.
  by apply: inc_V_range.
  by move=>/funI_P [z /(range_gP ha) [s sa ->] ->]; apply:funI_i.
Qed.


Lemma increasing_sup_limit4 X (Y:= Lg (domain X) (fun z => \aleph (Vg X z)))
  (a := \osup (range X)):
  ofg_Mlt_lto X -> limit_ordinal (domain X) ->
  [/\ limit_ordinal a, sub (range X) a & \csup (range Y) = \aleph a].
Proof.
move => pa lb.
have [xa xb xc] := pa.
have osX:= (ofg_Mle_leo_os xa xb).
move: (increasing_sup_limit2 pa lb); rewrite -/a => la.
split.
- exact.
- move => t /(range_gP xa) [z sd ->].
  have [qa qb] := (ofg_Mlt_lto_p1 xa xc lb sd).
  have qc: Vg X (osucc z) <=o a. 
    by apply: ord_sup_ub => //; apply /(range_gP xa); ex_tac.
  apply /(oltP (proj31 la)); split.
    by apply: (ord_sup_ub osX) ; apply /(range_gP xa); exists z.
  by move => bad;case:(oltNge qb); rewrite bad.
apply:(sup_range_aleph xa xb); exists \0c; exact (proj32 lb).
Qed.


Lemma aleph_sum_pr6 X  (Y:= Lg (domain X) (fun z => \aleph (Vg X z)))
  (a := \osup (range X)):
  ofg_Mlt_lto X -> limit_ordinal (domain X) ->
   \aleph a = csum Y.
Proof.
move => pa pb.
move: (increasing_sup_limit4 pa pb); rewrite -/a; move => [pc pd pe].
rewrite (aleph_sum_pr4 pc pd (refl_equal a)).
have [fgx ox si] := pa.
have os: ordinal_set (domain X). 
   move => u ub; move: pb => [ob _ _]; exact: (Os_ordinal ob ub).
apply:csum_Cn2; split => //.
+ move => t tx; apply /(range_gP fgx); ex_tac.
+ move=> u v ud vd sv.
  case: (oleT_ell (os _ ud) (os _ vd)) => // lt.
  - by case: (si _ _ ud vd lt).
  - by case: (si _ _ vd ud lt); rewrite sv. 
+ move => y  /(range_gP fgx) [x xd eq]; ex_tac.
Qed.

(** ** Inaccessible cardinals *)


Definition cofinality_aux r := 
  (Zo (\Po
        (substrate r))
      (fun z => cofinal r z /\ worder (induced_order r z))).

Definition cofinality' r := (fun_image (cofinality_aux r) 
     (fun z => ordinal (induced_order r z))).



Lemma cofinality'_pr0 r : worder r ->
   (nonempty (cofinality' r) /\ ordinal_set (cofinality' r)).
Proof.
move => wor; move: (wor) => [or _].
set x := substrate r.
have cx: cofinal r x.
  by split => //  t tx; exists t => //; order_tac. 
have ior: (induced_order r x) = r by apply: iorder_substrate.
split.
  exists (ordinal r); apply /funI_P; exists x; last by ue.
  apply: Zo_i; [ by aw; apply: setP_Ti | by rewrite ior].
move=> t /funI_P [z pa ->]; apply: OS_ordinal;apply: induced_wor => //.
by move: pa => /Zo_P [] /setP_P.
Qed.


Lemma cofinality'_pr2 r (y:= (intersection (cofinality' r))) :
  worder r -> 
  (exists z, [/\ sub z (substrate r), cofinal r z, worder (induced_order r z) & 
      y = ordinal (induced_order r z)]).
Proof.
move=> /cofinality'_pr0  [pa pb].
move: (ordinal_setI pa pb).
rewrite /cofinality'; move=> /funI_P [z z1 z2].
by move: z1 => /Zo_P [pc [pd pe]]; exists z;split => //; apply /setP_P.
Qed.


Lemma cofinality'_pr3 r z (y:= (intersection (cofinality' r))):
  worder r -> sub z (substrate r) -> cofinal r z ->
  y <=o ordinal (induced_order r z).
Proof.
move=> wor zx cf.
move: (cofinality'_pr0 wor) => [pa pb].
move: (ordinal_setI pa pb) => ys.
set t := (ordinal (induced_order r z)).
have wot : worder (induced_order r z) by apply: induced_wor.
have ti: inc t (cofinality' r).
  apply /funI_P; exists z => //; apply: Zo_i => //; by apply /setP_P. 
split;fprops; by apply: setI_s1.
Qed.

Definition cofinality_alt x := 
  intersection (cofinality' (ordinal_o x)).

Lemma cofinality_pr1 x  (r:= ordinal_o x): 
  ordinalp x -> 
  (exists z, [/\ sub z x, cofinal r z, worder (induced_order r z) & 
      cofinality_alt x = ordinal (induced_order r z)]).
Proof. 
move => /ordinal_o_wor; rewrite -{2} (ordinal_o_sr x); apply:cofinality'_pr2.
Qed.

Lemma cofinality_pr2 x  (r:= ordinal_o x) z: 
  ordinalp x -> sub z x -> cofinal r z ->
  (cofinality_alt x) <=o ordinal (induced_order r z).
Proof.
move => /ordinal_o_wor; rewrite -{2} (ordinal_o_sr x);apply:cofinality'_pr3.
Qed.

Definition cofinal_function f x y :=
  function_prop f y x /\
  (forall t, inc t x -> exists2 z, inc z y & t <=o Vf f z).

Definition cofinal_function_ex x y:= exists f, cofinal_function f x y.

Definition cofinality x := least_ordinal (cofinal_function_ex x) x.

Notation "\cf x" := (cofinality x) (at level 49).

Lemma cofinal_function_pr2 a: ordinalp a -> cofinal_function_ex a a.
Proof.
move=> oa; exists (identity a); split; first by red; aw;split;fprops.
move=> x xa; exists x => //; rewrite idV //.
exact: (oleR (Os_ordinal oa xa)).
Qed.

Lemma cofinality_rw a (b:= \cf  a) :
  ordinalp a -> [/\ ordinalp b, cofinal_function_ex a b &
    forall z, ordinalp z -> cofinal_function_ex a z ->  b <=o z].
Proof.
set p := cofinal_function_ex a.
move=> oa.
have pa: p a by apply: cofinal_function_pr2.
move: (least_ordinal1 oa pa) => [pb pc pd];split => // z oz pz; split;fprops.
Qed.

Lemma  OS_cofinality a: ordinalp a -> ordinalp (\cf a).
Proof. by move=> oa; move: (cofinality_rw oa) => [ok _]. Qed.

Lemma cofinality_pr3 a: ordinalp a -> \cf a <=o a.
Proof.
move=> oa; move: (cofinality_rw oa) => [p1 p2 p3].
exact: (p3 _ oa (cofinal_function_pr2 oa)).
Qed.

Lemma cofinality0: \cf \0o = \0o.
Proof.
move: (cofinality_rw OS0) => [_ [f [[ff sf tf] _]] _].
rewrite - sf; apply /set0_P => y ysf.
by move: (Vf_target ff ysf); rewrite tf /ord_zero => /in_set0.
Qed.

Lemma cofinality_n0 x: ordinalp x -> x <> \0o -> \cf x <> \0o.
Proof.
move => ox xnz;move: (cofinality_rw ox) => [p1 [f [[ff sf tf] fp]] _] se.
case: xnz; apply /set0_P => y yx.
move: (fp _ yx) => [z]; rewrite se; case; case; case.
Qed.


Lemma cofinality_succ x: ordinalp x -> \cf (osucc x) = \1o.
Proof. 
move=> ox.
have osx: ordinalp (osucc x) by fprops.
have xsx: inc x (osucc x) by rewrite /osucc; fprops.
move: (cofinality_rw osx) => [p1 _ p2].
apply: oleA ; last first.
  apply:oge1 => //; exact: (cofinality_n0 osx (@osucc_nz x)). 
apply: (p2 _ OS1).
have ta: lf_axiom (fun _ : Set => x) \1o (osucc x) by move => t tc.
have i01:inc \0o \1o by rewrite / \1o / \1c; fprops.
exists ( Lf (fun z => x) \1o (osucc x)).
split; first by saw;  apply: lf_function.
by move=> t ts; exists \0o => //; rewrite LfV //; apply /oleP.
Qed.

Lemma cofinality1: \cf \1o = \1o.
Proof. rewrite - {1} osucc_zero; apply: (cofinality_succ OS0). Qed.

Lemma cofinality_limit1 n: ordinalp n ->
  ((\cf n = \1o) <-> exists2 m, ordinalp m & n = osucc m).
Proof.
move => on; split; last first.
   move=> [m om ->]; rewrite cofinality_succ //.
move => fc1.
move: (cofinality_rw on) => [_ [f [[ff sf tf] cf]] _].
move: sf cf; rewrite fc1 / \1o / \1c => sf cf.
set m := Vf f emptyset.
have mn: inc m n by rewrite -tf; apply: Vf_target => //; rewrite sf;fprops.
move: (Os_ordinal on mn) => om.
exists m => //.
case :(oleT_ell on (OS_succ om)) => //.  
  by move: mn => /(oltP on) pa /oltSleP => /(oltNge pa).
move /(oltP on) => /cf [z] /set1_P.
rewrite -/m;move=> -> h1;case: (oltNge (oltS om) h1).
Qed.

Lemma cofinality_limit2 x (y:= \cf x): ordinalp x ->
  y = \0o \/ y = \1o \/ limit_ordinal y.
Proof.
move=> ox; move: (cofinality_rw ox) => [oy pb pc].
case: (equal_or_not x \0o) => xnz.
  by rewrite /y xnz cofinality0; left.
case: (ordinal_limA oy); [by left | | by right; right ].
rewrite -/y; move=> [a oa ca]; right; left.
move: pb => [f [[ff sf tf ] cf]].
have ay: inc a y by rewrite ca /osucc; fprops.
have ay1: a <o y by apply /oltP.
have fax: inc (Vf f a) x by rewrite - tf; apply:Vf_target => //; ue.
have ow: ordinalp (Vf f a) by apply: (Os_ordinal ox).
case: (p_or_not_p (exists2 b, inc b a & Vf f a <=o Vf f b)) => h2.
  suff cfa: cofinal_function_ex x a.
    case move:(oltNge ay1 (pc _ oa cfa)).
  move: (ordinal_transitive oy ay); rewrite - sf => saf.
  exists (restriction f a).
  split.
    split => //; rewrite /restriction; aw; trivial.
      apply: (proj31(restriction_prop ff saf)).
  move => t tx; move: (cf _ tx) => [z ]; rewrite -/y ca => zs tv.
  case /setU1_P: zs => za; first by ex_tac; rewrite restriction_V //.
  move: h2 => [b ba le]; ex_tac.
  rewrite za in tv; rewrite restriction_V //; exact:(oleT tv le).
suff: x = osucc(Vf f a) by  rewrite /y; move ->; apply:cofinality_succ.
set_extens t.
  move => tx; move: (cf _ tx) => [z zy tz]; apply/(oleP ow).
  case: (equal_or_not z a) => za; first by ue.
  have iza: inc z a.
    apply /(oltP oa); split => //. 
    by apply /oltSleP; rewrite - ca; apply /(oltP oy).
  case: (oleT_ee ow (proj32 tz)) => xx;[ case: h2; ex_tac | exact: oleT tz xx].
move/(oltP ox):fax => lt1.
by move/(oleP ow) =>  le1; apply/(oltP ox); apply:(ole_ltT le1 lt1).
Qed.


Lemma cofinality_limit3 x: limit_ordinal x -> limit_ordinal (\cf x).
Proof.
move => [pa pb pc].
case: (cofinality_limit2 pa).
  have xnz: x <> emptyset by move =>h; move: pb; rewrite h; case; case.
  by move: (cofinality_n0 pa xnz).
case => //.
rewrite (cofinality_limit1 pa); move => [m om xs].
have mx: inc m x by rewrite xs /osucc; fprops.
by move: (pc _ mx); rewrite -xs => xx; case: (ordinal_decent pa xx).
Qed.

Lemma cofinality_limit4 x: limit_ordinal x -> omega0 <=o \cf x.
Proof.
move => h; move: (cofinality_limit3 h); apply: limit_ge_omega.
Qed.

Lemma dirim_restr2 f a: fgraph f -> sub a (domain f) ->
  direct_image (restr f a) a = direct_image f a.
Proof.
move => fgf df; move: (restr_fgraph f a)=> fgf'.
have df': sub a (domain (restr f a)) by rewrite restr_d.
by rewrite - (dirim_restr fgf' df') -(dirim_restr fgf df) double_restr //. 
Qed.

Lemma cofinality_pr4 x (y:= \cf x): ordinalp x -> 
   exists2 f, (cofinal_function f x y /\ normal_function f y x) &
        (inc \1o y -> Vf f \0o = \0o).
Proof.
move => ox.
move: (cofinality_rw ox); rewrite -/y;move => [oy [g cg gmin]].
case: (ordinal_limA ox) => lx.
    move: cg; rewrite /y lx cofinality0 => cg; move: (cg) => [pa _].
    exists g; first (split => //;split => // a; first move =>  b); case; case.
  move: lx cg => [t ot ts]; rewrite /y ts cofinality_succ.
  exists g; last by move => h; case: (ordinal_irreflexive OS1 h).
  split => //; move: cg => [pa pb]; split => //.
    - by move => a b /set1_P -> /set1_P -> [_].
    - by move => a /set1_P -> /limit_nz.
  by apply: OS_succr; ue.
move: (cofinality_limit3 lx) => ly.
move: cg => [[fg sg tg] cfg].
move: (lx) => [_ xnz lx1].
move: (ordinal_o_wor oy); set r := ordinal_o _ => wor.
have sr: substrate r = y by rewrite /r ordinal_o_sr.
pose unsrc f:= Yo (inc (domain f) y) (domain f) \0o.
have cp3: forall a, inc (unsrc a) y.
  move=> a; rewrite /unsrc; Ytac h => //; exact (proj32 ly).
pose coex v :=  (Yo (inc v x) v \0o).
pose coer1 v u := (Yo (v <=o u) u v).
pose coer a ga fa su := coex (Yo (osuccp a) (coer1 ga (osucc fa)) su).
pose p f := let a := unsrc f in coer a (Vf g (opred a)) (Vg f (opred a)) 
   (\osup (direct_image f a)).
move: (transfinite_pr1 p wor); rewrite /transfiniteg_def sr.
set f:= transfiniteg_defined r p; move=>  [ff sf tfp].
have oty := (ordinal_transitive oy).
have sfa a: inc a y -> sub a (domain f) by move=> /oty ay; rewrite sf. 
set T := direct_image f. 
have cp4: forall a, inc a y -> 
   Vg f a = coer a (Vf g (opred a)) (Vg f (opred a)) (\osup (T a)).
  move=> a ay.
  rewrite (tfp _ ay) /p /unsrc restr_d (ordinal_segment oy ay); Ytac0.
  rewrite /coer; case: (p_or_not_p (osuccp a)) => aux2; Ytac0; Ytac0.
    by move: (succ_i (opred a)); rewrite (predo_K aux2) => /(restr_ev f) ->.
  by rewrite (dirim_restr2 ff (sfa _ ay)).
have ta: lf_axiom (Vg f) y x.
  by move => t /cp4 ->; rewrite /coer /coex; Ytac xx.
have srg: sub (range f) x by move => t /(range_gP ff) [z zs ->]; apply: ta; ue.
have taa: forall a, inc a y -> lf_axiom (Vg f) a x.
  move=> a ay t /(oty _ ay); apply: ta.
set h:= Lf (Vg f) y x. 
have hp a: inc a y -> Vf h a = Vg f a by  move => asf; rewrite /h LfV.
have fsv: forall b, inc b y -> inc (osucc b) y ->
    Vg f (osucc b) = coer1 (Vf g b) (osucc (Vg f b)).
  move=> b iby siby; rewrite (cp4 _ siby) /coer. 
  move: (Os_ordinal oy iby) => ob.
  have isb: (osuccp (osucc b)) by exists b. 
  Ytac0; rewrite  (succo_K ob).
  rewrite /coex Y_true//  /coer1; Ytac aux; first by apply: lx1; apply: ta. 
  rewrite -tg; apply: Vf_target => //; ue.
have noovf: forall a, inc a y -> inc (\osup (T a)) x.
  move => a ay.
  have ax := (taa _ ay).
  have pa:= (sub_trans (@dirim_Sr f a) srg).
  have ost:(ordinal_set (T a)) by move => t tT;apply:(Os_ordinal ox  (pa _ tT)).
  case:(oleT_el ox (OS_sup ost)); [move => xb |  by move/(oltP ox)].
  suff: cofinal_function_ex x a.
     have le2: (a <o y) by apply /oltP.
     by move /(gmin _ (Os_ordinal oy ay)) => /(oltNge le2).
  exists (Lf (Vg f) a x); split.
    hnf;saw; by apply: lf_function.
  move => t itx.
  move /(oltP ox):(itx) => ltx; move:(olt_leT ltx xb) => ltb.
  move:(olt_sup ost ltb) => [z zT /proj1 ltz].
  move: (zT) => /(dirim_P) [v va /(in_graph_V ff) /pr2_def zv]; ex_tac.
  by move: zv;aw; rewrite LfV// => <-.
have nf1:  (forall a, inc a y -> ~(osuccp a) ->  Vg f a = \osup (T a)).
  move=> a ay ni; rewrite (cp4 _ ay) /coer /coex; Ytac0.
  by rewrite (Y_true (noovf _ ay)).
have si1: forall a, inc a y -> Vg f a <o Vg f (osucc a).
  move=> a ay.
  have o1: ordinalp (Vf g a). 
    apply: (Os_ordinal ox); rewrite - tg; apply: Vf_target=> //; ue.
  have o2: ordinalp (osucc (Vg f a)).
    by apply: OS_succ;apply: (Os_ordinal ox); apply: (ta _ ay).
  rewrite  (fsv _ ay (proj33 ly _ ay)) /coer1;apply /oleSltP.
  case: (oleT_el o1 o2) => le1; first by  Ytac0; exact: (oleR (proj32 le1)).
  rewrite (Y_false (oltNge le1)); exact (proj1 le1).
have fh: function h by  apply:lf_function.
have fyx:function_prop h y x by rewrite /h; saw.
have nf: normal_function h y x.
  apply: ord_sincr_cont_propv => //.
    by move => a ay; rewrite (hp _ ay) (hp _ (proj33 ly _ ay)); apply: si1.
  move => a ay la; rewrite (hp _ ay) (nf1 _ ay  (limit_nonsucc' la)).
  by rewrite /T /Vfs /h /Lf corresp_g - sf (Lg_recovers ff).
exists h; last first.
  have n0z: ~ (osuccp \0o) by move => [u _ uu];case: (@osucc_nz u).
  move:(proj32 ly) => y0;  rewrite (hp _ y0) (nf1 _ y0 n0z) => _.
  suff: T \0o = emptyset by  move ->; rewrite setU_0.
  by apply/set0_P => t /dirim_P [z /in_set0].
split => //; split => //.
move => t tx; move: (cfg  _ tx) => [a ay tw]. 
move:(proj33 ly _ ay) => cy; ex_tac.  rewrite (hp _ cy) (fsv _ ay cy).
rewrite /coer1. Ytac hh  => //; apply: (oleT tw hh).
Qed.


Lemma cofinality_sd a: ordinalp a ->
  (cofinality a) = (cofinality_alt a).
Proof.
move => oa.
move: (ordinal_o_wor oa) => woa; move: (woa) => [ora _].
have ofa: ordinalp (cofinality_alt a).
 move: (cofinality'_pr0 woa) => [pa pb].
 exact: (pb _ (ordinal_setI pa pb)).
have ocfa: ordinalp (cofinality a) by apply: OS_cofinality.
apply: oleA.
  move: (cofinality_pr1 oa) => [z [za cfz woz xx]].
  move: cfz => [pb pc].
  move: (cofinality_rw oa) => [pa _ h] => //.
  suff cex:  cofinal_function_ex a (cofinality_alt a) by exact: (h _ ofa cex).
  move: (orderIS (ordinal_o_is woz)); rewrite -xx.
  move => [f isf].
  move: (isf) =>  [o1 o2 [[[ff _] sjf] sf tf] isfo].
  rewrite (ordinal_o_sr a) in pc.
  rewrite (ordinal_o_sr (cofinality_alt a)) in sf.
  have zs: sub z (substrate (ordinal_o a)) by rewrite ordinal_o_sr.
  move: tf; rewrite iorder_sr // => tf.
  set g:= Lf (Vf f) (cofinality_alt a) a.
  have ax: lf_axiom (Vf f) (cofinality_alt a) a.
     rewrite - sf;move=> t ts; apply: za; rewrite - tf; fprops.
  exists g;red; rewrite /g; split. 
    by red;saw; apply: lf_function.
  move=> x xa; move: (pc _ xa) => [u uz xu].
  rewrite -tf in uz.
  move: ((proj2 sjf) _  uz) => [y ysf wu]; rewrite sf in ysf.
  exists y=> //;rewrite LfV // - wu.
  move: xu => /ordo_leP [_ ua xu].
  by split => //; apply: (Os_ordinal oa).
move: (cofinality_pr4 oa) => [f [[[ff sf tf] cfa] [_ sif _ _]]].
set z:= Imf f.
have za: sub z a by rewrite -tf; apply: Imf_Starget.
have  zc:  cofinal (ordinal_o a) z.
   rewrite /cofinal (ordinal_o_sr a).
   split => //; move=> x xa; move: (cfa _ xa) => [y ya yp].
   have wb: inc (Vf f y) a by rewrite -tf; apply: Vf_target => //;ue.
   exists (Vf f y).
     apply /(Imf_P ff); exists y => //; ue.
   apply /ordo_leP;split => //; by move: yp; move=> [_ _].
move: (cofinality_pr2 oa za zc).
set o1:= (induced_order (ordinal_o a) z).
have z1: sub z (substrate (ordinal_o a)) by rewrite ordinal_o_sr //.
suff is1:  (ordinal_o (cofinality a)) \Is o1.
  have wo1: worder (ordinal_o (cofinality a)) by fprops.
  have wo2: worder o1 by apply: induced_wor => //.
  by move: (ordinal_o_isu1 wo1 wo2 is1); rewrite ordinal_o_o // => ->.
have so1: substrate o1 = z by rewrite /o1 iorder_sr //.
set g:= restriction_to_image f.
have sg1: source g = source f 
    by rewrite /g /restriction_to_image /restriction2; aw.
have sg: substrate (ordinal_o (cofinality a)) = source g.
   rewrite sg1 ordinal_o_sr //. 
have tg:  substrate o1 = target g.
  by rewrite /g /restriction_to_image /restriction2 so1; aw.
have bg: bijection g.
  apply: restriction_to_image_fb.
  split => //;  rewrite sf;move=> x y xsf ysf => sw.
  have ox:=(Os_ordinal ocfa xsf).
  have oy:= (Os_ordinal ocfa ysf).
  case: (oleT_ell ox oy) => // h.
      by move: (sif _ _ xsf ysf h) => [_ bad].
  move: (sif _ _ ysf xsf h) => [_ bad]; by case: bad.
exists g; split;fprops; first by rewrite /o1; apply: (proj1 (iorder_osr _ _)).
  done.
have ra: restriction2_axioms f (source f) (Imf f) by split => //; ue.
red;rewrite sg1 => x y xsg ysg.
rewrite /g /restriction_to_image restriction2_V //  restriction2_V //.
have wxz: inc (Vf f x) z by apply /(Imf_P ff);  exists x.
have wyz: inc (Vf f y) z by apply /(Imf_P ff);  exists y.
have wxfa: inc (Vf f x) a by apply: za.
have wyfa: inc (Vf f y) a by apply: za.
rewrite sf in xsg ysg. 
have ox:=(Os_ordinal ocfa xsg).
have oy:=(Os_ordinal ocfa ysg).
split.
  move /ordo_leP => [qa qb qc]; apply /iorder_gle0P => //; apply /ordo_leP.
  split => //.
  have h: x <=o y by [].
  case: (equal_or_not x y) => xy; first by rewrite xy; fprops.
  by move: (sif _ _ xsg ysg (conj h xy)) => [[_ _ k] _].
move  /(iorder_gle0P _ wxz wyz) => h.
case: (oleT_el ox oy); first by move =>  [_ _ h1]; apply /ordo_leP. 
move => h1; move: (sif _ _ ysg xsg h1) => h2.
case:(oltNge h2).
have [[ofy ofx _] _] := h2.
by move: h; move /ordo_leP => [_ _ h3].
Qed.


Lemma cofinality_least_fp_normal x y f:
  normal_ofs f -> f x <> x ->  least_fixedpoint_ge f x y ->
  \cf y = omega0.
Proof.
move=> nf fx [lexy fy fz].
move: (lexy) => [ox oy _].
move: (induction_defined_pr f x).
set g := induction_defined f x; move=> [sg [fg sjg] gz gnz].
have yv : y = \osup (target g).
  move: (normal_ofs_fix nf ox) => [pa pb pc].
  by apply: oleA; [apply:fz | apply: pc ].
have xi: inc x (target g) by rewrite -gz; Wtac; rewrite sg; apply:NS0.
have ne: nonempty (target g) by exists x.
have lt1: forall n, natp n -> Vf g n <o y.
   apply: Nat_induction.
     by rewrite gz; split => //; dneg xx; rewrite xx.
   by move=> n nB; rewrite (gnz _ nB) => pd; move: ((proj1 nf) _ _ pd); ue.
have otg: ordinal_set (target g).
  move => t itg; move: (sjg _ itg) => [j jsg ->].
  rewrite sg in jsg;  exact:(proj31_1 (lt1 _ jsg)).
case: (ord_sup_inVlimit otg ne); rewrite - yv.
  move => itg; move: (sjg _  itg).
  by rewrite sg; move=> [j jB eq]; move: (lt1 _ jB) =>[]; rewrite eq.
move => ly.
set g0:= Lf (Vf g) omega0 y.
have cg: cofinal_function g0 y omega0.
  have la: lf_axiom (Vf g) omega0 y by move => t /lt1 /(oltP oy).
  rewrite /g0; split; first by saw; apply: lf_function.
  move=> t ty; ex_middle tm.
  have ot: ordinalp t by apply: (Os_ordinal oy ty).
  suff e: y <=o t by move: ty =>/(oltP oy) /(oleNgt e).
  rewrite yv;apply: ord_ub_sup => // i itg;  move: (sjg _  itg). 
  rewrite sg ; move => [u usg v].
  have ow: ordinalp i by  apply: otg.
  case: (oleT_ee ot ow) => // ti; case: (tm); exists  u => //.
  by rewrite /g0 LfV//  -v. 
move: (cofinality_rw oy) => [pd pe pf].
have pg: (cofinal_function_ex y omega0)  by exists g0.
move: (pf _ OS_omega pg) => le1.
exact: (oleA le1(limit_ge_omega (cofinality_limit3 ly))).
Qed.

Lemma normal_function_fixpoints x f:
  ordinalp x -> normal_function f x x ->
  (\cf x <> omega0) ->
  (forall a, inc a x -> exists b, [/\ inc b x, a <=o b & Vf f b = b]).
Proof.
move=> ox nf cfx a ax.
move/(oltP ox) :ax => ax1.
move: (normal_function_fix nf ax1); set y := the_least_fixedpoint_ge _ _.
case; last by move => [ay /(oltP ox) yx fy _]; ex_tac.
move => yx; case: cfx.
move:nf => [[ff sf tf] sif nff].
move: (induction_defined_pr (Vf f) a).
set g := induction_defined (Vf f) a; move=> [sg [fg sjg] gz gnz].
have xi: inc a (target g) by rewrite -gz; Wtac; rewrite sg; apply:NS0.
have ne: nonempty (target g) by exists a.
have lt1: forall n, natp n -> Vf g n <o x.
   apply: Nat_induction; first by rewrite gz. 
   move=> n nB; rewrite (gnz _ nB) => /(oltP ox) pd; apply /(oltP ox).
   rewrite - tf;Wtac.
have otg: ordinal_set (target g).
  move => t itg; move: (sjg _ itg) => [j jsg ->].
  rewrite sg in jsg; exact: (proj31_1 (lt1 _ jsg)).
case: (ord_sup_inVlimit otg ne).
  by rewrite sg in sjg; move => /sjg [j /lt1 [_ xx] eq]; case: xx; rewrite - eq.
rewrite /g -/( the_least_fixedpoint_ge _ _) -/y yx => ly.
set g0:= Lf (Vf g) omega0 x.
have cg: cofinal_function g0 x omega0.
  have la: lf_axiom (Vf g) omega0 x by move => t /lt1 /(oltP ox).
  rewrite /g0; split; first by saw; apply: lf_function.
  move=> t ty; ex_middle tm.
  have ot: ordinalp t by apply: (Os_ordinal ox ty).
  suff e: x <=o t by move: ty =>/(oltP ox)/(oleNgt e).
  rewrite - yx;apply: ord_ub_sup => // i itg;  move: (sjg _  itg). 
  rewrite sg ; move => [u usg v].
  have ow: ordinalp i by  apply: otg.
  case: (oleT_ee ot ow) => // ti; case: tm; exists  u => //.
  by rewrite /g0 LfV// -v. 
move: (cofinality_rw ox) => [pd pe pf].
have pg: (cofinal_function_ex x omega0)  by exists g0.
move: (pf _ OS_omega pg) => le1.
exact (oleA le1 (limit_ge_omega (cofinality_limit3 ly))).
Qed.




Definition regular_ordinal x := ordinalp x /\ \cf x = x.
Definition singular_ordinal x := ordinalp x /\ not (regular_ordinal x).

Lemma regular_0: regular_ordinal \0o.
Proof. move: OS0 => oo; split => //; exact cofinality0. Qed.

Lemma regular_1: regular_ordinal \1o.
Proof. move: OS1 => oo; split => //; exact cofinality1. Qed.

Lemma regular_finite x: 
   regular_ordinal x -> [\/ x = \0o, x = \1o | omega0 <=o x].
Proof.
move => [ox rx].
case: (ordinal_limA ox) => aux; first by constructor 1.
  constructor 2.
  move: aux => [y _ xs].
  move:rx; rewrite {1} xs cofinality_succ //; apply: OS_succr; ue.
constructor 3;exact (limit_ge_omega aux).
Qed.

Lemma cofinality_pr5 a b: 
  ordinalp a -> ordinalp b -> 
  (exists2 f, cofinal_function f b a & sincr_ofn f a) ->
  \cf a = \cf b.
Proof.
move=> oa ob [f cf sif].
move: (cofinality_rw oa) => [pa pb pc].
move: (cofinality_rw ob) => [pd pe pf].
move: cf => [[ff sf tf] cf].
rewrite - sf in sif.
have sif1 : forall x y, inc x a -> inc y a -> x <=o y -> Vf f x <=o Vf f y.
  rewrite - sf;move=> x y xa ya xy.
  case: (equal_or_not x y) => exy.
       rewrite exy; apply: oleR; apply: (Os_ordinal ob).
    by rewrite -tf;apply: Vf_target.
  by move: (sif _ _ xa ya (conj xy exy)) => [ok _].
have aux1: (cofinal_function_ex b (cofinality a)).
  move: pb => [g [[fg sg tg] cg]]. 
  have cp:  (f \coP g) by split => //; ue.
  exists (f \co g); split; first by saw; fct_tac.
  move => x xb.
  move: (cf _ xb) => [y ya xf].
  move: (cg _ ya) => [z zf lzg].
  have zg: inc z (source g) by ue.
  exists z => //; rewrite compfV //; apply: (oleT xf); apply: sif1 => //.
  rewrite -tg; fprops.
apply: oleA; last by apply: (pf _ pa aux1).
move: pe => [g [[fg sg tg] cg]].
pose h x := intersection (Zo a (fun y => Vf g x <=o Vf f y)).
have hp: forall x, inc x (cofinality b) ->
   (inc (h x) a /\  Vf g x <=o Vf f (h x)).
  rewrite - sg; move => x xf; rewrite /h; set E := Zo _ _.
  have osE: ordinal_set E by move => t/Zo_S /(Os_ordinal oa).
  have vt: inc (Vf g x) b by Wtac.
  move: (cf _ vt) => [y y1 y2].
  have ne: nonempty E by exists y; apply:Zo_i.
  by move/Zo_P:(ordinal_setI ne osE).
have ta: lf_axiom h (cofinality b) a.
  by move=> t ta; move: (hp _ ta) => [].
apply: (pc _ pd); exists (Lf h (cofinality b) a).
split; first by red; saw; apply: lf_function.
move => u ua.
have wxb: inc (Vf f u) b by rewrite - tf; apply: Vf_target => //; ue.
move: (cg _ wxb) => [y yb le1]; move: (hp _ yb) => [p1 p2].
exists y => //; rewrite LfV //. 
have le2:=oleT le1 p2.
have o1:=(Os_ordinal oa ua).
have o2:=(Os_ordinal oa p1).
case: (oleT_el o1 o2) => // uy.
rewrite sf in sif; case: (oleNgt le2 (sif _ _ p1 ua uy)).
Qed.

Lemma cofinality_proj x: ordinalp x -> \cf (\cf x) = \cf x.
Proof.
move=> ox; move: (OS_cofinality ox) => ofx.
apply: (cofinality_pr5 ofx ox).
by move: (cofinality_pr4 ox) => [f [ff [_ si _ _]]]; exists f.
Qed.

Lemma cofinality_reg x: ordinalp x -> 
   regular_ordinal (\cf x).
Proof.
move=> ox; move:  (OS_cofinality ox) => ofx.
split => //; apply: (cofinality_proj ox).
Qed.

Lemma regular_omega: regular_ordinal omega0.
Proof.
move: OS_omega => oo; split => //; apply: oleA.
  exact (cofinality_pr3 oo).  
exact: (cofinality_limit4 omega_limit).
Qed.

Lemma cofinality_sum a b: ordinalp a -> \0o <o b ->
  \cf (a +o b) = \cf b.
Proof.
move=> oa bnz; symmetry.
have b0: inc \0o b by move/oltP0:bnz => [].
have ob:= proj32_1 bnz. 
have oab: ordinalp (a +o b) by fprops.
have ta: lf_axiom (osum2 a) b (a +o b).
  by move=> t /(oltP ob) tb; apply /(oltP oab); apply: osum_Meqlt.
apply: cofinality_pr5 => //.
exists (Lf (osum2 a) b (a +o b)); last first.
  by move=> x y xb yb; rewrite !LfV// => h; apply: osum_Meqlt.  
split;first by saw; apply: lf_function.
move => t /(oltP oab) tab; move:(proj31_1 tab) => ot.
case: (oleT_ee ot oa) => lta.
  ex_tac; rewrite LfV //;by rewrite (osum0r oa).
move: (odiff_pr lta)=> [da db].
have b1: inc (t -o a) b. 
  by apply /(oltP ob); apply: (osum_Meqltr da ob oa); rewrite - db.
ex_tac; rewrite LfV// - db; fprops.
Qed.

Lemma cofinality_prod a b: \0o <o a -> limit_ordinal b ->
 \cf (a *o b) = \cf b.
Proof.
move=> ap bl; symmetry.
move: (ap) (bl) => [[_ oa _] _] [ob _ lb].
have oab: ordinalp (a *o b) by fprops.
have ta: lf_axiom (oprod2 a) b (a *o b).
  by move=> t /(oltP ob) tb; apply /(oltP oab); apply: oprod_Meqlt.
apply: cofinality_pr5 => //.
exists (Lf (oprod2 a) b (a *o b)); last first.
  by move=> x y xb yb; rewrite !LfV// => h; apply: oprod_Meqlt. 
split; first (by saw; apply: lf_function); last first.
move => t /(oltP oab) tab.
have ot:=proj31_1 tab.
move: (odivision_exists oa ob tab) => [[oq or p3 [p4 _]] /(oltP ob)].
move => /lb qd; ex_tac; rewrite LfV //.
rewrite oprod2_succ // {1}p3; apply: osum_Meqle; fprops.
Qed.

Lemma cofinality_prod_omega a: \0o <o a -> \cf (a *o omega0) = omega0.
Proof.
move => oa.
rewrite (cofinality_prod oa  omega_limit); exact: (proj2 regular_omega). 
Qed.

Lemma regular_indecomposable x: 
   regular_ordinal x -> (x = \0o \/ indecomposable x).
Proof.
move => [ox rx]; case: (ozero_dichot ox) => xnz; first by left.
right; split => // u v [[ou _ _] unx] vx eq.
have ov:= proj31_1 vx. 
case: (ozero_dichot ov) => vnz.
   move: eq; rewrite vnz osum0r //.
case: (oleNgt(cofinality_pr3 ov)).
by move: (cofinality_sum ou vnz); rewrite eq rx => <-. 
Qed.


Lemma regular_indecomposable1 x: 
   regular_ordinal x -> [\/ x = \0o, x= \1o,  x =omega0  |
   exists2 y, limit_ordinal y & x = omega0 ^o y]. 
Proof.
move=> rx; case: (regular_indecomposable rx) => ix; first by constructor 1.
move: (indecomp_prop3 ix) rx => [y oy ->] [_ ha].
case: (ordinal_limA oy) => h; first by rewrite h oopow0; constructor 2.
  move: h => [t ot st].
  move: OS_omega => oo.
  move: (OS_oopow ot) (oopow_pos ot) => op tbz.
  move: (cofinality_prod_omega tbz); rewrite - (opow_succ oo ot) - st ha.
  by move => hb;constructor 3.
by constructor 4; exists y.
Qed.

Lemma CS_cofinality x: ordinalp x -> cardinalp (\cf x).
Proof.
move => ox.
move: (cofinality_rw ox) => [pa [g [[fg sg tg] gc]] pc]; split => //.
move=> z oz e; move: (EqS e)=> [f [[[ff _] sjf] sf tf]].
suff H:  (cofinal_function_ex x z) by exact (proj33 (pc _ oz H)).
have cop: g \coP f by split => //; ue. 
exists (g \co f); split; first by red; saw;  fct_tac.
move => t tx; move: (gc _ tx) => [u]; rewrite -tf => utf tu.
move: ((proj2 sjf) _ utf) => [v vsf vv].
rewrite - sf; ex_tac; rewrite compfV//; ue.
Qed.


Lemma cofinality_limit_countable x: limit_ordinal x -> countable_ordinal x ->
   \cf x = omega0.
Proof.
move => ha [hb /countableP hc]; apply: oleA.
  move: (ocle (cleT (ocle1 (cofinality_pr3 hb)) hc)).
  by rewrite (card_card(CS_cofinality hb)).
exact:(limit_ge_omega (cofinality_limit3 ha)).
Qed.


Lemma cofinality_pr8 x z: ordinalp x -> sub z x -> \osup z = x ->
   \cf x <=c cardinal z.
Proof.
move =>ox zx szx.
set r := ordinal_o x.
move: (ordinal_o_wor ox) => wor.
have sr: substrate r = x by apply: ordinal_o_sr.
have sr1: sub z (substrate r) by ue.
move: (induced_wor wor sr1) => woz; move: wor => [or _].
have crz: cofinal r z.
  hnf; rewrite sr;split => // t /(oltP ox) tx.
  have osx: ordinal_set z by move => u / zx /(Os_ordinal ox).
  rewrite - szx in tx. 
  move:(olt_sup osx tx) => [a az av]; ex_tac.
  move: (zx _ az) => ax.  
  move /(oltP (Os_ordinal ox ax)): (av) => ta.
  move: (ordinal_transitive ox ax ta) => itx.
  by apply/ordo_leP; split => //; move: av => [[_ _ ok] _].
move:(cofinality_pr2 ox zx crz); rewrite - (cofinality_sd ox).
move/ocle1.
rewrite (card_card (CS_cofinality ox)). 
rewrite (cardinal_of_ordinal woz) iorder_sr //.
Qed.

Lemma regular_is_cardinal x: regular_ordinal x -> cardinalp x.
Proof. by move=> [ox <-]; apply: CS_cofinality. Qed.

Lemma cofinality_infinite_limit x: 
   limit_ordinal x -> infinite_c (\cf x).
Proof.
move=> ix; split; first by apply: (CS_cofinality (proj31 ix)).
apply: OIS_limit; apply: (cofinality_limit3 ix).
Qed.

Lemma cofinality_infinite_cardinal x: 
   infinite_c x -> infinite_c (\cf x).
Proof.
move=> ix; apply: (cofinality_infinite_limit (infinite_card_limit2 ix)).
Qed.


Lemma cofinality_card x: infinite_c x ->
  cofinality_c x = cofinality x.
Proof.
move=> icx.
move: (icx) => [cx _]; move: (cx)=> [ox _].
move: (CS_cofinality ox)  (cofinality_pr3 ox) => ca cb.
move:  (cofinality_c_rw (infinite_ge2 icx)) => [p3 p4 p5].
apply: oleA.
  move: (OS_cofinality ox) => sa; apply: p5 => //.
  move:(cofinality_pr4 ox) => [f [[[ff sf tf] cff] _] _].
  set g := Lg (\cf x) (fun z => cardinal (Vf f z)).
  have pa: csum_of_small1 x g.
    rewrite /g; split; fprops; hnf; aw => t tsf; rewrite LgV//.
    have pa: Vf f t <o x by apply /(oltP ox); rewrite - tf; Wtac.
     apply/ocle2P => //; exact: (proj31_1 pa).
  have pb: domain g = \cf x by rewrite /g; aw.
  have pc: \cf x <=c x by apply:ocle3.
  exists g; split => //; apply: cleA.
    move: (cprod_inf1 pc icx)(csum_of_small_b2 pa);rewrite pb.
    move => ca' cb'; exact:(cleT cb' ca').
  set f1 := Lg (\cf x) (Vf f).
  have <-: cardinal (unionb f1) = x.
     rewrite - (card_card cx); congr cardinal; rewrite /f1;set_extens t.
       move /setUb_P;aw;move =>[y ydf]; rewrite LgV// => tv.
       have pd: inc (Vf f y) x by rewrite - tf; Wtac.
       exact (ordinal_transitive ox pd tv).
    move: (infinite_card_limit2 icx) => [_ _ lx].
    move /lx /cff => [z za /oleSltP zb]; apply/setUb_P; aw; ex_tac. 
    by rewrite LgV//; move/ oltP0: zb => [_ _].
  have <-: csumb (domain f1) (fun a => cardinal (Vg f1 a)) = csum g.
    rewrite /csumb/f1/g; aw; congr csum; apply:Lg_exten.
    by move => t tdf /=; rewrite !LgV.
  by move: (csum_pr1 f1).
move: p4 => [f [[qa qb] df q3]]; move: (p3) => [[ocfx _ _] _].
set T := fun_image (domain f) (Vg f).
have Ts: forall a, inc a T -> a <=c x.
   by move => t /funI_P [z zd ->]; move: (qb _ zd) => [].
have cst:cardinal_set T by move => t tt; exact: (proj31(Ts _ tt)).
set s := union T.
have sx: s <=c x by apply: card_ub_sup.
case: (equal_or_not s x) => esx.
  move: (cofinality_rw ox) => [pa pb]; apply => //.
  have ta: lf_axiom (Vg f) (cofinality_c x) x.
    move=> t; rewrite - df => tdf;  apply /(oltP ox).
    apply: oclt; exact:(qb _ tdf).
  set g:= Lf (Vg f) (cofinality_c x) x.
  exists g; split. rewrite /g; hnf; saw; apply: lf_function => //.
  have osT:ordinal_set T  by move => t /cst h; apply: OS_cardinal.
  move => t /(oltP ox); rewrite - esx => tx.
  move: (olt_sup osT tx) => [z /funI_P [w]].
  by rewrite df esx; move => u1 u2 [u3 _]; ex_tac; rewrite /g LfV// - u2.
have le1:x <=c s *c cofinality_c x.
  rewrite - csum_of_same -df -q3; apply: csum_increasing; aw; trivial.
  move=> a adf; rewrite LgV//; apply: card_sup_ub => //; apply /funI_P; ex_tac.
suff: (cofinality_c x *c s) <=c cofinality_c x.
  by rewrite cprodC; move=> le2; rewrite (cleA p3 (cleT le1 le2)).  
move:(CS_sup cst) (proj31 p3)=> cs cy.
case: (finite_or_infinite cs) => fs.
  case: (finite_or_infinite cy) => fy.
    have  fp: finite_c  (s *c cofinality_c x).
      by apply /NatP; apply: NS_prod; apply /NatP.
    case: (cleNgt le1 (clt_fin_inf fp icx)).
  exact: (cprod_inf2 fs fy).
have lt1: (s *c cofinality_c x) <=c s -> False.
  by move => le2; move: (cleA sx (cleT le1 le2)) => bad; case: esx.
case: (finite_or_infinite cy) => fy; first by case:(lt1 (cprod_inf2 fy fs)).
case: (cleT_ee cs cy) => le3; first exact:(cprod_inf1 le3 fy).
case: (lt1 (cprod_inf1 le3 fs)).
Qed.


Lemma cofinality_small x: infinite_c x -> \cf x <=c x.
Proof.
move => icx; rewrite - (cofinality_card icx).
apply: (cofinality_c_small (proj1 icx)).
Qed.


Lemma cofinality_regular x (y:= \cf x): ordinalp x ->
  [\/ y = \0c, y = \1c | regular_cardinal y].
Proof.
move => ox.
move: (cofinality_reg ox); rewrite -/y => ry.
case: (regular_finite ry); first by constructor 1.
  by constructor 2.
move: (regular_is_cardinal ry) => cy iy.
have icy: infinite_c y.
  by move /infinite_setP: (infinite_set_pr3 iy);rewrite card_card.
constructor 3; split => //; rewrite (cofinality_card icy).
exact (proj2 ry).
Qed.


Lemma cofinality_index a: ordinalp a -> 
   ord_index (\cf (\omega a)) <=o a.
Proof.
move=> on; move: (CIS_aleph on) => io.
move: (cofinality_pr3 (proj1 (proj1 io))).
move: (cofinality_infinite io).
rewrite (cofinality_card io) =>pa pd.
move: (ord_index_pr1 pa) => [pb pc].
by apply: aleph_leo_le => //; rewrite pc.
Qed.


Lemma cofinality_index_regular a (x :=\omega a) : ordinalp a -> 
   (regular_ordinal x <-> ord_index (\cf x) = a).
Proof.
move=> on;split; first by move => [pa ->]; apply: ord_index_pr.
move => pa; split; first by apply: OS_aleph.
rewrite /x - {2} pa.
have ic: infinite_c (\cf (\omega a)).
  by  apply: cofinality_infinite_cardinal; apply: CIS_aleph.
by move: (ord_index_pr1  ic) =>[_ ->].
Qed.

Lemma regular_initial_limit0 x: limit_ordinal x ->
  \cf (\aleph x) <=o \cf x.
Proof.
move => lx; move: (lx) => [ox _ _]; move: (CIS_aleph ox) => icx.
rewrite - (cofinality_card icx).
move: (cofinality_c_rw (infinite_ge2 icx)) => [pa pb pc].
move: (cofinality_rw ox)=> [pd [f [[ff sf tf] cf]] _].
set E:= Imf f.
have Ex: sub E x by rewrite -tf; apply: Imf_Starget.
have se: union E = x.
  set_extens t. 
    move => /setU_P [ z tz /Ex zx]; exact:(ordinal_transitive ox zx tz).
  move/(proj33 lx) /cf => [z za  /oleSltP zb]; apply /setU_P. 
  exists (Vf f z); first by move/oltP0: zb => [_ _].
  apply /Imf_P => //; exists z => //; ue.
have oce: ordinalp (cardinal E) by apply: OS_cardinal; fprops.
have pe: csum_of_small1 (\omega x) (Lg E \omega).
  split; fprops; hnf;aw => t tdf; rewrite LgV//; apply aleph_lt_ltc.
  by apply /(oltP ox); apply: Ex.
have pf: cofinality_c_ex (\omega x) (cardinal E).
  move: (csum_commutative1 pe) => [g [ga gb gc gd]]; exists g; split => //.
    by rewrite gb; aw.
  by rewrite - gc (aleph_sum_pr4 lx Ex se).
move: (pc _ oce pf).
move: (image_smaller ff); rewrite -/E sf.
rewrite (card_card (CS_cofinality ox)) => c1 c2 .
exact: (oleT c2 (ocle c1)).
Qed.

Lemma regular_initial_limit1 x: limit_ordinal x ->
    \cf (\aleph x) = \cf x.
Proof.
move=> lx; apply: oleA; first by apply: regular_initial_limit0.
move: (lx) => [ox _ _].
pose thei t := Yo (infinite_c t) (ord_index t) \0o.
rewrite - (cofinality_card  (CIS_aleph ox)).
have thei1: forall t, infinite_c t -> (ordinalp(thei t) /\ \aleph (thei t) = t).
   by move=> t it; rewrite /thei; Ytac0; apply: ord_index_pr1.
have the2: forall t, t <c (\aleph x) -> thei t <o x.
  move=> t to; case: (p_or_not_p (infinite_c t)) => ti.
    move: (thei1 _ ti) => [ot eq]; rewrite - eq in to.
    apply: (aleph_ltc_lt ot ox to).
  by rewrite /thei; Ytac0; move: lx => [p1 p2 _]; apply /oltP.
move: (cofinality_c_rw (infinite_ge2 (CIS_aleph ox))) => [pa pb _].
move: pb => [f [ [qa qb] qc qd]].
pose g  := Lf (fun  i => thei (Vg f i)) (domain f) x.
have the3: forall u,  inc u (domain f) -> thei (Vg f u) <o x.
   by  move => i idf; apply:  the2; apply: qb.
have ga: lf_axiom (fun  i => thei (Vg f i)) (domain f) x.
  by move => i /=; aw => idf; apply /(oltP ox); apply: the3.
have fg: function g by apply: lf_function.
set z := \osup (Imf g).
move: (cofinality_rw  ox) => [pc _ pd].
have oT: ordinal_set (Imf g).
  move=> t /(Imf_Starget fg);  rewrite /g; aw;exact: (Os_ordinal ox).
case: (equal_or_not z x) => zx.
   apply: pd. 
     exact: (proj31 (ocle pa)).
   rewrite -qc; exists g; split; first by split => //; rewrite /g; aw.
   move=> t /(oltP ox) tx; ex_middle bad.
   suff xt: x <=o t by case: (oltNge tx).
   move: (proj31_1 tx) => ot;rewrite - zx;apply: ord_ub_sup => //. 
   move=> i ia; move: ia (oT _ ia).
   move /(Imf_P fg);rewrite {1}/g; aw; move=> [u usg ->] ow.
   case: (oleT_el ow ot) => //; move=> [le1 _];case: bad; ex_tac.
have lezx: z <o x.
  split => //; apply: ord_ub_sup => //.
  move => i /(Imf_P fg).
  rewrite /g; aw; move=> [u usg ->]; rewrite LfV//; exact: (proj1 (the3 _ usg)).
have oz:=proj31_1 lezx.
have th4: forall i, inc i (domain f) -> Vg f i <=c (\aleph z).
   move=> i idf.
   case: (finite_or_infinite (proj31_1 (qb _ idf))) => fd.
     move: (CIS_aleph oz) => le2; exact: (cle_fin_inf fd le2).
   move:(thei1 _ fd) => [pe <-]; apply: aleph_le_lec.
   have ->: thei (Vg f i) = Vf g i  by rewrite /g LfV//.
   apply: ord_sup_ub => //; apply /(Imf_P fg).
   by exists i => //; rewrite /g; aw.
move: (csum_of_small_b1 (conj qa th4)); rewrite qc qd.
move: (aleph_lt_ltc lezx) pa.
set A := \aleph x; set B :=  \aleph z; set C := cofinality_c (\aleph x).
move => le1 pa le2.
have cb := proj31_1 le1.
have cc:= proj31 pa.
have anz: A <=c \0c -> False.
   move: (CIS_aleph ox) => ia h.
   have fz: finite_c \0c by apply: finite_0.
   case: (cleNgt h (clt_fin_inf fz ia)).
move: (CIS_aleph oz) => ib.
case: (equal_or_not C \0c) => cz.
  by move: le2; rewrite cz cprod0r => h; case: anz.
case: (cleT_ee cb cc) => auc; last first.    
  move: (cprod_inf auc ib cz) => xx.
  by case:(cltNge  le1); rewrite -xx. 
move: (cle_inf_inf ib auc) => ic.
move: (cprod_inf auc ic  (aleph_nz oz)). 
rewrite cprodC => xx; rewrite xx in le2.
apply: (oleT (cofinality_pr3 ox)).
rewrite (cleA pa le2).
by apply: aleph_pr6.
Qed.

Lemma regular_initial_limit2 x: limit_ordinal x ->
    \cf(\aleph x) <=o x.
Proof.
move=> lx; move: (regular_initial_limit0 lx) => pa.
exact: (oleT pa (cofinality_pr3 (proj31 lx))).
Qed.

Definition singular_cardinal x :=
  infinite_c x /\ \cf x <> x.

Lemma regular_cardinalP x: 
 regular_cardinal x <-> infinite_c x /\ \cf x = x.
Proof.
by split; move => [pa pb]; split => //;
   rewrite -{2} pb; move: (cofinality_card pa).
Qed.


Lemma singular_limit n: ordinalp n -> 
    singular_cardinal (\aleph n) -> limit_ordinal n.
Proof.
move => on [pa pb].
case: (ordinal_limA on) => li //.
  by move: pb; rewrite li aleph0E (proj2 (regular_omega)).
move:li => [c oc cv].
by move:(regular_initial_successor oc) => /regular_cardinalP [_]; rewrite - cv.
Qed.

Lemma regular_initial_limit3 x: limit_ordinal x ->
    x <o \aleph x -> singular_cardinal (\aleph x).
Proof.
move=> pa pb; move: (regular_initial_limit2 pa) => pc.
split; first by apply: (CIS_aleph (proj31 pa)).
by move: (ole_ltT pc pb) => [_].
Qed.

Lemma regular_initial_limit4: singular_cardinal (\aleph omega0).
Proof.
apply: regular_initial_limit3; first by apply: omega_limit.
rewrite - {1} aleph0E. apply: aleph_lt_lto; apply/olt_omegaP; fprops.
Qed.

Lemma regular_initial_limit5 x:
  singular_cardinal x -> (\aleph omega0) <=c x.
Proof.
move=> sx; move: (sx) => [ix _].
move: (sx) => [_]; rewrite -(cofinality_card ix).
move: (ord_index_pr1 ix) => [on <-] nr; apply: aleph_le_lec.
case: (ordinal_limA on) => h.
- case: nr; rewrite h aleph0E; exact:(proj2 regular_cardinal_omega). 
-  move:h=> [m om nsy]. 
   case: nr; rewrite nsy; exact: (proj2 (regular_initial_successor om)).
- by apply: limit_ge_omega.
Qed.

Definition inaccessible_w x :=
  regular_cardinal x /\ (exists2 n, limit_ordinal n & x = \aleph n).

Lemma inaccessible_pr1 x:
    inaccessible_w x -> x = \aleph x.
Proof.
move=> [/regular_cardinalP [xx re] [n ln xv]].
have on: ordinalp n by move: ln => [].
move: (osi_gex aleph_lt_lto on) => le1.
case: (equal_or_not n (\aleph n)) => eq; first by rewrite xv - {2} eq.
move: (regular_initial_limit3 ln (conj le1 eq))=> [_].
by rewrite -xv re.
Qed.

Lemma inaccessible_uncountable x:
  inaccessible_w x -> aleph0 <c x.
Proof.
move => sa.
have bx:= (inaccessible_pr1 sa).
rewrite bx /aleph0 - aleph0E; apply:aleph_lt_ltc;rewrite bx; apply: oclt.
by move:(clt_leT clt_02 (infinite_ge2 (proj1 (proj1 sa)))); rewrite - bx.
Qed.

Lemma cofinality_least_fp_normal2 x y f:
  normal_ofs f -> f x <> x ->  least_fixedpoint_ge f x y ->
  y = omega0  \/ singular_ordinal y.
Proof.
move => pa pb pc; case: (equal_or_not omega0 y) => yno; first by left.
right; rewrite /singular_ordinal /regular_ordinal.
move:(pc) => [[_ oy _] _]; split => //.
by rewrite (cofinality_least_fp_normal pa pb pc); move => [_ h].
Qed.

Lemma cofinality_least_fp_normal3 x y:
  ordinalp x ->
  least_fixedpoint_ge \omega (osucc x) y -> singular_cardinal y.
Proof.
move => ox pb.
have pa: \omega (osucc x) <> (osucc x).
  move: (infinite_card_limit2 (CIS_aleph (OS_succ ox))).
  set z := \omega _; move => [/ordinal_irreflexive oz zz zs] zz1.
  case: oz; rewrite {1} zz1; apply: zs; rewrite zz1; fprops.
case: (cofinality_least_fp_normal2 aleph_normal pa pb) => //.
  move => yo; move: pb => [_ fx _]; rewrite -fx  yo.
  apply: regular_initial_limit4.
move=> [pc pd].
have iy:infinite_c y  by move: pb => [xx <- _]; apply: CIS_aleph.
split => // aux; case: pd; split => //.
Qed.

Lemma regular_cofinal_si_unique z:
  uniqueness (fun x => regular_ordinal x
              /\ (exists2 f, cofinal_function f z x  & sincr_ofn f x)).
Proof.
set H := fun x => _.
suff: forall x y, H x -> H y -> x <=o y.
  by move=> ht x y hx hy; apply: oleA;apply: ht.
move=> x y [rx [f fx sif]] [ry [g gy sig]] {H}.
move: fx gy => [[ff sf tf] fp] [[fg sg tg] gp].
pose h t := choose (fun z => inc z x /\ Vf g t <=o (Vf f z)). 
have htp: forall t, inc t y -> (inc (h t) x /\ Vf g t <=o (Vf f (h t))).
   move=> t ty; apply choose_pr. 
   have wz: inc (Vf g t) z by rewrite - tg; apply: Vf_target => //; ue.
   by move: (fp _ wz) => [u u1 u2]; exists u.
have ta: lf_axiom h y x by  move=> t ty; move: (htp _ ty) => [].
move: rx ry => [ox rx] [oy _].
move: (cofinality_rw ox) => [_ _ aux]; rewrite -rx; apply: (aux _ oy).
exists (Lf h y x).
split; first by split => //;aw; trivial;apply: lf_function.
move=> t tx.
have wz: inc (Vf f t) z by rewrite - tf; apply: Vf_target => //; ue.
move: (gp _ wz) => [u zu le1].
move: (htp _ zu) => [wy le2].
have le3:= oleT le1 le2.
ex_tac; rewrite LfV//.
case: (oleT_el (Os_ordinal ox tx) (Os_ordinal ox wy)) => //.
move => le4; case: (oleNgt le3 (sif _ _ wy tx le4)).
Qed.


End Ordinals4.
Export  Ordinals4.
