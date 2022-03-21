(** * Theory of Sets : Ordinals
  Copyright INRIA (2011-2013 2018) Marelle Team (Jose Grimm).
*)

(* $Id: sset17.v,v 1.6 2018/09/04 07:58:00 grimm Exp $ *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From gaia Require Export sset15.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module Realisation.



Definition universe:=
    transdef_ord (fun f => unionf (range f) powerset).

Lemma universe_rec z: ordinalp z ->
   universe z = unionf z (fun t => \Po (universe t)).
Proof.
move => oz. rewrite /universe.
set p := (fun f => unionf (range f) powerset).
rewrite (transdef_ord_pr p oz) {1}/p.
set_extens t.
  move /setUf_P => [y /Lg_range_P [b bz ->] tp]; apply/setUf_P; ex_tac.
move/setUf_P => [y yz tv]; apply/setUf_P.
exists (transdef_ord p y) => //; apply/Lg_range_P; ex_tac.
Qed.

Lemma universe_P a: ordinalp a ->
  forall x, inc x (universe a) <-> exists2 b, b<o a & sub x (universe b).
Proof.
move => oa x.
rewrite (universe_rec oa); split.
  by move /setUf_P => [b /(oltP oa) ba /setP_P xb]; exists b.
move => [b /(oltP oa) ba /setP_P xb]; union_tac.
Qed.

Lemma universe_inc1 a b: a <o b -> sub (\Po (universe a)) (universe b).
Proof.
move /oltP0 => [oa ob ab].
rewrite (universe_rec ob) => t ta; apply /setUf_P; ex_tac.
Qed.


Lemma universe_inc1' a b: a <o b -> inc (universe a) (universe b).
Proof.
move => lab; apply/(universe_P (proj32_1 lab)); by exists a.
Qed.

Lemma universe_trans a: ordinalp a -> transitive_set (universe a).
Proof.
pose p x := transitive_set (universe x).
apply: (least_ordinal2 (p:=p)) => y oy h t.
move /(universe_P oy) => [s sy sb].
move => b bt; apply /(universe_P oy);exists s => //;apply:(h _ sy _ (sb _ bt)).
Qed.

Lemma universe_inc2 a b: a <=o b -> sub (universe a) (universe b).
Proof.
move => lab.
case: (equal_or_not a b); first by move => ->; fprops.
move=> anb; move: (universe_inc1 (conj lab anb)).
by apply: sub_trans => t ta; apply /setP_P; apply:(universe_trans (proj31 lab)).
Qed.


Lemma universe_0: universe \0o = emptyset.
Proof. by rewrite (universe_rec OS0); rewrite setUf_0. Qed.

Lemma universe_succ a: ordinalp a ->
  universe (osucc a) = \Po (universe a).
Proof.
move => oa.
have asa: a <o osucc a by apply: oltS.
apply: extensionality; last by exact:(universe_inc1 asa).
rewrite (universe_rec (OS_succ oa)) => t /setUf_P [y ys]. 
have: y <=o a by apply /oleP.
move /universe_inc2 /setP_S; apply.
Qed.

Lemma universe_limit a: limit_ordinal a ->
  universe a = unionf a universe.
Proof.
move => [pa pb pc]; apply extensionality.
  move => t /(universe_P pa) [b /(oltP pa) ba /setP_P etc]. 
  apply /setUf_P; exists (osucc b); first by apply: pc.
  rewrite universe_succ //; exact (Os_ordinal pa ba).
by move => t /setUf_P [y /(oltP pa) [ya _]]; apply: (universe_inc2). 
Qed.

Lemma ordinal_in_universe a: ordinalp a -> sub a (universe a).
Proof.
move => oa; case: (least_ordinal6 (fun z => sub z (universe z)) oa) => //.
set z := least_ordinal _ _; move => [oz h]; case.
move => t tz; move: (h _ tz) => /setP_P.
have ot:= (Os_ordinal oz tz).
have: osucc t <=o z by apply /oleSltP; apply/(oltP oz).
rewrite - (universe_succ ot) => /universe_inc2; apply.
Qed.


Lemma ordinals_of_universe a: ordinalp a ->
  Zo (universe a) ordinalp = a.
Proof.
move => oa; apply:extensionality; last first.
  move => t ta; apply/Zo_P; split; last exact:(Os_ordinal oa ta).
  exact:((ordinal_in_universe oa) _ ta).
case: (least_ordinal6 (fun a => sub (Zo (universe a) ordinalp) a) oa) => //.
set y := least_ordinal _ _; move => [oy hrec]; case.
case: (ordinal_limA oy) => h.
+ by rewrite h universe_0 => t /Zo_S /in_set0.
+ move: h => [z oz zy] t /Zo_P [ts ot]. 
  move: ts; rewrite zy (universe_succ oz) => /setP_P stz.
  apply/(oltP (OS_succ oz)) /oltSleP; split => // u ut.
  have izy: inc z y by rewrite zy; fprops.
  apply: (hrec _ izy); apply/Zo_P; split => //; first exact: (stz _ ut).
  exact: (Os_ordinal ot ut).
move/limit_ordinal_P:(h) => [sa sb].
move => t/Zo_P [tut ot]. 
move:tut;rewrite (universe_limit h) => /setUf_P [z zy zv].
have :inc t (Zo (universe z) ordinalp) by  apply/Zo_P.
by move /(hrec _ zy); move:(ordinal_transitive oy zy); apply.
Qed.

Lemma card_universe_fin n: natp n -> finite_set (universe n).
Proof.
move: n; apply: Nat_induction.
  by rewrite universe_0; apply: emptyset_finite.
move => n nN /card_finite_setP Hrec.
  rewrite (succ_of_nat nN) (universe_succ (OS_nat nN)).
  apply /card_finite_setP; rewrite card_setP - cpowcr; fprops.
Qed.


Lemma card_universe_omega: cardinal (universe omega0) = aleph0.
Proof.
apply: cleA; last first.
  by move: (sub_smaller (ordinal_in_universe OS_omega)); rewrite cardinal_Nat.
rewrite (universe_limit omega_limit). 
set f := (Lg omega0 universe).
have ->: (unionf omega0 universe) = unionb f.
   rewrite /f /unionb; aw; apply:setUf_exten => h hi /=; rewrite LgV//.
have ha: countable_set (domain f) by rewrite Lgd; apply: countable_Nat.
have hb: allf f countable_set. 
  rewrite /f;hnf; aw => i io; rewrite LgV//; apply:finite_is_countable. 
  exact:(card_universe_fin io).
by move: (countable_union ha hb) => /countableP.
Qed.

Lemma card_universe a: ordinalp a -> 
   cardinal (universe (omega0 +o a)) = beth a.
Proof.
move => oa.
pose hyp a:= cardinal (universe (omega0 +o a)) = beth a.
case:(least_ordinal6 hyp oa); first by apply.
set y := least_ordinal _ _;move => [oy hrec]; case.
case: (ordinal_limA oy) => h.
+ by rewrite /hyp h (osum0r OS_omega) beth0 card_universe_omega.
+ move: h=> [z oz zv]; rewrite /hyp zv (beth_succ oz).
  rewrite - (osum2_succ OS_omega oz) (universe_succ (OS_sum2 OS_omega oz)).
  rewrite card_setP - cpowcr hrec //; rewrite zv; fprops.
+ rewrite /hyp.
  have ls:= osum_limit OS_omega h.
  rewrite (universe_limit ls); apply: cleA.
    apply: (cleT (csum_pr1_bis (omega0 +o y) universe)). 
    rewrite/csumb; set f := Lg _ _.
    have csf: csum_of_small1 (beth y) f.
      rewrite /f; split; fprops; hnf; aw; move => i id; rewrite LgV//. 
      move/(oltP (proj31 ls)): id => lio.
      case: (oleT_ee OS_omega (proj31_1 lio)) => sa.
        move: (odiff_pr sa) => [sc sd].
        have sz: (i -o omega0) <o y. 
          by apply:(osum_Meqltr sc (proj31 h)  OS_omega); rewrite - sd.
        rewrite sd (hrec _ (olt_i sz)); exact: (beth_M sz).
      move:(sub_smaller (universe_inc2 sa)); rewrite card_universe_omega => sd.
      apply:(cle_ltT sd); rewrite /aleph0 - beth0; apply:beth_M.
      apply:(limit_pos h).
    have icb:= (beth_pr1 oy).
    move: (csum_of_small_b2 csf); rewrite - cprod2cr {2}/f Lgd.
    have ds: cardinal (omega0 +o y)  <=c  beth y.
      rewrite (osum_cardinal OS_omega oy).
      have ha:= (osi_gex (proj1 beth_normal) oy).
      have hb:= (oleT (limit_ge_omega h) ha).
      move: (csum_Mlele (ocle1 hb) (ocle1 ha)). 
      by rewrite (card_card (proj1 icb)) (csum_inf1 icb).
    rewrite (cprod_inf ds icb) // => /card_nonempty => sz.
    exact: (omega_nz (proj1 (osum2_zero OS_omega oy sz))).
  rewrite (proj2 beth_normal _ h).
  apply: card_ub_sup; first by exact:CS_cardinal.
  move => i /funI_P [z zy ->]. 
  rewrite - (hrec _ zy); apply: sub_smaller => t tu.
  apply/setUf_P; exists (omega0 +o z) => //; apply: olt_i.
  apply: (osum_Meqlt _ OS_omega); exact/oltP.
Qed.



Lemma universe_inaccessible x a :
  inaccessible a -> inc x (universe a) -> cardinal x <c a.
Proof.
move => ia. 
have ica := (proj1 (proj1 (proj1 ia))).
have oa:=(proj1 (proj1 ica)).
move /(universe_P oa) => [b lba s1].
have ob := (proj31_1 lba).
move: (beth_inaccessible ia lba).
move: (sub_trans s1 (universe_inc2 (osum_M0le OS_omega ob))).
move => /sub_smaller; rewrite (card_universe ob); apply:cle_ltT.
Qed.

Lemma universe_inaccessible_bis a :
  inaccessible a -> cardinal (universe a) = a.
Proof.
move => ia.
have ica := (proj1 (proj1 (proj1 ia))).
have  {1} <- : omega0 +o a = a.
  apply: (indecomp_prop1 (cardinal_indecomposable ica)).
  exact: (oclt (inaccessible_uncountable (proj1 ia))).
rewrite (card_universe (proj1 (proj1 ica))).
exact: (beth_inaccessible1  ia).
Qed.



Definition universe_i x := exists2 a, ordinalp a & inc x (universe a). 
Definition urank_prop x a :=  
  [/\ ordinalp a, sub x (universe a) & 
    forall c, c <o a -> ~(sub x (universe c)) ].
Definition urankA_prop x a :=  
  [/\ ordinalp a, inc x (universe a) & 
    forall c, c <o a -> ~(inc x (universe c)) ].
Definition urank a x:= least_ordinal (fun b => sub x (universe b)) a. 
Definition urankA a x:= least_ordinal (fun b => inc x (universe b)) a. 

Lemma urank_universe a: ordinalp a -> urank_prop (universe a) a.
Proof.
move => ap; split => // c /universe_inc1 ca su.
move: (sub_smaller (sub_trans ca su)); rewrite card_setP - cpowcr => sa.
case: (cltNge (cantor (CS_cardinal (universe c))) sa).
Qed.

Lemma urank_uniq x: uniqueness (urank_prop x).
Proof.
move => a b [oa pa pb][ob pc pd].
case: (oleT_ell oa ob) => //; [ by move /pd | by move /pb].
Qed.

Lemma urankA_uniq x: uniqueness (urankA_prop x).
Proof.
move => a b [oa pa pb][ob pc pd].
case: (oleT_ell oa ob) => //; [ by move /pd | by move /pb].
Qed.


Lemma urank_pr x a (b:= urank a x): ordinalp a -> sub x (universe a) ->
  b <=o a /\  urank_prop x b.
Proof.
move =>oa pa.
pose p b := sub x (universe b).
move: (least_ordinal4 oa pa (p:=p)) => []; rewrite -/(urank _ _) -/b /p.
move => ob xb etc; split; first by apply: etc.
split => //;move => c cb xc.
case: (oltNge cb (etc _ (proj31_1 cb) xc)).
Qed.

Lemma OS_urank x a: ordinalp a -> ordinalp (urank a x).
Proof.
move => oa; rewrite /urank /least_ordinal; set S := Zo _ _.
case: (emptyset_dichot S) => h; first by rewrite h setI_0; fprops.
have os: ordinal_set S. 
   move => t /Zo_S /setU1_P[] ta; [exact: (Os_ordinal oa ta) | ue ].
exact: (os _ (ordinal_setI h os)).
Qed.

Lemma urankA_pr x a (b:= urankA a x): ordinalp a -> inc x (universe a) ->
  b <=o a /\  urankA_prop x b.
Proof.
move =>oa pa.
pose p b := inc x (universe b).
move: (least_ordinal4 oa pa (p:=p)) => []; rewrite -/(urank _ _) -/b /p.
move => ob xb etc; split; first by apply: etc.
split => //;move => c cb xc.
case: (oltNge cb (etc _ (proj31_1 cb) xc)).
Qed.

Lemma urank_ex x: universe_i x -> exists b, urank_prop x b. 
Proof.
move => [a oa xa]; exists (urank a x).
by move: (universe_trans oa xa) => /(urank_pr oa) [_ h].
Qed.

Lemma urankA_succ x a: urankA_prop x a -> osuccp a.
Proof.
move => [oa xa etc].
case: (ordinal_limA oa) => // hc.
- by move: xa; rewrite hc; rewrite universe_0 => /in_set0.
- by move: xa; rewrite (universe_limit hc) => /setUf_P [y /(oltP oa) /etc].
Qed.

Lemma urankA_ex x: universe_i x -> 
   exists2 b, ordinalp b & urankA_prop x (osucc b). 
Proof.
move => [a oa xa]; move: (urankA_pr oa xa) => [_ pb].
move /urankA_succ: (pb) => [b ob bs]; rewrite bs in pb; exists b => //.
Qed.

Lemma urank_alt x b: urankA_prop x (osucc b) <-> urank_prop x b.
Proof.
split.
  move => [pa pb pc].
  have ob: ordinalp b by apply: OS_succr.
  split => //; first by apply/setP_P; rewrite - (universe_succ ob).
  move => c cb /setP_P h.
  have oc:=proj31_1 cb.
  by move /oltSSP: cb => /pc; rewrite  (universe_succ).
move => [ob pb pc]; move: (OS_succ ob) => osb.
have ha: inc x (universe(osucc b)) by rewrite (universe_succ ob); apply/setP_P.
have: universe_i x by  exists (osucc b).
move /urankA_ex => [c oc h];  move: (h) => [qa qb qc].
move: qb;  rewrite  (universe_succ oc) => /setP_P => qb.
case: (oleT_ell ob oc); [by move => -> |  | by move /pc].
by move /oltSSP => /qc.
Qed.

Lemma urank_alt1 a x: ordinalp a -> inc x (universe a) ->
   urankA a x = osucc (urank a x).
Proof.
move => oa xa.
move: (proj2 (urankA_pr oa xa)) => h2.
move:(urank_pr oa (universe_trans oa xa))=> [_ ] /urank_alt h1.
exact:(urankA_uniq h2 h1).
Qed.


Lemma urank_alt2 a x: ordinalp a -> inc x (universe a) ->
  inc x (universe (osucc (urank a x))).
Proof.
move => oa xa; rewrite - (urank_alt1 oa xa).
by move: (urankA_pr oa xa) => [h1 []]. 
Qed.

Lemma urank_pr1 x a (b:= urank a x): ordinalp a -> inc x (universe a) ->
  b <o a /\  urank_prop x b.
Proof. 
move => oa xa.
move:(urank_pr oa (universe_trans oa xa))=> [_ h]; split => //.
move: (urankA_pr oa xa) => [h1 h2]; apply /oleSltP.
by rewrite - (urank_alt1 oa xa). 
Qed.

Lemma urank_uniq2 x a b:
   ordinalp a -> ordinalp b ->
   inc x (universe a) -> inc x (universe b) ->
   urank a x = urank b x.
Proof.
move => oa ob xa xb;
move: (urank_pr1 oa xa) (urank_pr1 ob xb) => [_ s2] [_ s4].
apply: (urank_uniq s2 s4).
Qed.

Lemma urank_ordinal x: ordinalp x -> urank_prop x x.
Proof.
move => ox; split; first exact.
  apply: (ordinal_in_universe ox).
move => c cx /setP_P.
move: (universe_inc1 cx) => qa qb; move: (qa _ qb) => xx.
move: (least_ordinal4 ox xx (p:= fun y => inc y (universe y))).
simpl; set a := least_ordinal _ _; move => [oa nzz rec].
move /(universe_P oa): nzz => [b ba bb]; apply: (oleNgt _ ba).
apply:rec; first exact: (proj31_1 ba).
by apply: bb; apply /(oltP oa).
Qed.

Lemma universe_ordinal x: ordinalp x -> universe_i x.
Proof. by move /urank_ordinal => /urank_alt [pa pb pc]; exists (osucc x). Qed.

Lemma urank_inc a x y : ordinalp a -> inc x (universe a) -> inc y x ->
   inc y (universe a) /\ (urank a y) <o (urank a x). 
Proof.
move => oa xa yx.
move: (urank_pr1 oa xa) => [_ [sa sb _]].
move: (universe_trans oa xa yx) => ya; split => //; apply /oleSltP.
have ysa:= (universe_trans oa ya).
move: (sb _ yx) => h; move: (urankA_pr sa h)=> [pc pd].
by rewrite - (urank_alt1 oa ya) - (urankA_uniq pd (proj2 (urankA_pr oa ya))).
Qed.

Lemma urank_sub a x y : ordinalp a -> inc x (universe a) -> sub y x ->
   inc y (universe a) /\ (urank a y) <=o (urank a x). 
Proof.
move => oa xa yx.
move:(urank_pr1 oa xa) =>[pa pb];move: (pb) => [p1 p2 p3].
have pc: inc y (universe (osucc (urank a x))).
  rewrite (universe_succ p1); apply /setP_P; apply: (sub_trans yx p2).
have p4: (osucc (urank a x)) <=o a by apply /oleSltP.
have ya: inc y (universe a) by apply:(universe_inc2 p4). 
move: (urank_pr1 (OS_succ p1) pc) => [].
by rewrite (urank_uniq2 (OS_succ p1) oa pc ya)  => /oltSleP h _.
Qed.

Lemma urank_powerset a x : ordinalp a -> inc x (universe a) -> 
   inc (\Po x) (universe (osucc a)) /\
   (urank a (\Po x)) = osucc (urank a x).
Proof.
move => oa xa.
move: (urank_pr1 oa xa); set r := urank a x; move => [ra pra].
move /oleSltP: ra => sra.
have pa: sub (\Po x) (universe (osucc r)).
   move: pra => [uu vv _]; move => t /setP_P tcx; rewrite (universe_succ uu). 
   apply /setP_P; apply: sub_trans tcx vv.
move: (sub_trans pa (universe_inc2 sra)) => sa.
split; first by rewrite (universe_succ oa); apply /setP_P.
move: (urank_pr oa sa); move => [qa qb]. 
suff:urank_prop (\Po x) (osucc r) by  move => h; apply(urank_uniq qb h).
split => //; first exact: (proj31 sra).
move => c /oltSleP cr h; move: (h _ (setP_Ti x))=> xc.
move: (urank_pr1 (proj31 cr) xc) => [u1 u2].
by move: cr ; rewrite (urank_uniq pra u2) =>/(oltNge u1).
Qed.


Lemma urank_union a x : ordinalp a -> inc x (universe a) -> 
   inc (union x) (universe a) /\ (urank a (union x)) =  (opred (urank a x)).
Proof.
move => oa xa.
move: (urank_pr1 oa xa) => [pa pb].
move: (pb) => [orx qb qc].
set b := urank a x.
set c := opred (urank a x).
have pc: forall y, inc y x -> inc y (universe a) /\ (urank a y) <o b.
  by move => y /(urank_inc oa xa).
have osb: ordinal_set b by move => t /(Os_ordinal orx).
have pd: c <=o b. 
   by apply: ord_ub_sup => // t tb; move/(oltP orx): tb => [].
have oc:= proj31 pd.
have aux: forall u, u <o b -> u <=o c.
  move => u ub;have ub':=(olt_i ub); have ou'':= (Os_ordinal orx ub').
  split => //;apply: (setU_s1 ub').
have pe: sub (union x) (universe c).
  move => t /setU_P [z za zb].
  have p3: sub z (universe a) by move: (pc _ zb) => [/(universe_trans oa)].
  move: (urank_inc oa xa zb) => [_] /aux /universe_inc2; apply.
  by move: (urank_pr oa p3)  => [_ [s1 s2 s3]];apply: s2.
have pf :inc (union x) (universe a).
  by apply: (universe_inc1 (ole_ltT pd pa)); apply /setP_P.
move: (urank_pr oc pe) => [s1 s2].
move: (urank_pr oa (universe_trans oa pf)) => [_ s4].
move: (urank_uniq s2 s4) => eq.
move: s1 s2; rewrite eq; set d := urank a (union x) => dc pg.
split => //; clear s4 eq; apply: oleA => //.
move: (urank_powerset oa pf) => [q1].
move:(urank_pr1 (OS_succ oa) q1) => [_ rp1].
move: (q1); rewrite (universe_succ oa) => /setP_P /(urank_pr oa) [_ rp2].
rewrite (urank_uniq rp2 rp1) => h.
have sa: sub x (\Po (union x)).
  move => t tx; apply /setP_P => s st; union_tac.
move: (urank_sub (OS_succ oa) q1 sa) => [q3].
rewrite - (urank_uniq2 oa (OS_succ oa) xa q3) h -/d /c -/b  => bsd.
apply: (ord_ub_sup (proj31 dc)).
by move => t /(oltP (proj31 pb)) ha; apply /oltSleP; apply: (olt_leT ha bsd).
Qed.



Lemma sub_Nat_Vomega: sub Nat (universe omega0).
Proof. 
move => t tb.
move: (urank_ordinal (OS_nat tb))=> /urank_alt [pa pb _].
move: omega_limit => /limit_ordinal_P [_ h].
have to: t <o omega0 by apply /(oltP OS_omega).
exact:(universe_inc2 (proj1 (h _ to)) pb).
Qed.


Lemma universe_stable_inc x: 
  universe_i x <-> (forall y, inc y x -> universe_i y).
Proof.
split. 
  by move => [a pa pb] y ye; move: (urank_inc pa pb ye) => [ya _]; exists a.
move => h.
pose p x y := ordinalp y /\ inc x (universe y).
have cp: forall y, inc y x -> p y (choose (p y)).
  by move => y yx; apply choose_pr; move: (h _ yx) => [t ta tb]; exists t.
set E := fun_image x (fun z => choose (p z)).
have ose: ordinal_set E by move => t /funI_P [z /cp [pa _] ->].
move: (OS_sup ose)(ord_sup_ub ose); set a := \osup E => pa pb. 
exists (osucc a); first by fprops.
rewrite (universe_succ pa); apply /setP_P => y yx.
have: inc (choose (p y)) E  by apply /funI_P; ex_tac.
by move /pb /universe_inc2; apply; move: (cp _ yx) => [_].
Qed.


Definition urank0 x := 
   choose (fun z => exists a, [/\ ordinalp a, inc x (universe a) & 
    z = urank a x]).

Lemma urank0_pr a x (r:=  urank0 x): ordinalp a -> inc x (universe a) -> 
   r = urank a x /\ urank_prop x r.
Proof.
move => oa xua.
pose p z := exists a, [/\ ordinalp a, inc x (universe a) & 
    z = urank a x].
have pa:  (exists z, p z) by exists (urank a x); exists a; split => //.
move: (choose_pr pa); rewrite /r/urank0 -/p.
set v := choose p; move => [b [ob xub zv]].
rewrite(urank_uniq2 oa ob xua xub); split => //.
have ha: sub x (universe b). 
  apply /setP_P; rewrite - (universe_succ ob). 
  by apply: (universe_inc2 (proj1 (oltS ob))).
rewrite zv;exact: (proj2 (urank_pr ob ha)).
Qed.

Lemma urank0_pr1 x: universe_i x -> urank_prop x (urank0 x).
Proof. move => [a pa pb]; exact: (proj2 (urank0_pr pa pb)). Qed.


Lemma urank0_pr3 a b: 
   universe_i b -> inc a b -> urank0 a <o urank0 b.
Proof.
move => [c oc bc] iab.
move:(urank0_pr oc bc) => [-> _].
move:(urank_inc oc bc iab) => [sc sd].
by move:(urank0_pr oc sc) => [-> _].
Qed.

Lemma urank0_ordinal a: ordinalp a -> urank0 a = a.
Proof. 
move => oa.
exact: (urank_uniq (urank0_pr1 (universe_ordinal oa)) (urank_ordinal oa)). 
Qed.

(** transitive closure *)

Definition transitive_closure X:=
  union (target (induction_defined union X)).

Definition transitive_closure_pr X Y:=
   [/\ transitive_set Y, sub X Y &
     forall Z, transitive_set Z -> sub X Z  -> sub Y Z].

Lemma tc_unique X: uniqueness (transitive_closure_pr X).
Proof.
move => a b [p1 p2 p3] [q1 q2 q3]. 
apply: extensionality; [by apply:p3 |  by apply:q3].
Qed.

Lemma tc_exists X:
  transitive_closure_pr X (transitive_closure X).
Proof.
rewrite /transitive_closure.
move: (induction_defined_pr union X) => [].
set f := induction_defined _ _; set Y := union (target f) => sf [ff sjf] f0 fs.
have yp: forall y, inc y Y <-> exists2 n, inc n Nat & inc y (Vf f n).
  rewrite - sf;move => y; split.
     move /setU_P => [z zy /sjf [x xsf fx]]; ex_tac; ue.
  move => [n nsf yv]; apply /setU_P; exists (Vf f n) => //; Wtac.
split.
    move => t /yp [n nN tv] s st; apply/yp; exists (csucc n). 
      by apply:NS_succ.
    rewrite (fs _ nN); union_tac.
  rewrite -f0;move => t tX; apply /yp; exists \0c => //; apply:NS0.
move => Z tz xz.
have aux: forall n, inc n Nat -> sub (Vf f n) Z.
  apply: Nat_induction; first by ue.
  by move => n nN h; rewrite (fs _ nN); apply: setU_s2 => y /h /tz.
move => t /yp [n /aux]; apply.
Qed.

Lemma tc_pr1 X:
  transitive_closure X = X \cup (unionf X transitive_closure).
Proof.
move: (tc_exists X) =>[].
set Y := (transitive_closure X) => pa pb pc.
apply: extensionality.
  set Z := _ \cup _; apply: pc; last by apply:subsetU2l.
  move => t tz s st; apply /setU2_P; right; apply /setUf_P;case /setU2_P: tz. 
    by move => h;ex_tac; apply:(proj32 (tc_exists t)).
  by move/setUf_P => [y yx etc]; ex_tac; apply: (proj31 (tc_exists y) _ etc).
move => t /setU2_P;case; first by apply: pb.
move /setUf_P => [y ya yb].
exact: (proj33 (tc_exists y) Y pa (pa _ (pb _ ya)) _ yb).
Qed.

Definition foundation_prop x := 
  x = emptyset \/ exists2 y, inc y x & disjoint y x.
Definition foundation_axiom:= forall x, foundation_prop x.

Definition well_founded_set x := 
  forall f, function f  -> source f = Nat ->
    (forall n, (natp n -> inc (Vf f (csucc n)) (Vf f n))) ->
  x <> Vf f \0c.

Definition ordinal_altp x:=
   transitive_set x /\ 
   (forall a b, inc a x -> inc b x -> [\/ inc a b, inc b a | a = b]).

Lemma ordinal_with_AF x:
 (forall y, sub y x -> foundation_prop y) ->
 (ordinalp x <-> ordinal_altp x).
Proof.  
move => hc; split.
  move => ox; split; first by  apply: (ordinal_transitive ox).
  move => a b ax bx.
  exact (ordinal_inA (Os_ordinal ox ax) (Os_ordinal ox bx)).
move => [trx xp].
have hb: forall a b c, inc a x -> inc b x -> inc c x ->
   foundation_prop (tripleton a b c). 
  by move => a b c ax bcx cx; apply:hc => y /set3_P; case; move => ->. 
have ha: asymmetric_set x.
  move => u v ux vx uv vu.
  case: (hb _ _ _ ux ux vx).
    apply /nonemptyP; exists v; rewrite/tripleton;fprops.
  rewrite /tripleton -/(singleton _) setU2_11.
  move => [y /set2_P]; case => ->; apply/nonemptyP. 
    exists v; fprops.
    exists u; fprops.
apply /ordinal_pr1; split => //. 
have pa: (substrate (ordinal_oa x)) = x.
  by rewrite graph_on_sr => // a ax; right.
have pb: order (ordinal_oa x).
  pose r a b := [/\ inc a x, inc b x & (inc a b \/ a = b)].
  have ->: ((ordinal_oa x) = graph_on r x).
    by apply: Zo_exten1 => t /setX_P [_ px qx]; split => //; move => [_ _].
  apply:order_from_rel; split.
      move => b a c [ax bx ab] [_ cx bc]; split => //.
      case :(ab) => ab'; last by  ue.
      case :bc=> bc; last by  ue.
      move: (ha _ _ ax bx ab') => nba.
      case: (xp _ _ ax cx); first (by left); last first.
        by move => ac; case: nba; rewrite ac.
      move => ca.
    case: (hb _ _ _ ax bx cx).
        by move/set0_P=> h; case: (h a); apply/set3_P; constructor 1.
     move => [y /set3_P ya]; move /set0_P => h; case: ya => yv.
      case: (h c); rewrite yv;apply /setI2_P ; split=> //; apply/set3_P; in_TP4.
      case: (h a); rewrite yv;apply /setI2_P ; split=> //; apply/set3_P; in_TP4.
      case: (h b); rewrite yv;apply /setI2_P ; split=> //; apply/set3_P; in_TP4.
    move => a b [ax bx]; case => // ab [_ _]; case => // ba.
    case: (ha _ _  ax bx ab ba).
  by move => a b [ax bx etc]; split; split => //; right.
split =>  //; rewrite pa.
move => y yx /nonemptyP ney.
case: (hc _ yx) => // [] [z zy ztc].
exists z; red; rewrite (iorder_sr pb); last by ue.
split => // t ty; apply /iorder_gle0P => //.
move: (yx _ zy)(yx _ ty) =>  zx tx.
apply /graph_on_P1; split => //.
case: (xp _ _ zx tx); [ by left | move => tz; empty_tac1 t |  by right].
Qed.

Lemma well_founded_in_universe x: universe_i x ->
  well_founded_set x.
Proof.
move => ux f ff sf Hf xv.
have fu: forall i, natp i -> universe_i (Vf f i).
  apply: Nat_induction; first by rewrite -xv.
  by move => n nN /universe_stable_inc HR; exact: (HR _  (Hf _ nN)).
have rdec: forall n, natp n -> urank0  (Vf f (csucc n)) <o urank0 (Vf f n).
  by move => n nN; apply:(urank0_pr3 (fu _ nN) (Hf _ nN)).
set A := fun_image Nat (fun z => urank0 (Vf f z)).
have oA: ordinal_set A by move => t/funI_P [n /rdec /proj32_1 res ->]. 
have neA: nonempty A. 
  exists (urank0 (Vf f \0c)); apply/funI_P; exists \0c => //; apply: NS0.
move: (ordinal_setI neA oA); set v := intersection A => vA.
move/funI_P:vA => [n nN nv].
set t := (urank0 (Vf f (csucc n))).
have h: inc t A by apply/funI_P; exists (csucc n) => //; apply:NS_succ.
move:(rdec _ nN); rewrite - nv => /olt_i tv.
by move: ( (ordinal_irreflexive (oA _ h)) (setI_hi tv h)). 
Qed.

Lemma well_founded_universe a: ordinalp a ->
  forall x, inc x (universe a) <->
     (well_founded_set x /\ exists2 b , b<o a & urank_prop x b).
Proof.
move=> oa; split.
  move => xa; split.
    by apply: (well_founded_in_universe); exists a.
  by move: (urank_pr1 oa xa)=> [sa sb]; exists (urank a x).
by move => [sa [b /universe_inc1 lba [ob /setP_P sb _]]]; apply: lba.
Qed.

Section Foundation.
Hypothesis AF: foundation_axiom.

Lemma AF_infinite_seq x: well_founded_set x.
Proof.
move => f ff sf hf.
case: (AF (Imf f)).
  move => ie; empty_tac1 (Vf f \0c); apply/(Imf_P ff).
  rewrite sf; exists \0c => //; apply:NS0.
move => [y /(Imf_P ff) [u usf -> h]]; rewrite sf in usf.
case: (in_set0 (x := Vf f (csucc u))). rewrite -h.
empty_tac1 (Vf f (csucc u)).
by apply/(Imf_P ff); exists (csucc u) => //; rewrite sf;apply:NS_succ.
Qed.

Lemma AF_irreflexive x:  ~(inc x x).
Proof.
move => xx; case: (AF (singleton x)); first by apply/nonemptyP; fprops.
move => [y /set1_P -> /set0_P s]; case: (s x); apply /setI2_P; fprops.
Qed.

Lemma AF_asymmetric x: asymmetric_set x.
Proof.
move => u v _ _ uv vu.
case: (AF (doubleton u v)); first by apply /nonemptyP; exists u; fprops.
move => [y /set2_P]; case => ->; apply/nonemptyP.
  exists v;fprops.
exists u;fprops.
Qed.

Lemma AF_ordinal x: (ordinalp x <-> ordinal_altp x).
Proof. apply: ordinal_with_AF; move => y _; apply: AF. Qed.

Lemma AF_universe x: universe_i x.
Proof.
move: (tc_exists x) => []; set b1 := (transitive_closure x) => tb xb etc.
set b:= Zo b1 (fun z => ~(universe_i z)). 
case: (AF b).
   move => be; apply /universe_stable_inc => y yx; ex_middle bad.
   by empty_tac1 y; apply: Zo_i => //; apply: xb.
move => [y yb ye]; move: (Zo_S yb) => yb1.
move: (Zo_hi yb) => yne.
have [u uy nuu]: exists2 u, inc u y & ~ (universe_i u).
  ex_middle nxu; case: yne; apply /universe_stable_inc => s sx.
  ex_middle bad1; case: nxu; ex_tac.
by empty_tac1 u; apply:Zo_i => //; apply: (tb y). 
Qed.

Lemma urank0_pr2 x: urank_prop x (urank0 x).
Proof. by apply:urank0_pr1; apply: AF_universe. Qed.


End Foundation.


Lemma universe_AF x: universe_i x -> foundation_prop x.
Proof.
case: (emptyset_dichot x); first by left.
move => [e ex] [a oa xua]; right.
set U := fun_image x (urank a).
have neU: nonempty U by exists (urank a e); apply /funI_P; ex_tac.
have ose: ordinal_set U.
  move => b /funI_P [z zx ->]. 
  by move: (urank_pr1 oa (universe_trans oa xua zx)) => [/proj31_1].
move:(ordinal_setI neU ose); set y:= intersection U => yU.
move:  (ose _ yU) => yo.
move/funI_P: (yU) => [z zx zu]; ex_tac; apply /set0_P => t /setI2_P [tz tx].
have bu: inc (urank a t) U by apply /funI_P; ex_tac.
case: (ordinal_irreflexive (ose _ bu)); apply: (setI_s1  bu).
move:(universe_trans oa xua zx) => za.
by move: (urank_inc oa za tz)=> [ _]; rewrite - zu => /(oltP yo).
Qed.

Lemma AF_universe':  foundation_axiom <-> forall x, universe_i x.
Proof.
split; first by apply: AF_universe.
by move => h x; apply (universe_AF (h x)).
Qed.


Lemma universe_omega_props x: inc x (universe omega0) -> 
   [/\ finite_set x, sub x (universe omega0) & inc (urank omega0 x) Nat].
Proof.
have aux:= card_universe_fin.
move => xo.
move:(xo);rewrite {1} (universe_limit omega_limit) => /setUf_P [].
move => n nN etc; move:(OS_nat nN) => on.
split.
    move: (universe_inc2 (proj1 (oltS on)) etc).
    rewrite (universe_succ on); move /setP_P => sn.
    apply:(sub_finite_set sn (aux _ nN)).
  by apply: (universe_trans OS_omega).
move: (urank_pr1 on etc) => [[pa _] pb].
rewrite (urank_uniq2 OS_omega on xo etc).
apply/(oltP OS_omega).
move /(oltP OS_omega): nN; by apply: (ole_ltT).
Qed.


Lemma integer_in_Vomega x: inc x (universe omega0) ->
  (inc x Nat <->  ordinal_altp x).
Proof.
move => xu.
have hc: forall y, sub y x -> foundation_prop y.
  move => y yx;apply:universe_AF; exists omega0; first fprops.
  exact (proj1 (urank_sub OS_omega xu yx)).
split; first by move/OS_nat => /(ordinal_with_AF hc).
move /(ordinal_with_AF hc) => ox.
move: (proj31(universe_omega_props xu)) => fsx.
move: (card_card (CS_finite_o(ordinal_finite1 ox fsx))) => cx.
by apply/NatP; rewrite -  cx.
Qed.

Lemma universe_omega_hi x:
   finite_set x -> sub x (universe omega0) -> inc x (universe omega0).
Proof.
move => fxs ux.
set s := fun_image x (fun t => (urank omega0 t)).
case: (emptyset_dichot x) => nex.
  rewrite nex (universe_limit omega_limit);apply /setUf_P.
  exists \1o; first by apply: NS1.
  rewrite - osucc_zero (universe_succ OS0) universe_0.
  apply: setP_Ti.
have nes: nonempty s.
  exists (urank omega0 (rep x)); apply /funI_P;exists (rep x) => //.
  by apply: rep_i.
have fss: finite_set s by apply: finite_fun_image.
have sr: sub s Nat. 
  move => t /funI_P [z zx ->].
  by move: (universe_omega_props (ux _ zx)) => [].
move: (finite_subset_Nat sr fss nes) => [n].
move /funI_P => [z /ux /universe_omega_props [_ _ za] zb] pb.
set k := osucc (osucc n).
have on: ordinalp n by rewrite zb;  apply: OS_nat.
rewrite (universe_limit omega_limit); apply /setUf_P; exists k.
  by move: (proj33 omega_limit)=> rec; apply: (rec); apply: rec; rewrite zb.
rewrite universe_succ; last  by apply: OS_succ.
apply /setP_P => t tx.
have: inc (urank omega0 t) s by apply /funI_P; ex_tac.
move /pb => /ocle /universe_inc2 pd.
move :(urank_pr1 OS_omega (ux _ tx)) => [_ [_ pe _]].
rewrite (universe_succ on);apply/setP_P; apply: sub_trans pe pd.
Qed.


Lemma doubleton_in_Vomega x y (V := universe omega0):
   inc x V -> inc y V -> inc (doubleton x y) V.
Proof.
move => xv yv;apply:universe_omega_hi; first by apply: set2_finite.
by move => t/set2_P; case => ->.
Qed.

Lemma pair_in_Vomega x y (V := universe omega0):
   inc x V -> inc y V -> inc (J x y) V.
Proof.
  move => xv yv; rewrite kpairE.
by apply: doubleton_in_Vomega;apply: doubleton_in_Vomega.
Qed.


Definition rept_union x :=  Vf (induction_defined union x).
Definition finite_depth x := 
   exists2 n, natp n & rept_union x n = emptyset.
Definition rec_finite x:= forall n, natp n -> finite_set (rept_union x n).
Definition hereditarily_finite x := rec_finite x /\ finite_depth x.


Lemma rept_union_pr x (f := rept_union x):
   f \0c = x /\ (forall n, natp n -> f (csucc n) = union (f n)).
Proof.
move: (induction_defined_pr union x) => [pa pb pc pd]; split => //.
Qed.

Lemma rept_union_inc x y: inc y x ->
  forall n, natp n -> sub (rept_union y n) (rept_union x (csucc n)).
Proof.
move: (rept_union_pr y) => [sc sd] yx.
move: (rept_union_pr x) => [sa sb].
apply:Nat_induction.
    by rewrite sc (sb _ NS0) sa; apply: setU_s1.  
move => n nN Hrec.
rewrite (sd _ nN) (sb _ (NS_succ nN)).
move => t /setU_P [z tz /Hrec etc]; union_tac.
Qed.

Lemma hereditarily_finite_pr x:
  hereditarily_finite x -> 
  finite_set x /\ (forall y, inc y x -> hereditarily_finite y).
Proof.
move=> [pa [m mN xe]].
move: (rept_union_pr x) => [sa sb].
split; first by move: (pa _ NS0); rewrite sa.
move => y /rept_union_inc aux.
split.
  move => n nN; exact (sub_finite_set (aux _ nN) (pa _ (NS_succ nN))).
exists m; first by exact.
by move: (aux _ mN); rewrite (sb _ mN) xe setU_0 => /sub_set0.
Qed.

Lemma universe_omega_HF x: inc x (universe omega0) <-> 
   hereditarily_finite x.
Proof.
split; last first.
  move => [rf [n nb]]; move: n nb x rf.
  apply: Nat_induction.
    move => x rd; rewrite (proj1 (rept_union_pr x)) => ->.
    apply: universe_omega_hi; [apply:emptyset_finite | apply: sub0_set].
  move => n nN Hrec x recf fn.
  move: (rept_union_pr x) => [pa pb]; apply: universe_omega_hi.
    by move: (recf _ NS0); rewrite pa.
  move => t tx; move:(rept_union_inc tx nN); rewrite fn=> /sub_set0;apply: Hrec.
  move:(rept_union_inc tx) => aux.
  move => k kN; exact: (sub_finite_set (aux _ kN) (recf _ (NS_succ kN))).
move => h.
move: (rept_union_pr x) => [pa pb].
have aux: forall n, inc n Nat -> (inc (rept_union x n) (universe omega0)).
  apply: Nat_induction; first by rewrite pa.
  by move => n nN; move /(urank_union OS_omega)=> []; rewrite (pb _ nN).  
split; first by move => n /aux /universe_omega_props  [].
move:(proj33 (universe_omega_props h)); set n := urank _ _ => nN.
have rec: forall k, inc k Nat -> k <=c n -> 
     urank omega0 (rept_union x k) = n -c k.
  apply: Nat_induction; first by rewrite pa (cdiff_n0 nN).
  move => k kN Hrec skn.
  move: (urank_union OS_omega (aux _ kN)) => [_]; rewrite - (pb _ kN).
  suff: union (n -c k) = n -c csucc k.
     by move <-; rewrite (Hrec (cleT (proj1 (cltS kN)) skn)).
  move: (cdiff_pr skn); set c := n -c (csucc k).
  have cN: natp c by rewrite /c; fprops.
  rewrite (csum_Sn _ kN)  -(csum_nS _ cN) csumC => h1.
  rewrite (cdiff_pr2 (NS_succ cN) kN h1) (succ_of_nat cN) [union _]succo_K //.
  by apply: OS_nat.
move: (urank_pr1 OS_omega (aux _ nN)).
move: (rec _ nN (cleR (CS_nat nN))); rewrite cdiff_nn => ->.
by move => [_ [_]]; rewrite universe_0 => /sub_set0 sa _;exists n.  
Qed.


Lemma rept_union_inc2 x y n: natp n -> inc y (rept_union x (csucc n)) ->
  exists2 z, inc z x & inc y (rept_union z n).
Proof.
move => nN; rewrite (proj2 (rept_union_pr x) _ nN).
move: n nN x y;apply: Nat_induction.
  move => x y; rewrite (proj1 (rept_union_pr x)) => /setU_P [z yz zx];ex_tac. 
  by rewrite (proj1(rept_union_pr z)).
move => n nN Hrec x y.
rewrite (proj2 (rept_union_pr x) n nN) =>  /setU_P [z yz /Hrec [t tx zu]].
ex_tac; rewrite (proj2 (rept_union_pr t) n nN); union_tac.
Qed.

Lemma infinite_depth_prop x (f := rept_union x):
  (forall n, natp n -> (finite_set (f n) /\ nonempty (f n))) ->
  ~ (well_founded_set x).
Proof.
rewrite /f.
pose H x :=(forall n,
    inc n Nat -> finite_set (rept_union x n) /\ nonempty (rept_union x n)). 
rewrite -/(H x) => Hx wfx.
have aux: (forall x, H x -> exists2 y, inc y x & H y).
  move => z hz; ex_middle bad.
  move: (proj1 (rept_union_pr z)) => h0.
  case: (emptyset_dichot z) => znz.
   by move: (proj2 (hz _ NS0)); rewrite h0 znz; move => [t /in_set0].
  pose Ha x := (forall n, inc n Nat -> finite_set (rept_union x n)).
  have hay: forall y, inc y z -> Ha y.
    move => y yz n nN; move: (proj1 (hz _ (NS_succ nN))) => tu.
    by move: (rept_union_inc yz nN) => /sub_finite_set; apply.
    have hby: forall y, inc y z -> 
       exists2 n, inc n Nat & (rept_union y n) = emptyset.
      move => y yz; ex_middle bad2; case: bad; ex_tac.
      move => n nN; split; first by apply: (hay _ yz _ nN). 
      case: (emptyset_dichot (rept_union y n)) => // h; case: bad2; ex_tac.
    pose q y n := inc n Nat /\ (rept_union y n) = emptyset.
    pose tn y:= choose (q y).
    have tnp: forall y, inc y z -> q y (tn y).
       by move => y /hby [n nb etc]; apply: choose_pr; exists n.
    have tmp: forall y m, inc y z -> inc m Nat -> (tn y) <=c m ->
        rept_union y m = emptyset.
      move => y m yz mN le; rewrite - (cdiff_pr le); move: (NS_diff (tn y) mN).
      move: (tnp _ yz) => [sa sb].
      move: (m -c tn y); apply : Nat_induction; first by rewrite csum0r; fprops.
      move => n nN;rewrite (csum_nS _ nN).
      rewrite (proj2(rept_union_pr y) _ (NS_sum sa nN)) => ->; exact setU_0.
    have [n nN pn]: exists2 n, inc n Nat & forall y, inc y z -> (tn y) <=c n.
       set s := fun_image z tn.
       have p1: sub s Nat by  move => y /funI_P [t /tnp [aa _] ->].
       have p2: finite_set s. 
         by apply finite_fun_image; move: (proj1 (hz _ NS0)); rewrite h0.
       have p3: nonempty s by apply: funI_setne.
       move: (finite_subset_Nat p1 p2 p3) => [n ns etc].
       exists n; first by apply: p1.
       move => y yz; apply: etc; apply /funI_P; ex_tac.
   move: (proj2 (hz _ (NS_succ nN))) => [s sp].
   move: (rept_union_inc2 nN sp) => [y yz].
   by rewrite (tmp _ _ yz nN (pn _ yz)) => /in_set0.
pose p x y:= (inc y x /\ H y); pose nf x := choose (p x). 
move: (induction_defined_pr nf x); set g := induction_defined nf x.
move => [pa pb pc pd]. 
have pe: (forall n, inc n Nat -> inc (Vf g (csucc n)) (Vf g n)).
  have px: forall x, H x -> p x (nf x).
    by move => z /aux [y yz hy]; apply: (choose_pr); exists y.
  have py: forall n, inc n Nat ->p (Vf g n) (Vf g (csucc n)).
    apply: Nat_induction; first by rewrite (pd _ NS0) pc; apply: px.
    by move => n nN [_ h]; rewrite (pd _ (NS_succ nN)); apply: px. 
  by move => n /py [].
by case: (wfx g (proj1 pb) pa pe); rewrite - pc.
Qed.

(** Extensional sets *)



Definition extensional_set x := 
   (forall a b, inc a x -> inc b x -> a \cap x = b \cap x -> a = b).

Lemma transitive_extensional x: 
    transitive_set x -> extensional_set x.
Proof.
move => tx a b ax bx H; set_extens t => ts.
   have /setI2_P [] //:inc t (b \cap x).
   rewrite - H; apply/setI2_P; split => //; apply: (tx _ ax _ ts).
have /setI2_P [] //:inc t (a \cap x).
rewrite  H; apply/setI2_P; split => //; apply: (tx _ bx _ ts).
Qed.


Lemma extensional_pr X: foundation_axiom -> extensional_set X ->
  exists! f, [/\ bijection f, source f = X, transitive_set(target f) &
      forall a b, inc a X -> inc b X -> (inc a b <-> inc (Vf f a) (Vf f b))].
Proof.
move => pa pb; apply/unique_existence; split; last first.
  move => f g [[[ff ijf]  sjf] sf tf fp] [[[fg ijg] sjg] sg tg gp].
  set A:= Zo X (fun a => Vf f a <> Vf g a).
  case: (pa A).
    move => ae;apply: function_exten4 => //;[ ue | move => a ax; ex_middle bad].
    empty_tac1 a; apply:Zo_i => //; ue.
  move =>  [y /Zo_P [yX fgy] dya]; case: fgy.
  have sa: sub (y \cap X) (source f) by rewrite sf; apply:subsetI2r.
  have sb: sub (y \cap X) (source g) by rewrite sg; apply:subsetI2r.
  have ->: Vf f y = Vfs f (y \cap X).
    set_extens t. 
       move => tvf; apply/(Vf_image_P ff sa).
       have vft: inc (Vf f y) (target f) by Wtac.
       move:(tf _ vft _ tvf) => /(proj2 sjf) [u usf uv]; exists u; try ue.
       rewrite sf in usf; apply/setI2_P; split => //.
       by apply/(fp u y usf yX); ue. 
    by move/(Vf_image_P ff sa) => [u /setI2_P [uy uX] ->];apply/(fp u y uX yX).
  have ->: Vf g y = Vfs g (y \cap X).
    set_extens t. 
       move => tvf; apply/(Vf_image_P fg sb).
       have vft: inc (Vf g y) (target g) by Wtac.
       move:(tg _ vft _ tvf) => /(proj2 sjg) [u usf uv]; exists u; try ue.
       rewrite sg in usf; apply/setI2_P; split => //.
       by apply/(gp u y usf yX); ue. 
   by move/(Vf_image_P fg sb) => [u /setI2_P [uy uX] ->];apply/(gp u y uX yX).
  set_extens t. 
     move/(Vf_image_P ff sa) => [u ua ->];apply/(Vf_image_P fg sb); ex_tac.
     by move/setI2_P: ua => [uy uX];  ex_middle bad; empty_tac1 u;apply:Zo_i.
   move/(Vf_image_P fg sb) => [u ua ->];apply/(Vf_image_P ff sa); ex_tac.
   symmetry.
   by move/setI2_P: ua => [uy uX];  ex_middle bad; empty_tac1 u;apply:Zo_i.
pose W x := inc x X.
have ha: (forall x, W x -> ordinalp (urank0 x)).
   by move => x wx; move:(urank0_pr2 pa x) => [].
have hb: (forall i,  ordinalp i ->
        exists E, forall x : Set, inc x E <-> W x /\ urank0 x <o i).
  move => i oi; exists (Zo X (fun z => urank0 z <o i)) => x; split.
    by move /Zo_P. by move => h; apply/Zo_P.
pose H x f := Zo (range f) (fun z => exists2 t, inc t (x \cap X) & z = Vg f t).
move: (stratified_fct_pr H ha hb) => Ha.
set F:= stratified_fct W H urank0.
have hd: forall x, inc x X -> F x = fun_image (x \cap X) F. 
  move => x xX; rewrite /F (Ha _ xX) -/F.
  have ->: stratified_set W urank0 (urank0 x)
        = Zo X (fun t => urank0 t <o urank0 x). 
    have oi:= ha _ xX. 
    have hc:=(stratified_setP hb oi).
    set_extens t; [by move/hc=> hd; apply/Zo_P | by  move/Zo_P/hc ].
  rewrite /H; set_extens t.
    move => /Zo_P [/Lg_range_P [b /Zo_P [qa qb] ->] [v va ->]].
    rewrite LgV; first by apply/funI_P; ex_tac.
     move/setI2_P: va => [vx vX]; apply:Zo_i => //.  
     apply:(urank0_pr3 (AF_universe pa x) vx).
  move=>/funI_P [z /setI2_P [zx zX] ->].
  have he: inc z (Zo X (fun u => urank0 u <o urank0 x)).
   by apply:Zo_i => //; apply:(urank0_pr3 (AF_universe pa x) zx).
  apply /Zo_P; split; first by apply/Lg_range_P;exists z => //; apply:Zo_i. 
  exists z; [  by apply/setI2_P | rewrite LgV//].
have he: forall x, ordinalp x -> 
   forall a b, inc a X -> inc b X -> (urank0 a) <o x -> (urank0 b) <o x -> 
               F a = F b -> a = b.
  pose p x := forall a b : Set,
   inc a X -> inc b X -> urank0 a <o x -> urank0 b <o x -> F a = F b -> a = b.
  move => x ox; case:(least_ordinal6 p ox) => //.
  set alpha := least_ordinal  _ _.
  move => [oa hrec]; case => a b ax bx h1 h2.
  rewrite (hd _ ax) (hd _ bx) => h; apply: (pb _ _ ax bx).
  have aux: forall u v, inc u (a \cap X) -> inc v (b \cap X) ->
       F u = F v -> u = v.
    move => u v /setI2_P [ua uX] /setI2_P [ub vX].
    have ra:= (urank0_pr3 (AF_universe pa a) ua).
    have rb:= (urank0_pr3 (AF_universe pa b) ub).
    move:(proj31_1 h1)(proj31_1 h2) => o1 o2.
    set c:= Yo (urank0 a <=o urank0 b) (urank0 b) (urank0 a).
    have ca:  (urank0 a) <=o c by rewrite /c; Ytac hu;fprops.
    have cb: (urank0 b) <=o c. 
      rewrite /c; Ytac hu; fprops.
      by case: (oleT_el o2 o1) => // [][].
    have cc: c <o alpha by rewrite /c; Ytac hu => //. 
    have ica: inc c alpha by apply /(oltP oa). 
    apply:((hrec _ ica) _ _ uX vX (olt_leT ra ca)(olt_leT rb cb)).
  set_extens t => ta.
    have: inc (F t) (fun_image (b \cap X) F)
      by rewrite -h ; apply/funI_P; ex_tac.
    move /funI_P => [z za zb]; have -> //: t = z by apply: aux.
  have: inc (F t) (fun_image (a \cap X) F).
      by rewrite h ; apply/funI_P; ex_tac.
    move /funI_P => [z za zb]; have <- //: z = t by apply: aux.
have hf: forall a b, inc a X -> inc b X -> F a = F b -> a = b.
  move => a b aX bX. 
  move:(ha _ aX) (ha _  bX) => oa ob.
  set c:= Yo (urank0 a <=o urank0 b) (urank0 b) (urank0 a).
  have ca:  (urank0 a) <=o c by rewrite /c; Ytac hu; fprops.
  have cb: (urank0 b) <=o c. 
      rewrite /c; Ytac hu; fprops.
      by case: (oleT_el ob oa) => // [][].
  have sa:= (oltS (proj32 ca)).
  exact: (he _ (proj32_1 sa) _ _ aX bX (ole_ltT ca sa) (ole_ltT cb sa)).
set T:= fun_image X F.
have ax: forall a, inc a X -> inc (F a) T.
   move => a ax; apply/funI_P; ex_tac.
set f := Lf F X T.
exists f;split => //.
+ by apply: lf_bijective => // y /funI_P.
+ by rewrite /f; aw.
+  rewrite /f; aw; move => Y /funI_P [z zx]; rewrite (hd _ zx).
   move => -> t /funI_P [u /setI2_P [ua ub ->]]; apply/funI_P; ex_tac.
+ move => a b aX bX; rewrite /f !LfV// (hd _ bX); split. 
    by move => ab; apply /funI_P; exists a=> //; apply/setI2_P.
  by move => /funI_P [z /setI2_P [za zx]] /(hf _ _ aX zx) ->.
Qed.


(** Axiom of choice *)

Lemma AC_variants: 
   let AC:= forall x, (forall z, inc z x -> nonempty z) ->
      (forall z z', inc z x -> inc z' x -> z = z' \/ disjoint z z') ->
      (exists y, forall z, inc z x -> singletonp (y \cap z)) in
   (AC -> (forall f, nonempty_fam f -> nonempty (productb f)))
   /\ (AC -> forall x, exists y,
      [/\ fgraph y, domain y = \Po x -s1 emptyset &
        forall z, sub z x -> nonempty z -> inc (Vg y z) z])
   /\ ((forall x, exists r, forall z, inc z x -> nonempty z -> inc (r z) z)
        -> AC).
Proof.
move => AC.
have pr1: AC -> (forall f, nonempty_fam f -> nonempty (productb f)).
  move => ac f nef.
  set d := domain f.
  set x := fun_image d (fun z => (singleton z) \times (Vg f z)).
  have pa: (forall z, inc z x -> nonempty z).
    move => z /funI_P [u /nef [v ud] ->];exists (J u v); apply: setXp_i; fprops.
  have pb: (forall z z', inc z x -> inc z' x -> z = z' \/ disjoint z z').
    move => z z' /funI_P [u /nef _ ->] /funI_P [v /nef _ ->].
    case: (equal_or_not u v); first by move => ->; left.
    move => uv; right; apply: disjoint_pr => w /setX_P [_ /set1_P pw _].
    by move =>  /setX_P [_ /set1_P pw' _]; case: uv; rewrite -pw -pw'.
  move: (ac _ pa pb) => [y yp].
  set y1:= y \cap (union x).
  have yp': forall z, inc z x -> singletonp (y1 \cap z).
    move => z zx; move/yp: (zx) => [t t1];exists t; apply: set1_pr.
      move: (set1_1 t); rewrite -t1 => /setI2_P [ty tz]; apply /setI2_P. 
      split => //; apply /setI2_P; split => //; union_tac.
    move => u /setI2_P [/setI2_P [p1 p2] p3].
    by apply /set1_P; rewrite -t1; apply /setI2_P.
  have pc: forall s, inc s y1 -> 
    exists2 b, inc b d & let a:=  singleton b \times Vg f b in
      [/\ inc a x, y1 \cap a = singleton s & inc s (singleton b \times Vg f b)].
    move => s sy1; move: (sy1) => /setI2_P [_ /setU_P [a sa sb]].
    have pc:inc s (y1 \cap a) by apply /setI2_P.
    move /funI_P: (sb) => [b ba bb]; ex_tac; rewrite -bb; split => //.
    apply: set1_pr1; first by exists s.
    by move => z za; move:(yp' _ sb) => /singletonP [_ ss]; apply ss.
  have sy1: fgraph y1.
     split; first by move => t /pc [b _ [_ _ /setX_P []]].
     move => s s' s1 s2 sp.
     move: (pc _ s1)(pc _ s2) => [a ax [i1a i2a i3a]] [b bx [i1b i2b i3b]].
     move: i3a i3b => /setX_P [_ /set1_P psa _] /setX_P [_ /set1_P psb _].
     by apply: set1_inj; rewrite -i2a -i2b - psa sp psb.
  have dy1: domain y1 = domain f.
     set_extens t. 
       by move /funI_P => [z /pc [b bd [_ _ /setX_P [_ /set1_P -> _]]]-> ].
     move => tdf.
     set z := (singleton t \times Vg f t).
     have zx: inc z x by apply /funI_P;ex_tac.
     move: (yp' _ zx) => [a sa].
     have ay1: inc a y1 by move: (set1_1 a); rewrite - sa => /setI2_P [].
     have : inc a z by move: (set1_1 a); rewrite - sa => /setI2_P [].
     move => /setX_P [_ /set1_P pat _].
     apply /funI_P; by ex_tac.
  exists y1; apply /setXb_P; split => //.
  move => i idf.
  set z := (singleton i \times Vg f i).
  have zx: inc z x by apply /funI_P;ex_tac.
  move: (yp' _ zx) => [a sa].
  have ay1: inc a y1 by move: (set1_1 a); rewrite - sa => /setI2_P [].
  move: (pc _ ay1) => [b b1 [b2 b3 b4]].
  have : inc a z by move: (set1_1 a); rewrite - sa => /setI2_P [].
  move => /setX_P [_ /set1_P pat _].    
  move: (set1_1 a); rewrite -b3 => /setI2_P [_ /setX_P [_ /set1_P sb sc]].
  by rewrite - pat - (pr2_V sy1 ay1) sb.
have pr2: (AC -> forall x, exists y,
      [/\ fgraph y, domain y = \Po x -s1 emptyset &
        forall z, sub z x -> nonempty z -> inc (Vg y z) z]).
  move => ac x; set f := Lg (\Po x -s1 emptyset) id.
  have : nonempty_fam f. 
    by rewrite /f;hnf; aw;move => t tp; rewrite LgV//; move /setC1_P: tp => [_ /nonemptyP].
  move /(pr1 ac) => [y /setXb_P [pa pb pc]]; exists y; split => //.
    by rewrite pb /f;aw.
  move => z zb zne.
  have zi: inc z (\Po x -s1 emptyset).
     apply /setC1_P; split => //; [by apply/setP_P | by apply /nonemptyP].
  have: inc z (domain f) by rewrite /f; aw.
  move /pc;rewrite /f LgV//.
have pr3: (forall x : Set,
     exists r : Set -> Set,
       forall z : Set, inc z x -> nonempty z -> inc (r z) z) -> AC.
  move => h x x1 x2; move: (h x) => [r ra].
  set y := fun_image x r; exists y => z zx.
  have p1: inc (r z) z by apply: ra => //; apply: x1.
  have p2: inc (r z) y by apply /funI_P;ex_tac.
  apply/singletonP; split; first by exists (r z); apply/ setI2_P.
  move => a b /setI2_P [/funI_P [u ua ub] az] /setI2_P [/funI_P [v va vb]  bz].
  move: (ra _ ua (x1 _ ua)) (ra _ va (x1 _ va)) => uc vc.
  move: (x2 _ _ zx ua); case => zu; last by empty_tac1 a; ue.
  move: (x2 _ _ zx va); case => zv; last by empty_tac1 b; ue.
  by rewrite ub vb - zu -zv.
done.
Qed.


Section ModelTheory.
Variables (U: property)(R: relation).

Definition unionA_pr x u :=
  U u /\ (forall y, U y -> (R y u <->
            (exists z, [/\ U z, R z x & R y z]))).
Definition powersetA_pr x p:= 
  U p /\  (forall y, U y -> (R y p <->
             (forall t, U t -> R t y -> R t x))).
Definition comprehensionA_pr x (p:property) c :=
  U c /\  (forall z, U z -> (R z c <-> (R z x /\ p z))).
Definition replacementA_pr x (p:property) (f: fterm) r :=
  U r /\ (forall z, U z -> 
        (R z r <-> (exists2 t, U t & [/\ R t x, p t & z = f t]))). 
Definition emptysetA_pr e:= U e /\ forall t, U t -> ~ (R t e).

Definition pairA_pr a b p := 
  U p /\  (forall t, U t -> (R t p <-> t = a \/ t = b)).

Definition extensionalityA :=
  (forall x y, U x -> U y -> (forall z, U z -> (R z x <-> R z y)) ->
       x = y).

Definition unionA :=  forall x, U x -> exists u, unionA_pr x u.
Definition powersetA :=  forall x, U x -> exists p, powersetA_pr x p.
Definition comprehensionA :=
   forall x (p:property), U x -> exists c, comprehensionA_pr x p c.
Definition replacementA :=
  forall x (p: property) f, U x -> 
      (forall t, U t ->  R t x -> p t -> U (f t)) ->
     exists r, replacementA_pr x p f r.
Definition pairA :=  forall a b, U a -> U b -> exists c, pairA_pr a b c.


Lemma model_uniqueness: extensionalityA ->
  [/\ forall x, uniqueness (unionA_pr x),
      forall x, uniqueness (powersetA_pr x),
      forall x p, (uniqueness (comprehensionA_pr x p)),
      forall x p f, (uniqueness (replacementA_pr x p f)) &
      uniqueness emptysetA_pr /\
      forall a b, uniqueness (pairA_pr a b)].
Proof.
move => ea.
have pa: forall x, uniqueness (unionA_pr x).
  move => x  y1 y2 [u1 p1] [u2 p2]; apply ea => // z uz; split.
    by move /(p1 _ uz) => [t [ta tb tc]]; apply /(p2 _ uz); exists t.
    by move /(p2 _ uz) => [t [ta tb tc]]; apply /(p1 _ uz); exists t.
have pb: forall x, uniqueness (powersetA_pr x).
   move => x y1 y2 [u1 p1] [u2 p2]; apply ea => // z uz; split.
     by move /(p1 _ uz) => h; apply  /(p2 _ uz).
     by move /(p2 _ uz) => h; apply  /(p1 _ uz).
have pc: forall x p, (uniqueness (comprehensionA_pr x p)).
   move => x p y1 y2 [u1 p1] [u2 p2]; apply ea => // z uz; split.
     by move /(p1 _ uz) => h; apply  /(p2 _ uz).
     by move /(p2 _ uz) => h; apply  /(p1 _ uz).
have pd: forall x p f, (uniqueness (replacementA_pr x p f)).
   move => x p f y1 y2 [u1 p1] [u2 p2]; apply ea => // z uz; split.
     by move /(p1 _ uz) => h; apply  /(p2 _ uz).
     by move /(p2 _ uz) => h; apply  /(p1 _ uz).
have pe: uniqueness emptysetA_pr.
  move => e e' [u1 p1] [u2 p2]; apply: ea => // z uz; split => h.
      by case: (p1 _ uz).
      by case: (p2 _ uz).
have pf: forall a b, uniqueness (pairA_pr a b).
   move => a b y1 y2 [u1 p1] [u2 p2]; apply ea => // z uz; split.
     by move /(p1 _ uz) => h; apply  /(p2 _ uz).
     by move /(p2 _ uz) => h; apply  /(p1 _ uz).
split => //.
Qed.

Lemma model_replacement_comprehension:  replacementA -> comprehensionA.
Proof.
move =>  h x p ux.
have su:(forall t, U t -> R t x -> p t -> U t) by move => t.
move: (h x p id ux su)=> [r [r1 r2]]; exists r; split => // z uz.
split; first by move /(r2 _ uz)=> [t _ [ta tb ->]].
by move=> [pa pb]; apply /(r2 _ uz); exists z.
Qed.


Definition emptysetU := choose (fun z => emptysetA_pr z).
Definition unionU x:= choose (fun z => unionA_pr x z).
Definition powersetU x:= choose (fun z => powersetA_pr x z).
Definition setofU x p := choose (fun z => comprehensionA_pr x p z).
Definition funimageU x p f := choose (fun z => replacementA_pr x p f z).
Definition doubletonU a b := choose (fun z => pairA_pr a b z).

Definition ZF_axioms1 :=
  [/\  (exists x, U x), extensionalityA, unionA, powersetA & replacementA].

Lemma model_existence: ZF_axioms1 -> 
  [/\  emptysetA_pr (emptysetU),
       forall x, U x -> unionA_pr x (unionU x),
       forall x, U x -> powersetA_pr x (powersetU x),
       forall x r, U x -> comprehensionA_pr x r (setofU x r) &
       forall x (p: property) f, 
           U x -> (forall t, U t -> R t x -> p t -> U (f t)) ->
       replacementA_pr x p f (funimageU x p f)].
Proof.
move => [[x0 ux0] ea ua pa ra].
move: (model_replacement_comprehension ra) => ca.
have p1:  emptysetA_pr (emptysetU).
  apply: choose_pr.
  move :(ca x0 (fun t => ~(R t x0)) ux0) => [c [c1 c2]].
  by exists c; split => // t ut; move /(c2 _ ut) => [].
have p2: forall x, U x -> unionA_pr x (unionU x).
   move => x /ua;  apply: choose_pr.
have p3: forall x, U x -> powersetA_pr x (powersetU x).
   move => x /pa;  apply: choose_pr.
have p4: forall x r, U x -> comprehensionA_pr x r (setofU x r).
   move => x r /ca => h; apply: choose_pr; apply: h.
have p5: forall x (p: property) f, 
   U x -> (forall t, U t -> R t x -> p t -> U (f t)) ->
   replacementA_pr x p f (funimageU x p f).
   move => x p f ux hf; apply: choose_pr; exact: (ra _ _ _ ux hf).
done.
Qed.

Lemma model_existence2 : ZF_axioms1 -> 
  forall a b, U a -> U b -> pairA_pr a b (doubletonU a b).
Proof.
move => ax a b ua ub. 
move: (model_existence ax) => [ea una pa ca ra].
move: ax => [es eaa uaa paa raa].
move: ea => []; set e := emptysetU => [ea1 ea2].
move: (pa _ ea1) => []; set e1 := (powersetU e) => [eb1 eb2].
have qa: R e e1 by apply /(eb2 _ ea1).
have qb: forall x, U x -> (R x e1 <-> x = e).
   move => x xu; split; last by move ->.
   move /(eb2 _ xu) => te; apply:(eaa _ _  xu ea1) => s us; split.
      apply: (te _ us).
   by move => v; case: (ea2 _ us).
have ee1: e1 <> e.
  by move => ee1; move /(qb _ eb1): (ee1); rewrite  ee1; apply: ea2.
move: (pa _ eb1) => []; set e2 := (powersetU e1) => [ec1 ec2].
have qc: R e e2 by apply /(ec2 _ ea1) => t ut ba; case: (ea2 _ ut).
have qd: R e1 e2 by apply /(ec2 _ eb1).
have qe: forall x, U x -> (R x e2 <-> x = e \/ x = e1).
   move => x Ux; split; last by case => ->;[ apply qc | apply: qd].
   move => xe2;  move/ (ec2 _ Ux): xe2 => sa.
   case: (equal_or_not x e) => xne; [by left | right].
   apply: (eaa _ _ Ux eb1) => z uz; split; first by apply: sa.
   move /(qb _ uz) => ->. 
   case: (p_or_not_p (exists2 t, U t & R t x)).
    by move => [t ut tx]; move /(sa _ ut): (tx) => /(qb _ ut) => <-.
  move => ne; case: xne; apply: (eaa _ _ Ux ea1) => s su; split.
    by move => sx; case: ne; exists s.
  by move => sz; case: (ea2 _ su).
pose f := variant e a b.
have fa: f e = a by  rewrite /f /variant; Ytac0.
have fb: f e1 = b by  rewrite /f /variant; Ytac0.
have fp: (forall t, U t -> R t e2 -> True -> U (f t)).
  by move => t _ _ _; rewrite /f /variant;Ytac h.
move: (ra e2 (fun _ => True) f ec1 fp)=> []. 
set c := funimageU _ _ _ => [c1 c2].
apply: choose_pr; exists c;split => // t ut; split.
  move/(c2 _ ut) => [s us [/(qe _ us) rs2 _ ->]]. 
  by case: rs2 => ->; [ left | right].
case => ->. 
  by apply /(c2 _ ua); exists e. 
by apply /(c2 _ ub); exists e1.
Qed.

Definition unionU2 a b :=  unionU (doubletonU a b).
Definition intersectionU2 a b := setofU a (fun z => R z b).

Lemma model_union: ZF_axioms1 -> 
  forall a b, U a -> U b ->
  ( (forall z, U z -> (R z (unionU2 a b) <-> R z a \/ R z b)))
   /\ (forall z, U z -> (R z (intersectionU2 a b) <-> R z a /\ R z b)).
Proof.
move => ax a b ua ub.
move: (model_existence ax) => [ea una pa ca ra].
rewrite /unionU2 /intersectionU2.
move: (model_existence2 ax ua ub) => []; set c := (doubletonU a b) => cu cp.
split.
  move => z uz; move: (una c cu) => [u1 u2]; split.
     by move /(u2 _ uz) => [t [tu /(cp _ tu)]]; case => ->; [left| right].
  case => zx; apply /(u2 _ uz); [exists a | exists b];split => //.
    by apply/ (cp _  ua); left.
    by apply/ (cp _  ub); right.
move=> z uz.
move: (ca a (fun z =>  R z b) ua) => []; set d := (setofU _ _) => [du].
by apply.
Qed.

Definition choiceA:= forall x, 
    U x -> (forall z, U z -> R z x -> z <> emptysetU) ->
    (forall z1 z2, U z1 -> U z2 -> R z1 x -> R z2 x ->
        (z1 = z2 \/ intersectionU2 z1 z2 = emptysetU)) ->
   exists2 y, U y &
     forall z, U z -> R z x -> exists2 s, U s & 
       intersectionU2 y z = doubletonU s s.
Definition infiniteA:=
   exists2 x, U x &
    (R emptysetU x /\ 
     forall t, U t -> R t x -> R (unionU2 t (doubletonU t t)) x).
Definition foundationA :=
  forall x, U x -> 
  x = emptysetU \/ exists2 y, U y &
     R y x /\ intersectionU2 y x = emptysetU.

End ModelTheory.

Lemma universe_mo1 (U: property): 
   (forall x y, U x ->  inc y x -> U y) ->
   (forall x y, U x ->  sub y x -> U y) ->
  (extensionalityA U inc)
  /\ (forall x r, U x -> (setofU U inc x r) = (Zo x r))
  /\ (comprehensionA U inc)
  /\ (forall x, U x -> U (union x) ->
      (unionA_pr U inc x (union x)) /\ (unionU U inc x = union x))
  /\ (forall x, U x -> U (powerset x) ->
      (powersetA_pr U inc x (powerset x)) /\ (powersetU U inc x = powerset x))
  /\ ( forall a b, U a -> U b -> U (doubleton a b) ->
       (pairA_pr U inc a b  (doubleton a b))
       /\ (doubletonU U inc a b = doubleton a b))
  /\ (forall a b, U a -> intersectionU2 U inc a b = a \cap b)
  /\ (forall a b, U a -> U b -> U (doubleton a b) -> U (a\cup b) ->
     unionU2 U inc a b = a \cup b)
  /\ ((exists x, U x) -> emptysetU U inc = emptyset)
  /\ ((forall a, inc a omega0 -> U (singleton a))
   -> (forall a, inc a omega0 -> U (doubleton a (singleton a)))
   -> U omega0 
   -> infiniteA U inc)
  /\ ( (forall a b, U a -> U b -> U (doubleton a b)) ->
       (forall a b, U a -> U b -> U (a \cup b)) ->
        infiniteA U inc -> U omega0)
  /\ ( (forall x, U x -> x = emptyset \/ exists2 y, U y &
     inc y x /\ disjoint y x) -> foundationA U inc).
Proof.
move => su su'.
have p1: extensionalityA U inc.
  move => x y ux uy h; apply: extensionality => t ta.
    by apply /(h _ (su _ _ ux ta)).
  by apply /(h _ (su _ _ uy ta)).
move: (model_uniqueness p1) => [uu up uc ur [ue upa]].
have aux: forall (p:property) x, p x -> uniqueness p -> (choose p) = x. 
  by move => p x px unp; apply: unp => //; apply: choose_pr; exists x.
have p2: forall x p, U x -> (comprehensionA_pr U inc x p (Zo x p)).
  move => x p ux; split; first by apply: (su' x _  ux); apply: Zo_S.
  by move => z uz; split; move/Zo_P.
have p3:  (comprehensionA U inc).
  by move => x p ux; exists (Zo x p); apply: p2.
have p4: (forall x r, U x -> (setofU U inc x r) = (Zo x r)).
  move => x p ux; apply: aux; [ by apply: p2 | apply: uc].
have p5: forall x, U x -> U (union x) ->
  (unionA_pr U inc x (union x)) /\ (unionU U inc x = union x).
  move => x ux uux.
  have pa:unionA_pr U inc x (union x). 
    split=> // y uy; split => //.
       move /setU_P => [z za zb]; exists z; split => //; apply: (su _ _ ux zb).
    move => [z [_ zx zy]]; union_tac.
  split => //; apply: aux; [ by apply: pa | apply: uu].
have p6: (forall x, U x -> U (\Po x) ->
  (powersetA_pr U inc x (\Po x)) /\ (powersetU U inc x = \Po x)).
  move => x ux uux.
  have pa:(powersetA_pr U inc x (\Po x)).
    split => // y uy; split.
     move /setP_P => yx t _; apply: yx. 
     move => h; apply /setP_P => t tx; apply: h => //;apply (su _ _ uy tx).
  split => //; apply: aux; [ by apply: pa | apply: up].
have p7: forall a b, U a -> intersectionU2 U inc a b = a \cap b.
  move => a b ua ; rewrite /intersectionU2 (p4 _ _ ua);set_extens t.
    by move /Zo_P /setI2_P.
    by move /setI2_P => h; apply/Zo_P.
have p8: forall a b, U a -> U b -> U (doubleton a b) ->
  (pairA_pr U inc a b  (doubleton a b))
   /\ (doubletonU U inc a b = doubleton a b).
  move => a b ua ub uab.
  have pa:(pairA_pr U inc a b  (doubleton a b)).
    split=> // y uy; split => //; by move /set2_P.
  split => //; apply: aux; [ by apply: pa | apply: upa].
have p9: forall a b, U a -> U b -> U (doubleton a b) -> U (a\cup b) ->
  unionU2 U inc a b = a \cup b.
  move => a b ua ub ud uab.
  rewrite /unionU2 (proj2 (p8 _ _ ua ub ud)).
  by rewrite (proj2 (p5 _ ud uab)).
have p0: (exists x, U x) -> emptysetU U inc = emptyset.
  move => [x Ux]; apply: aux => //.
  split; last by move => t _ /in_set0.
  move: (p2 x (fun _:Set => False) Ux) => [].
  have -> // : (Zo x (fun _ : Set => False))= emptyset.
    apply /set0_P; apply :Zo_hi.
have p10: 
   (forall a, inc a omega0 -> U (singleton a))
   -> (forall a, inc a omega0 -> U (doubleton a (singleton a)))
   -> U omega0 
   -> infiniteA U inc.
  move=> q1 q2 q3; exists omega0 => //.
  move: omega_limit => [o1 o2 o3].
  have neu: (exists x, U x)  by exists omega0.
  rewrite (p0 neu); split; [exact | move => t ut to].
  move: (p8 _ _ ut ut (q1 _ to))=> [[sa _] ->]. 
  move: (o3 _ to) => so.
  by rewrite (p9 _ _ ut sa (q2 _ to)  (su _ _ q3 so)).
have p11:((forall a b, U a -> U b -> U (doubleton a b)) ->
    (forall a b, U a -> U b -> U (a \cup b)) ->
    infiniteA U inc -> U omega0). 
  move => pa pb [u ux [uy uz]].
  have ee: (exists x : Set, U x)  by exists u.
  rewrite (p0 ee) in uy.
  have pc: forall t, inc t u -> inc (osucc t) u.
    move => t tu; move: (su _ _ ux tu) => ut.
    move: (uz _ ut tu); move: (pa _ _ ut ut) => utt.
    rewrite (proj2 (p8 _ _ ut ut utt)).
    move: (pa _ _ ut utt) => ut3.
    by rewrite (p9 _ _ ut utt ut3 (pb _ _ ut utt)).
  have: sub omega0 u.
    by apply:Nat_induction => // n nN /pc; rewrite succ_of_nat.
  by apply: su'.
have p12:  (forall x, U x -> x = emptyset \/ exists2 y, U y &
     inc y x /\ disjoint y x) -> foundationA U inc.
  move => hyp x ux. 
  have neu: (exists x, U x)  by exists x.
  rewrite (p0 neu); case: (hyp _ ux);[ by left | move => [y yu [yx di]]; right].
  by exists y => //; rewrite (p7 _ _ yu).
done.
Qed.

Lemma universe_mo2 :
   let U := universe_i in
     [/\ ZF_axioms1 U inc, comprehensionA U inc,
        infiniteA U inc, choiceA U inc & foundationA U inc].
Proof.
set U := universe_i => /=.
have pa: forall x y, U x ->  inc y x -> U y. 
   move => x y /universe_stable_inc; apply.
have pa': forall x y, U x ->  sub y x -> U y. 
   move => x y ux yx; apply /universe_stable_inc => t ty. 
   apply:(pa _ _ ux (yx _ ty)).
move: (universe_mo1 pa pa')=>
    [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p10b p11]]]]]]]]]]].
have q1: (forall x, U x -> U (union x)).
  move => x ux; apply /universe_stable_inc => y /setU_P [z za zb].
  exact (pa _ _ (pa _ _ ux zb) za). 
have q2: unionA U inc.
  by move =>x ux; move: (p4 _ ux (q1 _ ux)) => [h _]; exists (union x).
have q3: (forall x : Set, U x -> U (\Po x)).
  by move => x ux; apply /universe_stable_inc => y /setP_P; apply: pa'.
have q4: powersetA U inc.
  by move =>x ux; move: (p5 _ ux (q3 _ ux)) => [h _]; exists (\Po x).
have q5: replacementA U inc.
  move => x p f ux fp; exists (fun_image (Zo x p) f); split.
    apply/universe_stable_inc => s /funI_P [z /Zo_P [za zb] ->].
    by apply:fp => //; apply: (pa _ _  ux za).
  move => z uz; split. 
       move /funI_P => [s /Zo_P [r1 r2] ->]; exists s => //.
       apply: (pa _ _  ux r1).
  by move => [t ut [tx pt ->]]; apply /funI_P; exists t => //;apply /Zo_P.
have q6: U omega0 by apply (universe_ordinal OS_omega).
have q7: exists x, U x by exists omega0.
have q8:  (ZF_axioms1 U inc) by [].
move: (model_existence2 q8) => p12.
have pru: forall a b, U a -> U b -> U (doubleton a b).
  by move => a b ua ub; apply  /universe_stable_inc=> y /set2_P; case => ->.
have q9: infiniteA U inc.
  have qq:forall a, inc a omega0 -> U (singleton a).
    move => a ao; apply: pru; apply: (pa _ _ q6 ao).
  apply: p10 => //.
  by move => a ao; apply: pru => //; [ apply: (pa _ _ q6 ao) | apply: qq].
have q10: foundationA U inc.
  apply p11 => x xu; case:(universe_AF xu);[ by left| move => [y yx dx]; right].
  exists y => //; apply (pa _ _ xu yx).
split => //.
move => x xu; rewrite (p9 q7); move => xx1 xx2.
set y := fun_image x rep.
have pc:  forall t, inc t x -> inc (rep t) t.
   move => t tx; apply: rep_i; apply /nonemptyP; apply: xx1 => //.
   apply: (pa _ _ xu tx).
have pd: forall t, inc t x -> U (rep t).
  move => t tx; exact: (pa _ _ (pa _ _ xu tx)  (pc _ tx)).
have yU: U y. 
  by apply /universe_stable_inc => s /funI_P [z zx ->]; apply: pd.
exists y => // z _ zx; exists (rep z); first by apply: pd.
rewrite (p7 _ _ yU).
have ->: doubletonU U inc (rep z) (rep z) = (singleton (rep z)).
  move: (p12 _ _ (pd _ zx) (pd _ zx)) => [s1 s2].
   apply: extensionality.
     move => t ts; apply /set1_P. 
     by move: (s2 _ (pa _ _ s1 ts)) => h; move /h: ts; case.
   by move => t /set1_P ->; apply /(s2 _ (pd _ zx)); left.
apply: set1_pr.
  apply /setI2_P; split; [apply /funI_P; ex_tac | by apply: pc].
move => t /setI2_P [/funI_P [u ux -> t2]].
case: (xx2 _ _ (pa _ _ xu zx) (pa _ _  xu ux) zx ux); first by move ->.
rewrite (p7 _ _ (pa _ _ xu zx)) => di; empty_tac1 (rep u).
Qed.

Lemma universe_mo' a (U :=fun z => inc z (universe a)) :
  ordinalp a -> 
  ( (forall x y, U x ->  inc y x -> U y) /\ 
    (forall x y, U x ->  sub y x -> U y)).
Proof.
move => oa.
rewrite /U; split; first by move => x y xy; apply: (universe_trans oa).
by move => x y xua /(urank_sub oa xua) [].
Qed.

Lemma universe_mo3 a (U :=fun z => inc z (universe a)) :
  limit_ordinal a ->
  [/\ [/\ (exists x, U x), (extensionalityA U inc), (unionA U inc),
      (powersetA U inc) & comprehensionA U inc], 
       ((forall x : Set, U x -> U (powerset x)) /\ 
       (forall x y, U x -> U y -> U (doubleton x y))),
       (omega0 <o a <-> infiniteA U inc), choiceA U inc & foundationA U inc].
Proof.
move => /limit_ordinal_P [anz la].
have la': forall t, osucc t <=o a ->
   sub (universe (osucc (osucc t))) (universe a).
   by move =>  t /oleSltP /la  /oleSltP/universe_inc2.
have oa:= (proj32_1 anz).
move: (universe_mo' oa) => [pa pb].
move: (universe_mo1 pa pb)
   =>[p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p10b p11]]]]]]]]]]].
have q1: (forall x, U x -> U (union x)).
   move =>x ux; exact (proj1(urank_union oa ux)).
have q2: unionA U inc.
  by move =>x ux; move: (proj1 (p4 _ ux (q1 _ ux))); exists (union x).
have q3: (forall x : Set, U x -> U (\Po x)).
  move => x xa.
  move: (urank_pr1 oa xa) => [sa [sb /setP_P sc sd]].
  move: sc; rewrite - (universe_succ sb) => aa.
  have: (osucc (osucc (urank a x))) <=o a by apply /oleSltP; apply:la.
  move /universe_inc2; apply.
  by move: (urank_powerset  (OS_succ sb) aa) => [se _].
have q8b: forall x y, U x -> U y -> U (doubleton x y).
  move => x y xa ya.
  suff: exists b, [/\ b <o a, inc x (universe b) & inc y (universe b)].
    move => [b [b1 b2 b3]].
    by apply:(universe_inc1 b1); apply /setP_P => t;case /set2_P => ->.
  move: (urank_alt2 oa xa) (urank_alt2 oa ya) => sx sy.
  move: (urank_pr1 oa xa) => [/la sa _].
  move: (urank_pr1 oa ya) => [/la sb _].
  move: (OS_succ (OS_urank oa (x:=x))) => o1.
  move: (OS_succ (OS_urank oa (x:=y))) => o2.
  case: (oleT_ee o1 o2) => H.
     by exists (osucc (urank a y)); split => //; apply:(universe_inc2 H).
     by exists (osucc (urank a x)); split => //; apply:(universe_inc2 H).
have q8: forall x, U x -> U (singleton x) by move => x ux; apply: q8b.
have q4: powersetA U inc.
  by move =>x ux; move: (p5 _ ux (q3 _ ux)) => [h _]; exists (\Po x).
have q6: U emptyset.
  move: (ord_ne0_pos oa (nesym (proj2 anz))) => /universe_inc1. 
  by rewrite universe_0 setP_0; apply; apply /set1_P.
have q7: exists x, U x by exists emptyset.
have q9: foundationA U inc.
  apply p11 => x xa.
  have xu: universe_i x by exists a.
  case:(universe_AF xu);[ by left| move => [y yx dx]; right].
  exists y => //; apply (pa _ _ xa yx).
have q10: choiceA U inc.
  move => x xu; rewrite (p9 q7); move => xx1 xx2.
  set y := fun_image x rep.
  have pc:  forall t, inc t x -> inc (rep t) t.
     move => t tx; apply: rep_i; apply /nonemptyP; apply: xx1 => //.
     apply: (pa _ _ xu tx).
  have pd: forall t, inc t x -> U (rep t).
    move => t tx; exact: (pa _ _ (pa _ _ xu tx)  (pc _ tx)).
  have yU: U y.
    apply: (pb _ _ (q1 _ xu)) => s /funI_P [z zx ->]; apply /setU_P; ex_tac.
  exists y => // z _ zx; exists (rep z); first by apply: pd.
  rewrite (p7 _ _ yU).
  have ->: doubletonU U inc (rep z) (rep z) = (singleton (rep z)).
     rewrite /doubletonU.
     set p := [eta pairA_pr U inc (rep z) (rep z)].
     move: (pd _ zx) => urz; move: (q8 _ urz) => sa.
     have aux: p (singleton (rep z)). 
       split => // t _; split; first by move /set1_P => h; left.
       by case => ->; apply /set1_P.
     have: exists y, p y by exists (singleton (rep z)).
     move /choose_pr; set w := choose p; move => [sb h]; set_extens t => tz.
        move /(h _ (pa _ _ sb tz)): tz; case => ->; fprops.
     by move /set1_P: tz ->; apply /(h _ urz); left.
  apply: set1_pr.
    apply /setI2_P; split; [apply /funI_P; ex_tac | by apply: pc].
  move => t /setI2_P [/funI_P [u ux -> t2]].
  case: (xx2 _ _ (pa _ _ xu zx) (pa _ _  xu ux) zx ux); first by move ->.
  rewrite (p7 _ _ (pa _ _ xu zx)) => di; empty_tac1 (rep u).
have q11 : omega0 <o a <-> infiniteA U inc.
  move: (urank_ordinal OS_omega) => [sa sb sc].
  split.
    move /universe_inc1 => h.
    have ou: U omega0 by apply h; apply /setP_P. 
    apply: p10 => // b bo; first by apply:(q8 _ (pa _ _ ou bo)).
    move: (pa _ _ ou bo) => aa; exact: (q8b _ _ aa  (q8 _ aa)).
  move => ia. 
  case: (oleT_el oa OS_omega) => // /universe_inc2 H.
  have pr1: forall u v, U u -> U v -> U (u \cup v).
    by move => u v uu vv; apply: q1; apply: q8b.
  by move: (H _ (p10b q8b pr1 ia)) => /(universe_P OS_omega)  [b /sc].
split => //.
Qed.


Lemma universe_mo4 (U :=fun z => inc z (universe omega0)) :
  [/\ ZF_axioms1 U inc, ~(infiniteA U inc), choiceA U inc & foundationA U inc].
Proof.
move:(universe_mo3 omega_limit).
move: (universe_mo' OS_omega) => [pr1 pr2].
move => [[pa pb pc pd] pe ap pf pg ph]; split => //;last by move => /pf [].
split => //.
move => x p f ux au; exists (fun_image (Zo x p) f); split.
  move: (universe_omega_props ux) => [ra rb rc].
  apply: universe_omega_hi.  
     apply: finite_fun_image;apply: (sub_finite_set _ ra); apply: Zo_S.
  move => t /funI_P [z /Zo_P [sa sb] ->]; apply: au => //.
  apply: (pr1 _ _ ux sa).
move => z uz; split.
move /funI_P => [a /Zo_P [bb cc] ->]; exists a => //; apply: (pr1 _ _ ux bb).  
by move => [t tu [sa sb ->]]; apply /funI_P;exists t => //; apply /Zo_P.
Qed.


Definition subU U x y:= forall t, U t -> inc t x -> inc t y.
Definition transitive_setU U X := forall x, U x -> inc x X -> subU U x X.
Definition ordinalU U X:= forall Y, U Y -> subU U Y X -> transitive_setU U Y -> 
   Y <> X -> inc Y X.
Definition equipotentU U X Y := exists2 Z, U Z & [/\ subU U Z (X \times Y),
   (forall x, inc x X -> exists2 y, U y & inc (J x y) Z),
   (forall y, inc y Y -> exists2 x, U x & inc (J x y) Z),
   (forall x x' y, U x -> U x' -> U y -> inc (J x y) Z -> inc (J x' y) Z ->
       x = x') &
   (forall x y y', U x -> U y -> U y' -> inc (J x y) Z -> inc (J x y') Z ->
       y = y')].
Definition cardinalU U x :=
    [/\ U x, ordinalU U x & forall z, U z -> ordinalU U z ->
      equipotentU U x z -> subU U x z].
Definition funsetU U X Y Z :=
  U Z /\  (forall f, inc f Z <-> 
      [/\ U f, 
          (forall p, inc p f -> inc p (Y \times X)),
          (forall x, inc x Y -> exists2 y, U y & inc (J x y) f) &
          (forall x y y', inc (J x y) f -> inc (J x y') f -> y = y') ]).
Definition powerU_pr U x y z := 
    cardinalU U z /\ (exists2 Z, funsetU U x y Z & equipotentU U z Z).
Definition powerU U x y := choose (powerU_pr U x y).
Definition inaccessibleU U x :=
  [/\ cardinalU U x, ssub omega0 x, 
    (forall a b, cardinalU U a ->  cardinalU U b -> ssub a x -> ssub b x ->
       ssub (powerU U a b) x) &  
    (forall a, cardinalU U a ->  a <> emptyset -> ssub a x ->
       (powerU U x a) = x) ].


Definition Ufacts U a:=
 [/\
   (forall x, (U x /\ ordinalU U x) <-> (ordinalp x /\ x <o a)),
   (forall x y, U x -> U y -> (x \Eq y <-> equipotentU U x y)),
   (forall x, cardinalU U x <-> (cardinalp x /\ x <c a)),
   (forall x y, cardinalU U x -> cardinalU U y ->
     powerU U x y = (x ^c y)) &
   (forall x, inaccessibleU U x <-> (inaccessible x /\ x <c a)) ].


Section InaccessibleUniverse.
Variable a: Set.
Hypothesis ia: inaccessible a.

Lemma universe_inaccessible_card1 b:
   b <o a -> cardinal(universe b) <c a.
Proof.
pose p b := b<o a -> cardinal (universe b) <c  a.
move: (ia) => [[ [ica _] _] _].
move => ba;ex_middle bad.
apply:(least_ordinal2 (p:=p)) (proj31_1 ba) ba => y oy etc yb.
move /(ocle2P (proj1 ica) oy) : (yb) => cya.
rewrite /p (universe_rec oy).
set yy := unionf _ _.
have ->: yy = unionb (Lg y (fun z => \Po (universe z))).
  set_extens t.
     move /setUf_P => [s sa sb]; apply /setUb_P; aw; ex_tac; rewrite LgV//.
  move => /setUb_P; aw; move => [s sa]; rewrite LgV// => sb; apply /setUf_P; ex_tac.
move: (csum_pr1 (Lg y (fun z => \Po (universe z)))).
set s := csumb _ _; move => h; apply: (cle_ltT h); clear h.
set f := Lg y (fun z => cardinal(\Po (universe z))). 
have pra: csum f = s.
  rewrite /s /f; aw;apply: csumb_exten; move => t ty /=; rewrite LgV//.
have prb: domain f = y by rewrite /f;aw.
have prc: cardinal_fam f by move => t; rewrite prb /f => ys; rewrite LgV//; fprops.
have prd: fgraph f by rewrite /f; fprops.
move /(infinite_regularP ica) : (proj1 (proj1 ia)) => h.
apply: h; last by aw.
split;fprops; hnf; aw => x xy; rewrite !LgV//; rewrite card_setP.
move: (xy) => /(oltP oy) iy';rewrite - cpowcr. 
exact: ((proj2 ia) _ (etc _ iy' (ole_ltT (proj1 iy') yb))).
Qed.

Lemma universe_inaccessible_card2:  cardinal(universe a) = a.
Proof.
move: (ia) => [[ [ica _] _] _].
move:(infinite_card_limit2 ica) => loa.
move:(proj31 loa) => oa.
move: (card_card (proj1 ica)) => caa.
apply cleA; last first.
  by move: (urank_ordinal oa)=> [ _ /sub_smaller]; rewrite caa.
rewrite  (universe_rec oa).
set yy := unionf _ _.
have ->: yy = unionb (Lg a (fun z => \Po (universe z))).
  set_extens t.
     move /setUf_P => [s sa sb]; apply /setUb_P; aw; ex_tac; rewrite LgV//.
  move => /setUb_P; aw; move => [s sa]; rewrite LgV// => sb.  
  by apply /setUf_P; ex_tac.
move: (csum_pr1 (Lg a (fun z => \Po (universe z)))) => h.
apply: (cleT h); set s := csumb _ _; clear h.
set f := Lg a (fun z => cardinal(\Po (universe z))). 
have pra: csum f = s. 
   rewrite /s /f; aw; apply:csumb_exten; move => t ty /=; rewrite LgV//.
have prb: domain f = a by rewrite /f;aw.
have prc: cardinal_fam f by move => t; rewrite prb /f => ys; rewrite LgV; fprops.
have prd: fgraph f by rewrite /f; fprops.
have pre: forall i : Set, inc i (domain f) -> Vg f i <c a.
  move => i; rewrite prb /f => iy; rewrite LgV// card_setP.
  move: (iy) => /(oltP oa) iy'.
  rewrite - cpowcr; exact: (proj2 ia _ (universe_inaccessible_card1 iy')).
move: (csum_of_small_b2 (conj prd pre)). 
by rewrite prb pra (csquare_inf ica).
Qed.

Lemma universe_inaccessible_inc x:
   inc x (universe a) <-> (sub x (universe a) /\ cardinal x <c a). 
Proof.
move: (ia) => [[ [ica _] _] _].
move:(infinite_card_limit2 ica) => loa.
move:(proj31 loa) => oa.
split.
  move => xua; split;first by apply: universe_trans.
  move: xua; rewrite (universe_limit loa) => /setUf_P [y ya yu].
  move: (universe_trans (Os_ordinal oa ya) yu) => /sub_smaller.
  move /(oltP oa) : ya => /universe_inaccessible_card1. 
  move => pa pb; apply: (cle_ltT pb pa).
move => [xu cx].
set f := Lg x (fun z => cardinal (urank a z)).
set s := csum f. 
have pra: csum f = s by [].
have prb: domain f = x by rewrite /f;aw.
have prc: cardinal_fam f by move => t; rewrite prb /f => ys; rewrite LgV; fprops.
have prd: fgraph f by rewrite /f; fprops.
have pre: forall i : Set, inc i (domain f) -> Vg f i <c a.
  move => i; rewrite prb /f => tx; rewrite LgV//.
  move: (xu _ tx); rewrite (universe_limit  loa) => /setUf_P [y ya yb].
  move: (urank_pr1 oa (xu _ tx)) => [pa1 pa2].
  move: (urank_pr1 (Os_ordinal oa ya) yb) => [pb1 pb2].
  apply /(ocle2P (proj1 ica) (proj31_1 pa1)).
  rewrite (urank_uniq pa2 pb2); apply: (ole_ltT (proj1 pb1)).
  by apply /(oltP oa).
move /(infinite_regularP ica) : (proj1 (proj1 ia)) => h.
have ww: cardinal (domain f) <c a by ue.
move: (h _  (conj prd pre) ww) => lsa.
move: (proj2 ia _ lsa); set s1 := \2c ^c s => lsb.
move: (oclt lsb) => /universe_inc1; apply; apply /setP_P.
move => i ix; move: (ix); rewrite  - prb => ix'.
move: (urank_pr1 oa (xu _ ix)) => [_  [hb /setP_P hc _]].
move: (csum_increasing6 (prc _ ix') ix'); rewrite pra /f LgV// => le2.
move: (cle_ltT le2 (cantor (proj31_1 lsa))).
by move /(ocle2P (CS_pow \2c s) hb) => /universe_inc1; apply.
Qed.

Lemma universe_inaccessible_mo1: 
   replacementA (fun z => inc z (universe a)) inc.
Proof.
move => x p f /universe_inaccessible_inc [pa pb] h.
exists (fun_image (Zo x p) f); split; last first.
  move => z za; split. 
    by move /funI_P => [t /Zo_P [ra rb] ->]; exists t => //; apply: pa.
  by move => [t ta [tx pt ->]]; apply /funI_P; exists t => //; apply /Zo_P.
have sc: sub (Zo x p) x by apply: Zo_S.
apply /universe_inaccessible_inc; split.
  by move => t/funI_P [z /Zo_P[ra rb] ->]; apply: h => //; apply: pa.
move: (cleT (fun_image_smaller (Zo x p) f) (sub_smaller sc)) => sa.
exact: (cle_ltT sa pb).
Qed.


Lemma universe_inaccessible_mo2 :
   let U := (fun z => inc z (universe a)) in
   [/\ ZF_axioms1 U inc, comprehensionA U inc,
        infiniteA U inc, choiceA U inc & foundationA U inc]
   /\ Ufacts U a.
Proof.
move: ia => [[[/infinite_card_limit2 la _] _] _]. 
move:(universe_mo3 la) => [ [p1 p2 p3 p4 p5] [ap ap'] p6 p7 p8].
move: universe_inaccessible_mo1 => p9.
have p10: ZF_axioms1 (inc^~ (universe a)) inc by [].
have loa: omega0 <o a.
   rewrite -aleph0E (inaccessible_pr1 (proj1 ia)).
   by apply /aleph_lt_lto; apply: limit_pos.
move /p6: (loa) => p6'.
move:(proj32_1 loa) => oa.
move: (universe_mo' oa) => [pa pb].
move: (universe_mo1 pa pb)
   =>[r1 [r2 [r3 [r4 [r5 [r6 [r7 [r8 [r9 [r10 [r10b r11]]]]]]]]]]].
pose U x := inc x (universe a).
have sa: forall x y, U x -> U y -> (subU U x y <-> sub x y).
  move => x y ux uy; split. 
    move => h t tx; apply:h => //; apply: (pa _ _ ux tx).
  by move => h t ut tx; apply: h.
have sb: forall X, U X ->  (transitive_setU U X <-> transitive_set X).
  move => X UX; split => h.
    move => t tX; move:(pa _ _ UX tX) => ut.
    by apply /(sa _ _ ut UX); apply: h.
  by move => x ux xx; apply /(sa _ _ ux UX); apply: h.
have sc: forall X, U X -> (ordinalU U X <-> ordinalp X).
  move => X UX; split => h.
    move=> t tT tt tnx; move: (pb _ _ UX tT) => tU; apply: h => //;
      [by apply/ (sa _ _ tU UX) | by  apply /(sb _ tU)].
  move => y uy yx ty xy; apply: h => //; first by apply/ (sa _ _ uy UX).
  by apply /(sb _ uy).
have sd: forall x, (U x /\ ordinalU U x) <-> (ordinalp x /\ x <o a).
  move => x; split; move => [xa xb].
    move /(sc _ xa): xb => ox; split => //. 
    move: (urank_pr1  oa xa)(urank_ordinal ox) => [q1 q2] q3.
    by rewrite -{1} (urank_uniq q2 q3).
  have ux: U x. 
    apply:(universe_inc1 xb); apply /setP_P; exact:(proj32 (urank_ordinal xa)). 
  by split => //; apply /(sc _ ux).
have se0: forall x, U x -> U (union x).
   move => x ux; move: (p3 x ux) => [u [ua ub]].
   suff : u = union x by move => <-.   
   set_extens t => tu.
     move /(ub _ (pa _ _ ua tu)): tu => [z [za zx tz]]; union_tac.
   move/setU_P: tu => [z tz zx]; move:(pa _ _ ux zx) => zu.
   by apply /(ub _ (pa _ _ zu tz)); exists z.
have se00: forall r x,  U x -> (forall t, inc t x -> U (r t)) ->
  U (fun_image x r).
  move => r x /universe_inaccessible_inc [pa1 pb1] xru.
  apply /universe_inaccessible_inc; split.
    by move => t/funI_P [z ra ->]; apply: xru => //; apply: pa.
  exact: (cle_ltT (fun_image_smaller x r) pb1).
have se1: forall x y, U x -> U y -> U (J x y).
  by move => x y ux uy; rewrite kpairE; apply: (ap'); apply: ap'.
have se2: forall x y, U x -> U y -> U (x \times y).
  move => x y ux uy; apply: se0; apply: (se00) => //.
  move => t tx; apply: se00 => // s sy; apply: se1. 
      apply: (pa _ _ ux tx).
      apply: (pa _ _ uy sy).
have se3: forall x y, U x -> U y -> (x \Eq y <-> equipotentU U x y).
  move => x y ux uy; split => ha.
    move: ha => [f [[fa fb] sf tf]].
    move: (proj1 fa) => [[qa qa'] qb qc].
    rewrite sf in qa'; rewrite tf in qa'; move: (se2 _ _ ux uy) => xyu.
    move: (pb _ _ xyu qa') => grfu.
    have qd: subU U (graph f) (x \times y) by apply /sa.
    have qe:forall b, inc b x -> exists2 c, U c & inc (J b c) (graph f).
       move => b; rewrite - sf => bsf. 
       move: (Vf_target (proj1 fa) bsf); rewrite tf => h1.
       rewrite qc in bsf; move :(fdomain_pr1 qb bsf) => h.
       exists (Vg (graph f) b) => //; apply (pa _ _ uy h1).
    have qf:forall c, inc c y -> exists2 b, U b & inc (J b c) (graph f).
      rewrite - tf; move => c cy; move: (surjective_pr fb cy); rewrite sf.
      move => [b bx ok]; exists b => //; apply (pa _ _ ux bx).
    have qg:forall b c c', U b -> U c -> U c' -> inc (J b c) (graph f) 
      -> inc (J b c') (graph f) -> c = c'.
       move => b b' c _ _ _ s1 s2; move: (proj2 qb _ _ s1 s2); aw => h.
       by move: (pr2_def (h (erefl b))).
    have qh:forall b b' c, U b -> U b' -> U c -> inc (J b c) (graph f) 
      -> inc (J b' c) (graph f) -> b = b'.
       move => b b' c _ _ _ s1 s2; exact: (injective_pr3 fa s1 s2). 
     exists (graph f) => //; split => //.
  move: ha => [g gu [q1 q2 q3 q4 q5]].
  have q7: sub g (x \times y) by apply/sa => //; apply /se2.
  have q8: forall  b c, inc (J b c) g -> U b /\ U c.
     move => b c /q7 /setXp_P [s1 s2]; split.
       apply: (pa _ _ ux s1).
       apply: (pa _ _ uy s2).
  set f := (triple x y g); exists f; rewrite /f; saw.
  have fgg: fgraph g.
     apply /functionalP; split; first by apply: (sub_setX_graph q7).
   move => b c c' bc1 bc2. 
   exact (q5 _ _ _ (proj1 (q8 _ _ bc1)) (proj2 (q8 _ _ bc1))
       (proj2 (q8 _ _ bc2)) bc1 bc2).
  have ff: function f.
    apply: function_pr => //.
      by move => s /funI_P [z /q7 /setX_P [_ _ h] -> ].
    set_extens s. 
      by  move => /q2 [c _  cu]; apply /funI_P; ex_tac; aw.
    by move =>  /funI_P [z /q7 /setX_P [_ h _] -> ].
  split.
    apply: injective_pr_bis => // c; aw; move =>  b b' /= bu b'u. 
    exact: (q4 _ _ _ (proj1 (q8 _ _ bu)) (proj1 (q8 _ _ b'u))
       (proj2 (q8 _ _ bu)) bu b'u).
  apply: surjective_pr5 => //; aw => b /q3 [c uc pg]; exists c => //.
  by move: (q7 _ pg) =>  /setXp_P [].
have ca: cardinalp a by move: ia => [[[[]]]].
have se6: forall x, cardinalU U x <-> (cardinalp x /\ x <c a).
   move => x; split.
     move => [ux oux etc].
     move /sd: (conj ux oux) => [ox xa]; suff: cardinalp x.
       by split => //; apply:oclt3 => //.
     split => // z oz xeqz.
     case: (oleT_el (proj1 ca) oz) => za.
       move: (ocle1 za); rewrite (card_card ca).
       move /(universe_inaccessible_inc x): ux => [_ ].
       by move /card_eqP: xeqz => -> e1 /(cltNge e1).
     move /sd:(conj oz za) => [uz ouz].
     move /(se3 _ _ ux uz): xeqz => eq1.
     apply /(sa _ _ ux uz); exact (etc _ uz ouz eq1). 
  move => [cx xa]. move: cx => [c1 c2].
  have xa1: x <o a by apply: oclt.
  move /sd:(conj c1 xa1) => [ux oux]; split => // z uz ouz euz.
  move /sd: (conj uz ouz) => [oz za]; move /(se3 _ _ ux uz):euz => euz'.
  by move: (c2 _ oz euz') => /(sa _ _ ux uz).
have se4: forall X Y Z Z', funsetU U X Y Z -> funsetU U X Y Z' -> Z = Z'.
  move => X Y Z  Z' [ra rb] [rc rd].
  set_extens t; [ by move /rb /rd | by move /rd /rb].
have se5: forall X Y, U X -> U Y -> funsetU U X Y (gfunctions Y X).
  move => X Y ux uy.
  have ra: sub (gfunctions Y X) (\Po (Y \times X)) by apply: Zo_S.
  move: (ap _ (se2 _ _  uy ux)) => rb.
  split; first by exact (pb _ _ rb ra).
  split. 
    move => /Zo_P [rc [rd re]];move: (pa _ _ rb rc)=> rf.
    move/setP_P: rc => rc; split => //. 
      rewrite re => x /(fdomain_pr1 rd) => h; exists (Vg f x) => //.
      by move: (rc _ h) => /setXp_P [_] => vx; apply: (pa _ _ ux vx).
   move => x y z rg rh; move: (proj2 rd _ _ rg rh); aw => h.
   exact: (pr2_def(h (erefl x))).
  move => [rc rd re rf]. 
  have sgf: sgraph f by move => t /rd /setX_P [].
  apply: Zo_i; [by  apply /setP_P => p /rd | split ].
     split=> //.
     move => u v rg rh sp; move: (sgf _ rg)(sgf _ rh) => pr1 pr2.
     by move: rg rh; rewrite - pr1 -pr2 sp => rg rh; rewrite (rf _ _ _ rg rh).
  set_extens t; first by move /re => [y uuy yv]; apply /funI_P; ex_tac; aw.
  by move /funI_P => [z /rd /setX_P [_ aa bb] ->].
have se7: forall x y, cardinalU U x -> cardinalU U y -> powerU_pr U x y (x^c y).
  move => x y cux cuy.
  move /se6: (cux) => [cx cxs]; move: (proj31 cux) => ux.
  move /se6: (cuy) => [cy cys]; move: (proj31 cuy) => uy.
  move: (se5 _ _ ux uy) => fsv; move: (fsv) => [fsu _].
  have aux: cardinalU U (x^c y). 
    by apply /se6; split; fprops;apply: (proj2 (inaccessible_dominant ia)).
  split => //;  exists (gfunctions y x) => //. 
  apply/se3 => //; first exact (proj31 aux). 
  by apply/card_eqP; rewrite cpow_pr0 ;aw.
have se8: (forall x y, cardinalU U x -> cardinalU U y ->
     powerU U x y = (x ^c y)).
  move => x y cux cuy; move: (se7 _ _ cux cuy) => h.
  move: (se5 _ _ (proj31 cux) (proj31 cuy)) => ha.
  pose p z := powerU_pr U x y z.
  have: exists z, p z  by exists  (x ^c y).
  move /choose_pr; rewrite -/(powerU _ _ _); set z :=  (powerU U x y).
  rewrite /p; move => [ra [Z za zb]]; move: (se4 _ _ _ _ ha za) => hb.
  move / (se3 _ _ (proj31 ra) (proj1 za)): zb; rewrite - hb.
  move/se6:ra => [cz _].
  move /card_eqP; rewrite (card_card cz) => ->.
  by move:(Eq_fun_set y x) => /card_eqP <-.
have se9: (forall x, inaccessibleU U x <-> (inaccessible x /\ x <c a)).
  have aux: forall a b, (a <c b) <-> [/\ cardinalp a, cardinalp b& ssub a b].
    by move => b c; split; [move => [[s1 s2 s3] s4] | move => [s1 s2 [s3 s4]]].
  move => x;split.
    move=> [ra rb rc rd]; move /se6: (ra) => [re rf]; split => //.
    move /aux: (And3 CS_omega re rb) => ox.
    have a2: forall b, b <c x -> cardinalU U b /\ ssub b x.
     move => b bx. 
        move: (clt_leT bx (proj1 rf)) => ba.
        by move/aux: bx => [cb _ h]; split => //;apply /se6. 
    apply /(inaccessible_dominant3 ox); split.
       move => b c l1 l2; move: (a2 _ l1)(a2 _ l2) => [c1 c2][c3 c4].
       apply/ aux; split; [ by apply: CS_pow | exact | ].
       move: (rc _ _ c1 c3 c2 c4);rewrite se8 //.
     move => z za zb; move: (a2 _ zb) => [c1 c2].
     have ze: z <> emptyset by  move => h; move: (proj2 za); rewrite h.
     by move: (rd _ c1 ze c2); rewrite se8.
  move=> [ra rb].
  have xo: omega0 <c x. 
    move: (ra) => [[[/infinite_card_limit2 la1 _] _] _]. 
    rewrite -aleph0E (inaccessible_pr1 (proj1 ra)).
    by apply /aleph_lt_ltc; apply: limit_pos.
  move /(inaccessible_dominant3 xo): ra=> [rc rd].
  have cux: cardinalU U x by apply /se6; split => //; exact: (proj31_1 rb).
  move/ (aux): xo => [_ cx xo1].
  split => //.
    move => b c qa qb qc qd; move/se6: (qa) => [qe qf].
    move /se6: (qb) => [qg qh].
    move /aux: (And3 qe cx qc) => bx.
    move /aux: (And3 qg cx qd) => lcx.
    move /aux: (rc _ _ bx lcx) => [qi qj qk]; rewrite se8 //.
  move => b qa qb qc;  move/se6: (qa) => [qd qe].
  move /aux: (And3 qd cx qc) => bx.
  have qf: ssub emptyset b by split; fprops.  
  move /aux: (And3 CS0 qd qf) => bx0.
  by move: (rd _  bx0 bx); rewrite se8.
done.
Qed.   

End  InaccessibleUniverse.

Section UniversePermutation.
Variables (f g: fterm).
Hypotheses (fg: forall x, f (g x) = x) (gf: forall x, g (f x) = x).

Let U:= fun x: Set => True.
Let inc':= fun x y => inc x (f y).

Lemma up_fi x y: f x = f y -> x = y.
Proof. by move => h ; rewrite - (gf x) - (gf y) h. Qed.

Lemma up_Ut t: U t.
Proof. by []. Qed.

Lemma up_exten: extensionalityA U inc'. 
Proof.  
by move => a b _ _ /= h; apply:up_fi; set_extens t; move / (h _ (up_Ut t)).
Qed.

Lemma up_ZF1: ZF_axioms1 U inc'.
Proof.
split.
+ by exists emptyset.  
+ apply: up_exten.
+ move => x _;  exists (g (union (fun_image (f x) f))); split => // y _.
  rewrite /inc' fg; split. 
    move /setU_P => [z yz /funI_P [t zx zv]]; exists t; split => //; ue.
  move => [z [_ zfx yfz]]; union_tac; apply /funI_P; ex_tac.
+ move => x _; exists (g (fun_image (\Po (f x)) g)); split => // y _.
  rewrite /inc' fg; split.
    by move/funI_P=> [z /setP_P h1 ->] t _; rewrite fg => /h1.
  move => h; apply/funI_P; exists (f y); rewrite ? gf //.
  by apply/setP_P => t; apply:(h _ (up_Ut t)).
+ move => x p f0 _ _; exists  (g (fun_image (Zo (f x) p) f0));split => // y _.
  rewrite /inc' fg; split.
    move => /funI_P [z /Zo_P [pa pb] pc]; exists z => //.
  by move => [t _ [pa pb pc]]; apply /funI_P; exists t => //; apply/Zo_P.
Qed.

Lemma up_values:
 [/\ emptysetU U inc' = g emptyset,
     forall x, unionU U inc' x = (g (union (fun_image (f x) f))),
     forall x, powersetU U inc' x = (g (fun_image (\Po (f x)) g)),
     forall x p, setofU U inc' x p = (g (Zo (f x) p)) & 
    (forall x p f0, funimageU U inc' x p f0 = (g (fun_image (Zo (f x) p) f0)))
    /\ (forall x y, doubletonU U inc' x y = g (doubleton x y))].
Proof.
move:(model_uniqueness up_exten) => [uU uP uC uR [uE up]].
move:(model_existence  up_ZF1) => [eE eU eP eC eR].
split; last split.
+ by apply: uE => //; split => // t _; rewrite /inc' fg => /in_set0. 
+ move => x; apply:(uU x); first by apply:eU.
  split => // y _; rewrite /inc' fg; split. 
    move /setU_P => [z yz /funI_P [t zx zv]]; exists t; split => //; ue.
  move => [z [_ zfx yfz]]; union_tac; apply /funI_P; ex_tac.
+ move =>x; apply(uP x); first by apply:eP.
  split => // y _ ;rewrite /inc' fg; split.
    by move/funI_P=> [z /setP_P h1 ->] t _; rewrite fg => /h1.
  move => h; apply/funI_P; exists (f y); rewrite ? gf //.
  by apply/setP_P => t; apply:(h _ (up_Ut t)).
+ move => x p; apply:(uC x p); first by apply:eC.
  split => // y _; rewrite /inc' fg; exact:(Zo_P (f x) p y).
+ move => x p f0; apply:(uR x p f0); first by apply:eR.
  split => // y _; rewrite /inc' fg; split.
    move => /funI_P [z /Zo_P [pa pb] pc]; exists z => //.
  by move => [t _ [pa pb pc]]; apply /funI_P; exists t => //; apply/Zo_P.
+ move => x y; apply:(up x y). 
    exact:(model_existence2 up_ZF1 (up_Ut x) (up_Ut y)).
  by split => // t _; rewrite /inc' fg; move:(set2_P t x y).
Qed.

Lemma up_union2 x y:  unionU2 U inc' x y = g (f x \cup f y).
Proof.
move:up_values => [_ pb _ _ [_ pf]].
by rewrite /unionU2 pf pb fg funI_set2.
Qed.

Lemma up_succ x: (unionU2 U inc' x (doubletonU U inc' x x)) = g (f x +s1 x).
Proof.
by move:up_values => [_ pb _ _ [_ ->]]; rewrite up_union2 fg.
Qed.

Lemma up_infinite: infiniteA U inc'.
Proof.
move:up_values => [pa pb pc pd [pe pf]].
move:(induction_defined_pr (fun x => g (f x +s1 x)) (g emptyset)).
set h:= induction_defined _ _; move => [sh [fh sjh] h0 hr].
exists (g (target h)) => //; split.
  rewrite pa - h0 /inc' fg; Wtac; rewrite sh; apply:NS0.
move => t _; rewrite up_succ  /inc' fg; move /sjh => [x xh ->].
by rewrite  sh in xh; rewrite - hr //; Wtac; rewrite sh; apply: NS_succ.
Qed.

Lemma up_inter2 x y: intersectionU2 U inc' x y = g (f x \cap f y).
Proof.
move:up_values => [pa pb pc pd [pe pf]].
rewrite /intersectionU2 pd. apply: f_equal.
set_extens t; first by move /Zo_P => /setI2_P.
by move /setI2_P => h; apply/Zo_P.
Qed.

Lemma up_disjoint x y: 
  (intersectionU2 U inc' x y = emptysetU U inc') <-> disjoint (f x) (f y).
Proof.
rewrite up_inter2; move:up_values => [-> _ _ _ _]. 
rewrite /disjoint; split => // h; first by move: (f_equal f h); rewrite fg fg.
by rewrite h.
Qed.

Lemma up_choice: choiceA U inc'.
Proof.
move:up_values => [Ev _ _ _ [_ dv]]. 
rewrite /choiceA => x _ pa pb.
set E := fun_image (f x) f.
have p1: (forall z, inc z E -> nonempty z).
  move => z /funI_P [y /(pa _ (up_Ut y)) h ->]. 
  by case: (emptyset_dichot (f y)) => // fe; case h;rewrite Ev - (gf y) fe.
have p2:(forall z z', inc z E -> inc z' E -> z = z' \/ disjoint z z'). 
  move => z z' /funI_P [y fyx ->] /funI_P [y' fyx' ->].
  move:(pb _ _  (up_Ut y)  (up_Ut y') fyx fyx').
  rewrite up_disjoint;case; [ by move => ->; left | by  right].
move: AC_variants =>  [_ [_ ac3]].
have: (forall x, exists r,  forall z, inc z x -> nonempty z -> inc (r z) z). 
  by move => X; exists rep => y _ ney; apply:rep_i.
move /ac3 => AC; move: (AC E p1 p2) => [y yp]; clear AC ac3.
exists (g y) => //.
move => z _ zx.
have fze: inc (f z) E by apply /funI_P; exists z.
by move: (yp _ fze) => [t]; move => h; exists t => //;rewrite up_inter2 fg dv h.
Qed.

End UniversePermutation.

Lemma Universe_permutation1
  (f:= fun x => Yo (x = \0c) \1c (Yo (x = \1c) \0c x))
  (U := fun z: Set => True)
  (R := fun x y => inc x (f y))
  (x0 := \1c) (x1:= \0c):
  [/\ ZF_axioms1 U R, infiniteA U R, choiceA U R, emptysetU U R = x0 &
   ( doubletonU U R x1 x1 = x1 /\
    forall t, doubletonU U R t t = t -> t = x1 \/ (t = singleton t))].
Proof.
have h0:= card1_nz.
have ff: forall x, f (f x) = x. 
  rewrite /f => x; case: (equal_or_not x \0c) => xz; first by repeat Ytac0.
  case: (equal_or_not x \1c) => xo; first by repeat Ytac0.
  by repeat Ytac0.
move: (up_values ff ff) => [us _ _ _ [_ db]].
split; last split.
+ exact: (up_ZF1 ff ff). 
+ exact: (up_infinite ff ff).
+ exact: (up_choice ff ff).
+ by rewrite us /f -/card_zero; Ytac0; Ytac0.
+ by rewrite db /x1 -/(singleton _) -/card_one /f; Ytac0; Ytac0.
+ move => t; rewrite db -/(singleton _) /f.
  case: (equal_or_not t \0c) => tz //; first by rewrite tz; left.
  have hb: (singleton t <> \0c). 
    by move => h; move: (set1_1 t); rewrite h => /in_set0.
  have hc: (singleton t <> \1c) by move => h; move:(set1_inj h).
  by Ytac0; Ytac0; right.
Qed.

Section UniversePermutation2.

Definition universe_permutation_fun x :=
  Yo (inc x Nat /\ x <> \0c) (singleton x)
  (Yo (exists y, [/\ inc y Nat, y <> \0c & x = singleton y]) (union x) x).

Let f :=  universe_permutation_fun.

Lemma up2_f0: f \0c = \0c. 
Proof.
have pa: ~ (inc \0c Nat /\ \0c <> \0c) by move => [].
have pb: ~ (exists y, [/\ inc y Nat, y <> \0c & \0c = singleton y]).
  by move => [y [yb ynz yv]]; move:(set1_1 y); rewrite - yv; case; case.
by rewrite /f /universe_permutation_fun; Ytac0; Ytac0. 
Qed.

Lemma up2_fnat x : natp x -> x <> \0c -> f x = singleton x. 
Proof.  
move => pa pb; move: (conj pa pb) => pc.
by rewrite /f /universe_permutation_fun; Ytac0.
Qed.


Lemma up2_fnats x : natp x  -> x <> \0c -> f (singleton x) = x.
Proof.  
move => pa pb; 
have pc: ~(inc (singleton x) Nat /\ singleton x <> \0c).
  move => [ sa _].
  move: (card_nat sa); rewrite cardinal_set1 => /set1_inj ex.
  by case: pb.
have pd:(exists y, [/\ inc y Nat, y <> \0c & singleton x = singleton y]).
  exists x; split => //.
by rewrite /f /universe_permutation_fun; Ytac0; Ytac0; rewrite setU_1.
Qed.

Lemma up2_fperm x :  f (f x) = x.
Proof.
case: (equal_or_not x \0c) => xz; first by rewrite xz up2_f0 up2_f0.
case: (inc_or_not x Nat) => xN. 
  by rewrite (up2_fnat xN xz); apply: up2_fnats. 
have pa: ~ (inc x Nat /\ x <> \0c) by move => [].
case: (p_or_not_p (exists y, [/\ inc y Nat, y <> \0c & x = singleton y]))=> h.
  move:h => [y [yn tnz yv]]; rewrite yv up2_fnats // up2_fnat  //.
suff fx: f x = x by rewrite fx.
by rewrite /f /universe_permutation_fun; Ytac0; Ytac0.
Qed.


Lemma Universe_permutation2
  (U := fun z: Set => True)
  (R := fun x y => inc x (f y))
  (x1 := \1c) (x0:= \0c):
  [/\ ZF_axioms1 U R, infiniteA U R, choiceA U R, emptysetU U R = x0 &
   ((forall x, inc x Nat -> x <> \0c -> doubletonU U R x x = x) /\
    forall t, doubletonU U R t t = t ->
        (inc t Nat /\ t <> \0c) \/  singleton t = t)].
Proof.
have h0:= card1_nz.
have ff:= up2_fperm.
move: (up_values ff ff) => [us _ _ _ [_ db]].
split; last split.
+ exact: (up_ZF1 ff ff). 
+ exact: (up_infinite ff ff).
+ exact: (up_choice ff ff).
+ by rewrite us up2_f0.
+ by move => x xb xnz; rewrite  db  up2_fnats.
+ move => t; rewrite db -/(singleton _) => sft.
  move:(f_equal f sft); rewrite up2_fperm => sft1.
  case: (equal_or_not t \0c) => tb.
    by move: sft1; rewrite tb up2_f0=> h; case: C1_ne_C0.
  case: (inc_or_not t Nat) => itb; first by left.
  have hb: ~ (inc t Nat /\ t <> \0c) by move => [].
  move:sft1; rewrite /f /universe_permutation_fun; Ytac0.
  Ytac hh; last by right.
  move: hh => [y [yb ynz tv]]; rewrite {2} tv setU_1 => hha.
  have ha: inc t y by rewrite - hha; fprops.
  have hc: inc y t by rewrite  tv; fprops.
  case: (ordinal_irreflexive (OS_nat yb)).  
  exact: (ordinal_transitive (OS_nat yb) ha hc).
Qed.

End UniversePermutation2.


Lemma int_not_pair x: inc x Nat -> pairp x -> False.
Proof.
move => xN; rewrite /pairp kpairE /kpair_def => h.
have ox :=(OS_nat xN).
case: (equal_or_not emptyset x) => xne.
  rewrite - h in xne; empty_tac1 ((singleton (P x))).
move /(oltP ox): (conj (ole0x ox) xne); rewrite - h /ord_zero.
move => /set2_P; case => h3; empty_tac1 (P x).
Qed.

Section Formulae.

Let val_eq := \0c.
Let val_in := \1c.
Let val_or := \2c.
Let val_not := \3c.
Let val_ex := \4c.

Definition variables := Nat.
Definition variablep x := inc x variables. 

Lemma val_compare:
  [/\ val_eq <> val_in, val_eq <> val_or, val_eq <> val_not, val_eq <> val_ex
  & [/\ val_in <> val_or, val_in <>  val_not, val_in <> val_ex &
    [/\ val_or <> val_not, val_or <> val_ex & val_not <> val_ex]]].
Proof.
have ha:= clt_01.
have hb:= clt_12.
move: (cltS NS2); rewrite -/card_three => hc.
move: (cltS NS3); rewrite -/card_four => hd.
move:(clt_ltT ha hb)(clt_ltT hb hc)(clt_ltT hc hd) => he hf hg.
move:(clt_ltT he hc)(clt_ltT hf hd)(clt_ltT he hg).
move: ha hb hc hd he hf hg  => [_ ha] [_ hb] [_ hc] [_ hd] [_ he] [_ hf]
   [_ hg] [_ hi] [_ hj] [_ hk].
split => //; split => //.
Qed.

Definition atomic_formulas := 
   ((doubleton val_in val_eq) \times (variables \times variables)).


Definition next_formulas F :=
   F \cup (singleton val_not \times F) \cup 
   ((singleton val_or) \times (F \times F)) \cup
   ((singleton val_ex) \times (variables \times F)).

Definition formulas_rec := 
   induction_defined next_formulas atomic_formulas. 
Definition all_formulas := union (target formulas_rec).

Definition formulap x := inc x all_formulas. 
Definition atomic_formulap x := inc x atomic_formulas. 

Lemma atomic_formulaP x:
   atomic_formulap x <->
   [/\ pairp x, pairp (Q x), variablep (P (Q x)), variablep (Q (Q x)) &
         (P x = val_in \/ P x = val_eq)].
Proof.
split. 
  move => /setX_P [px /set2_P pa /setX_P[pc pd pe] ]; split => //.
by move => [pa pb pc pd /set2_P pe]; apply/setX_P; split => //; apply/setX_P.
Qed.

Lemma next_formulasP F x :
  inc x (next_formulas F) <->
  [\/ (inc x F), 
      [/\ pairp x, P x = val_not & inc (Q x) F ],
      [/\ pairp x, P x = val_or, pairp (Q x), inc (P (Q x)) F &
       inc  (Q (Q x))  F] |
      [/\ pairp x, P x = val_ex, pairp (Q x), variablep (P (Q x)) &
       inc  (Q (Q x))  F] ].
Proof.
split.
  case/setU2_P; last first.
    by move/setX_P => [px /set1_P pa /setX_P[pb pc pd]]; constructor 4.
  case/setU2_P; last first.
    by move/setX_P => [pa /set1_P pb /setX_P[pc pd pe]]; constructor 3. 
  case/setU2_P; first by constructor 1.
  by move/setX_P => [pa /set1_P pb pc]; constructor 2. 
case.
+ move => h; apply /setU2_P; left;  apply /setU2_P; left; fprops.
+ move => [pa pb pc]; apply /setU2_P; left;  apply /setU2_P; left.
  apply/setU2_P; right; apply /setX_P; split => //; rewrite pb; fprops.
+ move => [pa pb pc pd pe]; apply /setU2_P; left; apply/setU2_P; right. 
  apply /setX_P; split => //; [rewrite pb; fprops |  by apply /setX_P].
+ move => [pa pb pc pd pe]; apply /setU2_P; right; apply /setX_P; split => //. 
    rewrite pb; fprops.
  by apply /setX_P.
Qed.

Lemma formulas_rec0: Vf formulas_rec \0c = atomic_formulas.
Proof.
by move:(induction_defined_pr next_formulas atomic_formulas) => [].
Qed.

Lemma formulas_rec_succ n: inc n Nat ->
   Vf formulas_rec (csucc n) = next_formulas (Vf formulas_rec n).
Proof.
move:(induction_defined_pr next_formulas atomic_formulas) => [_ _ _ h].
apply: h.
Qed.

Lemma formula_hi x n: natp n -> inc x (Vf formulas_rec n) -> formulap x.
Proof.  
move:(induction_defined_pr next_formulas atomic_formulas) => [h1 [h2 _] _ _].
move => nV xf; apply/ setU_P; exists(Vf formulas_rec n) => //; Wtac; ue.
Qed.

Lemma formula_i1 x : formulap x ->
  exists2 n, natp n & inc x (Vf formulas_rec n).
Proof.
move:(induction_defined_pr next_formulas atomic_formulas).
  rewrite -/formulas_rec; move => [pa [pb1 pb2] pc pd].
move /setU_P => [z za /pb2  [n na nb]]; rewrite /natp - pa; exists n => //; ue.
Qed.

Lemma formula_sub_rec n m: n <=c m -> natp m ->
  sub (Vf formulas_rec n) (Vf formulas_rec m).
Proof.
move => nm mN.
move:(NS_le_nat nm mN) => nN.
move:(NS_diff n mN);rewrite -{2} (cdiff_pr nm); move:(m -c n).
apply: Nat_induction; first by rewrite (csum0r (proj31 nm)). 
move => p pN hrec; rewrite (csum_nS _ pN) formulas_rec_succ; fprops.
move => t ta; apply/next_formulasP; constructor 1; apply: hrec => //. 
by apply:NS_sum.
Qed.


Lemma formula_Vomega n: natp n ->  
  sub (Vf formulas_rec n) (universe omega0).
Proof.
have H: sub variables (universe omega0) by exact:sub_Nat_Vomega.
move:n;apply: Nat_induction.
   rewrite formulas_rec0 => t /atomic_formulaP [qa qb qc qd qe].
   have qf: inc (Q t) (universe omega0).
     rewrite - qb;  apply:pair_in_Vomega; fprops.
   rewrite - qa;apply:pair_in_Vomega => //;case: qe => ->.
     apply:sub_Nat_Vomega; apply: NS1.
     apply:sub_Nat_Vomega; apply: NS0.
move => n nN Hr; rewrite (formulas_rec_succ nN) => t /next_formulasP; case.
+ apply: Hr.
+ move => [pt Pt Qt]; rewrite - pt; apply: pair_in_Vomega; last by apply: Hr.
  rewrite Pt; apply:sub_Nat_Vomega; apply: NS3.
+ move => [qa qb qc qd qe]; rewrite - qa - qc; apply: pair_in_Vomega. 
   rewrite qb; apply:sub_Nat_Vomega; apply: NS2.
   apply:pair_in_Vomega; fprops.
+ move => [qa qb qc qd qe]; rewrite - qa - qc; apply: pair_in_Vomega. 
   rewrite qb; apply:sub_Nat_Vomega; apply: NS4. 
   apply: pair_in_Vomega; fprops.
Qed.

Lemma formulas_Vomega: sub all_formulas (universe omega0).
Proof. by move => t /formula_i1 [n na nb]; apply:(formula_Vomega na). Qed.

Lemma formula_HF x: formulap x -> hereditarily_finite x.
Proof. by move/formulas_Vomega /universe_omega_HF. Qed.


Lemma countable_formulas: countable_set all_formulas.
Proof.
rewrite /all_formulas.
move:(induction_defined_pr next_formulas atomic_formulas).
rewrite -/formulas_rec; move => [h1 h2 h3 h4].
have ff:= proj1 h2.
rewrite - (surjective_pr0 h2) (ImfE ff)  -(setUb_alt(function_fgraph ff)).
apply: countable_union. 
   rewrite (domain_fg ff) h1; apply/countableP.
   rewrite - aleph0_pr1; exact: (cleR (CS_aleph0)).
have ha: forall x y, countable_set (doubleton x y).
   move / (oclt3 CS1 CS_aleph0): olt_1omega => [H1 _].   
   move / (oclt3 CS2 CS_aleph0): olt_2omega => [H2 _].   
   move => x y; apply /countableP; case: (equal_or_not x y) => exy.
     by rewrite exy cardinal_set1.
   by rewrite (cardinal_set2 exy).
have hb: countable_set variables by apply:countable_Nat.
move => x; rewrite (domain_fg ff) h1 -/(Vf _ _).
move:x; apply: Nat_induction.
   rewrite h3 /atomic_formulas; apply: countable_setX2; first by apply: ha.
   by apply: countable_setX2.
move => n nN Hrec; rewrite (h4 _ nN);apply:countable_setU2.
  apply:countable_setU2.
    apply:countable_setU2 => //; apply:countable_setX2 => //; apply: ha.
  by apply:countable_setX2 => //; [apply: ha | apply:countable_setX2].
by apply:countable_setX2; [ apply: ha | apply:countable_setX2].
Qed.


Definition formula_len x := 
  intersection (Zo Nat (fun n => inc x (Vf formulas_rec n))).


Lemma formula_len_pr x (n := formula_len x): formulap x ->
  [/\ natp n, inc x (Vf formulas_rec n) &
   forall m, natp m -> inc x (Vf formulas_rec m) -> n <=c m].
Proof.
move => xi;rewrite /n /formula_len; set E := Zo _ _.
move:(induction_defined_pr next_formulas atomic_formulas).
  rewrite -/formulas_rec; move => [pa pb pc pd].
have ne: nonempty E by  move:(formula_i1 xi) => [m ma mb]; exists m; apply:Zo_i.
have oe: ordinal_set E by move => t /Zo_S /OS_nat.
move: (ordinal_setI ne oe) => /Zo_P [ha hb]; split => //.
move => m mN xf; split => //; fprops.
by move => t ti; apply: (setI_hi ti); apply /Zo_P. 
Qed.

Lemma NS_formula_len x: formulap x -> natp (formula_len x).
Proof. by move / formula_len_pr => []. Qed.

Lemma flength_rec x m (n := formula_len x):
   formulap x -> n <=c m -> natp m -> inc x (Vf formulas_rec m).
Proof.
move => fp; move:(formula_len_pr fp) => []; rewrite -/n => nN xv _ nm mN.
apply:(formula_sub_rec  nm mN xv).
Qed.

Lemma flength0P x: formulap x ->
   (formula_len x = \0c <-> atomic_formulap x).
Proof.
have qc:= formulas_rec0.
move => /formula_len_pr [pa pb pc]; rewrite /atomic_formulap - qc.
split => h; [ue | exact(cle0 (pc _ NS0 h)) ]. 
Qed.

Lemma formula_i x: formulap x ->  inc x (Vf formulas_rec (formula_len x)).
Proof. by move / formula_len_pr => []. Qed.

Lemma flength_nz x (n := formula_len x) (F := (Vf formulas_rec (cpred n))): 
  formulap x -> n <> \0c -> 
  [/\ natp (cpred n), inc x (next_formulas F) & ~ inc x F].
Proof.
move => fp nz. 
move:(formula_len_pr fp) => []; rewrite -/n => nN qa qb.
move:(cpred_pr nN nz) => [mN mv].
move: qa; rewrite {1} mv (formulas_rec_succ  mN) -/F => qc; split => // xF.
by move:(qb _ mN xF)(cltS mN); rewrite - mv => l1 /(cleNgt l1).
Qed.

Lemma fkind_pa x: formulap x ->
  ((P x = val_in \/ P x = val_eq ) <-> atomic_formulap x).
Proof.
move => fx.
have Ha: atomic_formulap x -> P x = val_in \/ P x = val_eq.
  by move /atomic_formulaP => [_ _ _ _]. 
split => // hb; case: (equal_or_not (formula_len x) \0c) => lex0.
  by move/(flength0P fx): lex0.
move: val_compare => [q0 q1 q2 q3 [q4 q5 q6 [q7 q8 q9]]].
move:(flength_nz fx lex0) => [hu hv hw].
move: hv => /next_formulasP; case.
+ done.
+ move => [_ h _]; case hb; rewrite h => h1; [ by case q5 | by case q2].
+ move => [_ h _ _ _]; case hb; rewrite h => h1; [ by case q4 | by case q1].
+ move => [_ h _ _ _]; case hb; rewrite h => h1; [ by case q6 | by case q3].
Qed.


Lemma fkind_eq_p1 x (b:= (P (Q x))) (c := Q (Q x)):
 formulap x -> P x = val_eq ->
 [/\  x = J val_eq (J b c), variablep b & variablep c].
Proof.
move => pa pb.
have pc: (P x = val_in \/ P x = val_eq) by right.
move/(fkind_pa pa): pc => /atomic_formulaP [qa qb qc qd qe]; split => //.
by rewrite - pb qb qa. 
Qed.

Lemma fkind_eq_p2 a b (x := J val_eq (J a b)): 
  variablep a -> variablep b -> (formulap x /\ formula_len x = \0c).
Proof.
move => pb pc.
have pd: atomic_formulap x. 
   rewrite /x;apply/atomic_formulaP; aw;split => //; fprops.
have fp: formulap x by apply:(formula_hi NS0); rewrite formulas_rec0.
by split => //; apply/flength0P.
Qed.

Lemma fkind_in_p1 x (b:= (P (Q x))) (c := Q (Q x)):
  formulap x -> P x = val_in ->
  [/\  x = J val_in (J b c), variablep b & variablep c].
Proof.
move => pa pb.
have pc: (P x = val_in \/ P x = val_eq) by left.
move/(fkind_pa pa): pc => /atomic_formulaP [qa qb qc qd qe]; split => //.
by rewrite - pb qb qa. 
Qed.

Lemma fkind_in_p2 a b (x := J val_in (J a b)): 
  variablep a -> variablep b -> (formulap x /\ formula_len x = \0c).
Proof.
move => pb pc.
have pd: atomic_formulap x. 
   rewrite /x;apply/atomic_formulaP; aw;split => //; fprops.
have fp: formulap x by apply:(formula_hi NS0); rewrite formulas_rec0.
by split => //; apply/flength0P.
Qed.

Lemma fkind_or_p1 x (a := P (Q x)) (b := Q (Q x)):
  formulap x ->  P x = val_or ->
  [/\ x = J val_or (J a b), formulap a, formulap b, 
    formula_len a <c formula_len x & formula_len b <c formula_len x].
Proof.
move: val_compare => [q0 q1 q2 q3 [q4 q5 q6 [q7 q8 q9]]].
move => fp kx1. 
case (equal_or_not (formula_len x) \0c) => ha.
  move /(flength0P fp): ha => /atomic_formulaP [_ _ _ _].
  rewrite kx1; case => h; [ by case:  q4 |  by case: q1 ].
case:(flength_nz fp ha); set F:= Vf _ _ => pa pb pc.
case/next_formulasP: pb.
+ done.
+ by move => [_ qb _ ]; case: q7; rewrite  - kx1.
+ move => [prx _ ppx aF bF].
  rewrite {1} /a {1} /b ppx  - kx1 prx.
  move:(NS_formula_len fp) => nN.
  move: (cpred_pr nN ha) => [sa ->].
  have fa:= (formula_hi sa aF).
  have fb:= (formula_hi sa bF).
  split => //; apply/(cltSleP sa).
    exact:(proj33 (formula_len_pr fa) _ sa  aF).
  exact (proj33 (formula_len_pr fb) _ sa  bF).
+ by move => [_ h _ _ _]; case: q8; rewrite - kx1.
Qed.

Lemma fkind_or_p2 a b (x := J val_or (J a b)): 
  formulap a -> formulap b ->
  (formulap x /\ formula_len x = csucc (cmax (formula_len a) (formula_len b))).
Proof.
move => fa fb.
move:(formula_len_pr fa); set n := formula_len a;move => [nN pa pb].
move:(formula_len_pr fb); set m := formula_len b;move => [mN pc pd].
move: (cmax_p1 (CS_nat nN) (CS_nat mN)).
set p := cmax n m; move => [max1 max2].
have pN: natp p by apply: Gmax_E.
have pe: inc x (Vf formulas_rec (csucc p)).
  rewrite (formulas_rec_succ pN).
  apply/next_formulasP; constructor 3; rewrite /x; aw; split; fprops.
     exact:(flength_rec fa max1 pN).
   exact:(flength_rec fb max2 pN).
have fx:=(formula_hi (NS_succ pN) pe).
split => //.
move: val_compare => [q0 q1 q2 q3 [q4 q5 q6 [q7 q8 q9]]].
move:(formula_len_pr fx); set q := formula_len x;move => [qN pa' pb'].
case: (equal_or_not q \0c) => qnz.
  move: pa'; rewrite qnz formulas_rec0 => /(fkind_pa fx).
  rewrite /x; aw; case => h; [by case:q4 |  by case: q1].
move:(cpred_pr qN qnz) => [sa sb].
move: pa'; rewrite sb (formulas_rec_succ sa) => /next_formulasP; case.
+ by move/(pb' _ sa); move: (cltS sa); rewrite - sb => su /(cltNge su).
+ by rewrite /x; aw;move => [_ ha _]; case:C0_ne_C1.
+ move => [px Px qa qb qc].
  move: qb; rewrite /x; aw; move/(pb _ sa) => ha.
  move: qc; rewrite /x; aw; move/(pd _ sa) => hb.
  move: (cmax_p0 ha hb); rewrite -/p => hc.
  move /(cleSSP (CS_nat pN) (CS_nat sa)): hc; rewrite - sb.
  move: (pb' _ (NS_succ pN) pe); apply: cleA. 
+ by rewrite /x; aw;move => [_ h _ _ _]; case: q8.
Qed.

Lemma fkind3_p1 x (a := Q x):
  formulap x -> P x = val_not ->
  [/\ x = J val_not a, formulap a & formula_len a <c formula_len x].
Proof.
move => fp kx1. 
move: val_compare => [q0 q1 q2 q3 [q4 q5 q6 [q7 q8 q9]]].
case (equal_or_not (formula_len x) \0c) => ha.
  move /(flength0P fp): ha => /atomic_formulaP [_ _ _ _].
  rewrite kx1; case => h; [by  case: q5 | by case: q2].
case:(flength_nz fp ha); set F:= Vf _ _ => pa pb pc.
case/next_formulasP: pb.
+ done.
+ move => [prx _ aF].
  rewrite {1} /a  - kx1  prx.
  move:(NS_formula_len fp) => nN.
  move: (cpred_pr nN ha) => [sa ->].
  have fa:= (formula_hi sa aF); split => //; apply/(cltSleP sa).
  exact:(proj33 (formula_len_pr fa) _ sa  aF).
+ by move => [_ h _ _ _];case:q7; rewrite - h. 
+ by move => [_ h _ _ _];case:q9; rewrite - h. 
Qed.

Lemma fkind_not_p2 a (x := J val_not a): 
  formulap a ->
  (formulap x /\ formula_len x = csucc (formula_len a)).
Proof.
move: val_compare => [q0 q1 q2 q3 [q4 q5 q6 [q7 q8 q9]]].
move => fa.
move:(formula_len_pr fa); set n := formula_len a;move => [nN pa pb].
have pc: inc x (Vf formulas_rec (csucc n)).
  rewrite (formulas_rec_succ nN).
  apply/next_formulasP; constructor 2;rewrite /x; aw;split; fprops.
have fx:=(formula_hi (NS_succ nN) pc).
split => //.
move:(formula_len_pr fx); set m := formula_len x;move => [mN pa' pb'].
move:(pb' _ (NS_succ nN) pc) => le1.
case: (equal_or_not m \0c) => mnz.
  move: pa'; rewrite mnz formulas_rec0 => /(fkind_pa fx).
  rewrite /x; aw; case => h; [by case:q5 |  by case: q2].
move:(cpred_pr mN mnz) => [vc vb].
move: pa'; rewrite vb (formulas_rec_succ vc) => /next_formulasP; case.
+ by move/(pb' _ vc); move: (cltS vc); rewrite - vb=> su /(cltNge su).
+ move => [_ _]; rewrite /x; aw; move/(pb _ vc) => he.
  move /(cleSSP (CS_nat nN) (CS_nat vc)): he; rewrite - vb => le.
  by apply: cleA.
+ by move => [_ hh _ _ _]; case: q7; rewrite - hh; rewrite /x; aw.
+ by  move => [_ hh _ _ _]; case: q9; rewrite - hh; rewrite /x; aw.
Qed.

Lemma fkind_ex_p1 x (a := (P (Q x))) (b := Q (Q x)):
  formulap x -> P x = val_ex ->
  [/\ x = J val_ex (J a b), variablep a, formulap b
        & formula_len b <c formula_len x].
Proof.
move => fp kx1.
move: val_compare => [q0 q1 q2 q3 [q4 q5 q6 [q7 q8 q9]]].
case (equal_or_not (formula_len x) \0c) => ha.
  move /(flength0P fp): ha => /atomic_formulaP [_ _ _ _].
  rewrite kx1; case => h; [by  case: q6 | by case: q3].
case:(flength_nz fp ha); set F:= Vf _ _ => pa pb pc.
case/next_formulasP: pb.
+ done.
+ by move => [_ h _ ];case:q9; rewrite - h. 
+ by move => [_ h _ _ _];case:q8; rewrite - h. 
+ move => [prx _ pqx ab bf].
  rewrite - kx1 pqx prx.
  move:(NS_formula_len fp) => nN.
  move: (cpred_pr nN ha) => [sa ->].
  have fa:= (formula_hi sa bf); split => //; apply/(cltSleP sa).
  exact:(proj33 (formula_len_pr fa) _ sa bf).
Qed.

Lemma fkind_ex_p2 a b (x := J val_ex (J a b)): 
  variablep a -> formulap b ->
  (formulap x /\ formula_len x = csucc (formula_len b)).
Proof.
move: val_compare => [q0 q1 q2 q3 [q4 q5 q6 [q7 q8 q9]]].
move => va fb.
move:(formula_len_pr fb); set n := formula_len b;move => [nN pa pb].
have pc: inc x (Vf formulas_rec (csucc n)).
  rewrite (formulas_rec_succ nN).
  apply/next_formulasP; constructor 4;rewrite /x; aw;split; fprops.
have fx:=(formula_hi (NS_succ nN) pc).
split => //.
move:(formula_len_pr fx); set m := formula_len x;move => [mN pa' pb'].
move:(pb' _ (NS_succ nN) pc) => le1.
case: (equal_or_not m \0c) => mnz.
  move: pa'; rewrite mnz formulas_rec0 => /(fkind_pa fx).
  rewrite /x; aw; case => h; [by case:q6 |  by case: q3].
move:(cpred_pr mN mnz) => [vc vb].
move: pa'; rewrite vb (formulas_rec_succ vc) => /next_formulasP; case.
+ by move/(pb' _ vc); move: (cltS vc); rewrite - vb => su /(cltNge su).
+ by move => [_ hh _ ]; case: q9; rewrite - hh; rewrite /x; aw.
+ by move => [_ hh _ _ _]; case: q8; rewrite - hh; rewrite /x; aw.
+ move => [_ _ _ _]; rewrite /x; aw; move/(pb _ vc) => he.
  move /(cleSSP (CS_nat nN) (CS_nat vc)): he; rewrite - vb => le2.
  by apply:cleA.
Qed.


Definition length_smaller_formulas i :=
   Yo (i = \0c) emptyset
   (Yo (natp i) (Vf formulas_rec (cpred i)) all_formulas).
Definition small_formulas n := Zo all_formulas (fun z => formula_len z <c n).


Lemma stratified_formula_ax1: 
  (forall x, formulap x -> ordinalp (formula_len x)). 
Proof. by move => x /NS_formula_len /OS_nat. Qed.


Lemma stratified_formula_ax2' i: ordinalp i ->
  (forall x, inc x (length_smaller_formulas i)  <-> 
    formulap x /\ formula_len x <o i).
Proof.
move => oi; rewrite /length_smaller_formulas.
case: (equal_or_not i \0c) => inz; Ytac0.
  by move => x; split;[ move/in_set0 | rewrite inz; move => [_ /olt0]].
case: (inc_or_not i Nat) => iN; Ytac0;last first.
  move => x; split; last by move => [].
  move => fp; split => //; move:(NS_formula_len fp) => /olt_omegaP h.
  case: (oleT_el OS_omega oi) =>// h'; first by apply: (olt_leT h h').
  by case/olt_omegaP: iN.
case: (cpred_pr iN inz); set n := cpred i => nN nv.
move => x; split => h.
  have fx:= (formula_hi nN h); split => //; apply: oclt.
  move:(formula_len_pr fx) => [pa pb pc]; move:(pc _ nN h); rewrite nv=> h'.
  by apply /(cltSleP nN).
move: h => [h1]; move: (h1) => /formula_len_pr [pa pb pc].
move /(oclt3 (CS_nat pa) (CS_nat iN)); rewrite nv.
move /(cltSleP nN) => le; exact:(flength_rec h1 le nN).
Qed.

Lemma stratified_formula_ax2: 
 (forall i,ordinalp i ->
   exists E, forall x, inc x E <-> formulap x /\ formula_len x <o i).
Proof.
move => i oi;exists (length_smaller_formulas i).
by apply:stratified_formula_ax2'.
Qed.

Lemma stratified_formula_rec  (H : fterm2) 
  (f := stratified_fct formulap H formula_len):
  (forall x, formulap x -> 
     f x = H x (Lg (small_formulas (formula_len x)) f)).
Proof.
move => x fx; rewrite {1} /f. 
rewrite(stratified_fct_pr H stratified_formula_ax1 stratified_formula_ax2 fx).
congr (H x (Lg _ f)). 
have nN:= (NS_formula_len fx).
move: (stratified_setP stratified_formula_ax2 (OS_nat nN)) => h.
set_extens y.
  move /h =>[pa pb]; apply:Zo_i => //.
  have pc := (NS_formula_len pa).
  exact :(oclt3 (CS_nat pc) (CS_nat nN)).
by move => /Zo_P [ffx / oclt lt]; apply/h.
Qed.

Definition free_vars_aux x f := 
  Yo (P x = val_in \/ P x = val_eq)  (doubleton (P (Q x)) (Q (Q x)))
  (Yo (P x = val_not ) (Vg f (Q x))
   (Yo (P x = val_or) (Vg f (P (Q x)) \cup  (Vg f (Q (Q x))))
     ((Vg f (Q (Q x)) -s1 (P (Q x)))))).

Definition free_vars := stratified_fct formulap free_vars_aux formula_len.
Definition closed_formula x := free_vars x = emptyset.

Lemma free_vars_rec x: formulap x ->
  free_vars x = 
  free_vars_aux x (Lg (small_formulas (formula_len x)) free_vars).
Proof. exact:(stratified_formula_rec free_vars_aux). Qed.


Lemma free_vars_eq b c (x := J val_eq (J b c)): 
  variablep b -> variablep c -> free_vars x = doubleton b c.
Proof.
move => pb pc.
have ha: (val_eq = val_in \/ val_eq = val_eq) by right.
have fx: formulap x by exact  (proj1 (fkind_eq_p2 pb pc)).
by rewrite (free_vars_rec fx) /free_vars_aux /x; aw; Ytac0.
Qed.

Lemma free_vars_in b c (x := J val_in (J b c)): 
  variablep b -> variablep c -> free_vars x = doubleton b c.
Proof.
move => pb pc.
have ha: (val_in = val_in \/ val_in = val_eq) by left.
have fx: formulap x by exact  (proj1 (fkind_in_p2 pb pc)).
by rewrite (free_vars_rec fx) /free_vars_aux /x; aw; Ytac0.
Qed.

Lemma free_vars_not a (x := J val_not a): formulap a ->
  free_vars x = free_vars a.
Proof.
move => pa;move: (fkind_not_p2 pa) => [sa sb].
move: val_compare => [q0 q1 q2 q3 [q4 q5 q6 [q7 q8 q9]]].
have ha:~(val_not = val_in \/ val_not = val_eq) by case => h; fprops.
rewrite (free_vars_rec sa) /free_vars_aux; aw; Ytac0; Ytac0; Ytac0.
rewrite LgV//;  apply/Zo_P; split => //; rewrite sb.
apply: (cltS (NS_formula_len pa)).
Qed.

Lemma free_vars_or a b (x := J val_or (J a b)): 
  formulap a -> formulap b ->
  free_vars x = free_vars a \cup free_vars b.
Proof.
move => pa pb;move: (fkind_or_p2 pa pb)=> [sa sb].
move: val_compare => [q0 q1 q2 q3 [q4 q5 q6 [q7 q8 q9]]].
have hc:~(val_or = val_in \/ val_or = val_eq) by case => h; fprops.
rewrite (free_vars_rec sa) /free_vars_aux; aw; Ytac0; Ytac0; Ytac0.
have ha:= (NS_formula_len pa).
have hb:= (NS_formula_len pb).
move: (cmax_p1 (CS_nat ha)(CS_nat hb)) => [sd se].
have mN: natp (cmax (formula_len a)(formula_len b)) by apply:Gmax_E.
by rewrite !LgV//; apply /Zo_P; split => //; rewrite sb; apply/cltSleP.
Qed.

Lemma free_vars_ex  a b (x := J val_ex (J a b)): 
  variablep a -> formulap b ->
  free_vars x = (free_vars b) -s1 a.
Proof.
move => pa pb;move: (fkind_ex_p2 pa pb) => [sa sb].  
move: val_compare => [q0 q1 q2 q3 [q4 q5 q6 [q7 q8 q9]]].
have hc:~(val_ex = val_in \/ val_ex = val_eq) by case => h; fprops.
rewrite (free_vars_rec sa) /free_vars_aux; aw; Ytac0; Ytac0; Ytac0.
have hN := NS_formula_len pb.
rewrite LgV//;apply/Zo_P; split => //; rewrite sb; apply: (cltS hN).
Qed.

Lemma free_vars_variables x: formulap x ->
   sub (free_vars x) variables /\ finite_set (free_vars x).
Proof.
move => fx.
move: (formula_len_pr fx) => []; clear fx.
move: {1 2} (formula_len x) => n na nb _; move:n na x nb . 
apply: Nat_induction.
  rewrite formulas_rec0 => x /atomic_formulaP [sa qa qb qc qd].
  suff: (free_vars x) = doubleton (P (Q x)) (Q (Q x)).
    move => ->; split; first by move =>  t /set2_P; case => ->.
    apply: set2_finite.
  rewrite - {1} sa -{1} qa; case qd => ->.
    by apply:free_vars_in.
  by apply:free_vars_eq.
move => n nN Hrec x;rewrite (formulas_rec_succ nN); case /next_formulasP.
+ apply: Hrec.
+ move => [pa pb pc];move:(formula_hi nN pc) => pd.
  by move:(free_vars_not pd); rewrite - pb pa => ->; apply: Hrec.
+ move => [pa pb pc pd pe].
  move: (free_vars_or (formula_hi nN pd) (formula_hi nN pe)).
  move: (Hrec _ pd) => [ua /card_finite_setP ub].
  move:(Hrec _ pe) =>[uc /card_finite_setP ud].
  rewrite - pb pc pa => ->; split; first ( move  => t /setU2_P; case; fprops).
  move:(NS_sum ub ud) => ue; apply/card_finite_setP.
  by apply: (NS_le_nat _ ue); rewrite csum2cl csum2cr; apply: csum2_pr6.
+  move => [pa pb pd pc pe]; move:(formula_hi nN pe) => pf.
  move:(free_vars_ex pc pf);rewrite pd - pb pa => sa.
  have sb: sub (free_vars x) (free_vars (Q (Q x))).
    by rewrite sa; move => t /setC_P [].
  move:(Hrec _ pe) => [sc sd]; split; first by apply: (sub_trans sb sc).
  apply: (sub_finite_set sb sd).
Qed.


(** Evaluating a formula *)


Definition Val_of_eq X a b := 
  Zo (gfunctions (doubleton a b) X) (fun z => Vg z a = Vg z b).

Definition Val_of_inc X a b := 
  Zo (gfunctions (doubleton a b) X) (fun z => inc (Vg z a) (Vg z b)).

Definition Val_of_not X v V := (gfunctions v X) -s V.

Definition Val_of_or X v1 v2 V1 V2 := 
   Zo (gfunctions (v1 \cup v2) X)
   (fun z => inc (restr z v1) V1 \/inc (restr z v2) V2). 

Definition Val_of_ex X v V :=
  Zo (gfunctions v X) (fun z => exists2 f, inc f V & z = restr f v).

Definition formula_values X x := gfunctions (free_vars x) X.

Definition formula_val_aux X x f (t:= P x) := 
  Yo (P x = val_in) (Val_of_inc X (P (Q x)) (Q (Q x)))
     (Yo (P x = val_eq) (Val_of_eq X  (P (Q x)) (Q (Q x)))
         (Yo (P x = val_not) (Val_of_not X (free_vars x) (Vg f (Q x)))
             (Yo (P x = val_or) (Val_of_or X (free_vars (P (Q x)))
                    (free_vars (Q (Q x))) (Vg f (P (Q x))) (Vg f (Q (Q x))))
                 (Val_of_ex X (free_vars x) (Vg f (Q (Q x))))))).

Definition formula_val X:= stratified_fct formulap
    (formula_val_aux X) formula_len.

Lemma formula_val_rec X x: formulap x ->
  formula_val X x = formula_val_aux X x
      (Lg (small_formulas (formula_len x)) (formula_val X)).
Proof. exact:(stratified_formula_rec (formula_val_aux X)). Qed.


Lemma formula_val_eq X a b (x := J val_eq (J a b)) (V := formula_val X x):
  variablep a -> variablep b ->  
  [/\ V  =  Val_of_eq X a b, sub V (formula_values X x) &
    forall f,  inc f V <-> 
    [/\ fgraph f, domain f = doubleton a b, Vg f a = Vg f b & inc (Vg f a) X]].
Proof.
move => va vb.
move: val_compare => [q0 q1 q2 q3 [q4 q5 q6 [q7 q8 q9]]].
move: (fkind_eq_p2 va vb) => [sa sb].
have vc: val_eq = val_in \/ val_eq = val_eq by right.
have ->:  V = Val_of_eq X a b.
  rewrite /V(formula_val_rec X sa) /formula_val_aux sb. 
  by aw; Ytac0; Ytac0; Ytac0; Ytac0.
rewrite /formula_values (free_vars_eq va vb).  
split; [exact | apply: Zo_S |split ].
  move => /Zo_P [/Zo_P [/setP_P pa [pb pc]] pd]; split => //.
  have adf: inc a (domain f) by rewrite - pc; fprops.
  by move: (pa _ (fdomain_pr1 pb adf)) => /setX_P [_ _]; aw.
move => [fgf df sf fa]; apply/Zo_P; split => //; apply/gfunctions_P2.
split => // t /(range_gP fgf) [z zdf ->].
by move: zdf; rewrite df; case /set2_P => -> //; rewrite - sf.
Qed.


Lemma formula_val_inc X a b (x := J val_in (J a b)) (V := formula_val X x):
  variablep a -> variablep b ->  
  [/\ V  =  Val_of_inc X a b, sub V (formula_values X x) &
   forall f, inc f V <-> 
   [/\ fgraph f, domain f = doubleton a b, inc (Vg f a) X, inc (Vg f b) X &
         inc (Vg f a) (Vg f b)]].
Proof.
move => va vb.
move: val_compare => [q0 q1 q2 q3 [q4 q5 q6 [q7 q8 q9]]].
move: (fkind_in_p2 va vb) => [sa sb].
have vc: val_in = val_in \/ val_in = val_eq by left.
have ->:  V = Val_of_inc X a b.
  rewrite /V(formula_val_rec X sa) /formula_val_aux sb. 
  by aw; Ytac0; Ytac0; Ytac0; Ytac0.
rewrite /formula_values (free_vars_in va vb).  
split; [exact | apply: Zo_S |split ].
  move => /Zo_P [/Zo_P [/setP_P pa [pb pc]] pd]; split => //.
    have adf: inc a (domain f) by rewrite - pc; fprops.
    move: (pa _ (fdomain_pr1 pb adf)) => /setX_P [_ _]; aw; trivial.
  have bdf: inc b (domain f) by rewrite - pc; fprops.
  by move: (pa _ (fdomain_pr1 pb bdf)) => /setX_P [_ _]; aw.
move => [fgf df fa fb fc]; apply/Zo_P; split => //; apply/gfunctions_P2.
split => // t /(range_gP fgf) [z zdf ->].
by move: zdf; rewrite df; case /set2_P => -> //; rewrite - sf.
Qed.

Lemma formula_val_not X a  (x := J val_not a) 
    (V := formula_val X x) (Va := formula_val X a): 
  formulap a ->
  [/\ V  = Val_of_not X (free_vars a) Va, sub V (formula_values X x) &
    forall f,  inc f V <-> 
      inc f  (formula_values X x) /\ ~ inc f Va].
Proof.
move => pa;move: (fkind_not_p2 pa) => [sa sb].
move: val_compare => [q0 q1 q2 q3 [q4 q5 q6 [q7 q8 q9]]].
have fv: (free_vars (J val_not a)) = free_vars a by apply: free_vars_not. 
have ->: V = Val_of_not X (free_vars a)  Va.
  rewrite /V (formula_val_rec X sa) /formula_val_aux; aw. 
  Ytac0; Ytac0; Ytac0; Ytac0.
  rewrite fv LgV//; apply/Zo_P; split => //; rewrite sb.
   apply: (cltS (NS_formula_len pa)).
rewrite - fv;split; [ exact | by move => t /setC_P [] | ].
by split; [ move /setC_P | move => h; apply /setC_P].
Qed.

Lemma formula_val_or X  a b (x := J val_or (J a b)) 
    (V := formula_val X x) (Va := formula_val X a)(Vb := formula_val X b):
  formulap a -> formulap b ->
  [/\ V = Val_of_or X (free_vars a) (free_vars b) Va Vb, 
     sub V (formula_values X x) &
   forall f, inc f V <-> 
     (inc f  (formula_values X x) /\
         (inc (restr f (free_vars a)) Va \/ inc (restr f (free_vars b)) Vb))].
Proof.
move => pa pb;move: (fkind_or_p2 pa pb) => [sa sb]. 
move: val_compare => [q0 q1 q2 q3 [q4 q5 q6 [q7 q8 q9]]].
have ->: V = Val_of_or X (free_vars a) (free_vars b) Va Vb.
  rewrite /V (formula_val_rec X sa) /formula_val_aux.
  aw; Ytac0; Ytac0; Ytac0; Ytac0.
  have ha:= (NS_formula_len pa).
  have hb:= (NS_formula_len pb).
  move: (cmax_p1 (CS_nat ha)(CS_nat hb)) => [sd se].
  have mN:natp (cmax (formula_len a)(formula_len b)) by apply:Gmax_E.
  by rewrite !LgV//; apply /Zo_P; split => //; rewrite sb; apply/cltSleP.
have pc:= (free_vars_or pa pb).
rewrite {3 4} /Val_of_or - pc -/x.
split; [ exact | apply: Zo_S | ].
by split; [ move => /Zo_P | move => h; apply/Zo_P].
Qed.


Lemma formula_val_ex X  a b (x := J val_ex (J a b))
  (V := formula_val X x) (Vb := formula_val X b):
  variablep a -> formulap b ->
  [/\ V = Val_of_ex X (free_vars x) Vb, 
     sub V (formula_values X x) &
   forall f, inc f V <-> 
     (inc f  (formula_values X x) /\ 
         exists2 g, inc g Vb & f = restr g (free_vars x))].
Proof.
move => pa pb;move: (fkind_ex_p2 pa pb)=> [sa sb].
have pc:=free_vars_ex pa pb. 
move: val_compare => [q0 q1 q2 q3 [q4 q5 q6 [q7 q8 q9]]].
have hN := NS_formula_len pb.
have ->: V = Val_of_ex X (free_vars x) Vb.
  rewrite /V (formula_val_rec X sa) /formula_val_aux; aw. 
  Ytac0; Ytac0; Ytac0; Ytac0; rewrite LgV//.
  apply/Zo_P; split => //; rewrite sb; apply: (cltS hN).
split; [done | apply:Zo_S |by split; [ move => /Zo_P | move => h; apply/Zo_P]].
Qed.

Lemma formula_val_i X x:
    formulap x -> sub (formula_val X x) (formula_values X x).
Proof.
move => fx.
case: (equal_or_not (formula_len x) \0c) => ha.
  move/(flength0P fx):ha => /atomic_formulaP [pa qa qb qc pc]. 
  case: pc => h.
    by move:(proj32 (formula_val_inc X qb qc)); rewrite qa - h pa.
    by move:(proj32 (formula_val_eq X qb qc)); rewrite qa - h pa.
move:(flength_nz fx ha) => [mN hc hd].
move/next_formulasP:hc; case.
+ done.
+ move => [pc pv qx]; move: (proj32 (formula_val_not X (formula_hi mN qx))).
  by rewrite - pv pc.
+ move => [pc pv qa qb qc]. 
  move: (proj32 (formula_val_or X (formula_hi mN qb)(formula_hi mN qc))).
  by rewrite - pv qa pc.
+ move => [pa pb pc pd pe].
  move: (proj32(formula_val_ex X pd (formula_hi mN pe))).
  by rewrite  pc - pb pa.
Qed.

Lemma formula_val_ic X x f:
  formulap x -> closed_formula x -> inc f (formula_val X x) ->
  f = emptyset.
Proof.
move => pa pb pc.
move: (formula_val_i pa pc);rewrite /formula_values pb.
by move /gfunctions_P2 => [_ /domain_set0_P -> _].
Qed.

Lemma formula_or_simp X a: formulap a -> 
   formula_val X (J val_or (J a a)) =  formula_val X a.
Proof.
move => pa.
move: (proj33 (formula_val_or X pa pa)).
set Va := (formula_val X a). 
set V := (formula_val X (J val_or (J a a))).
rewrite /formula_values (free_vars_or pa pa) setU2_id => H.
have ha: forall f,
  inc f  (gfunctions (free_vars a) X) ->  (restr f (free_vars a)) = f.
  move => f /gfunctions_P2 [qa qb qc].
  apply: fgraph_exten; [ fprops |  exact | by aw | aw => t tv; rewrite LgV// ].
set_extens f.
  by move /H => [qa]; rewrite (ha _ qa); case.
  move => qa; move: (formula_val_i pa qa) => qb.
by apply/H; split => //; left;  rewrite (ha _ qb).
Qed.


Lemma formula_not_simp X a: formulap a -> 
   formula_val X (J val_not (J val_not a)) =  formula_val X a.
Proof.
move => pa.
move: (proj33 (formula_val_not X pa)).
set x := (J val_not a); set E := (formula_val X x) => H.
have pb: formulap (J val_not a) by exact (proj1 (fkind_not_p2 pa)).
move: (proj33 (formula_val_not X pb)).
set y := (J val_not x); set F := (formula_val X y).
have e1: (formula_values X y) =  (formula_values X x).
   by rewrite /formula_values (free_vars_not pb).
have e2: (formula_values X x) =  (formula_values X a).
   by rewrite /formula_values (free_vars_not pa).
rewrite e1 -/E => Hf.
set_extens t.
  by move /Hf => [ta tb]; ex_middle  ba; case tb; apply /H.
move => h; apply/Hf; move: (formula_val_i pa h); rewrite e2 => qb.
by split => // /H [hu hv].
Qed.


Lemma formula_ex_simp X a b: 
  variablep a -> formulap b -> ~(inc a (free_vars b)) ->
  formula_val X (J val_ex (J a b)) =  formula_val X b.
Proof.
move => pa pb pc.
move: (proj33 (formula_val_ex X pa pb)).
set x :=  (J val_ex (J a b)); set E := (formula_val X x).
have e1: free_vars x = free_vars b.
   by rewrite  (free_vars_ex pa pb) setC1_eq.
have ->: (formula_values X x) = (formula_values X b).
   by rewrite /formula_values e1.
have aux: forall f, inc f (formula_values X b)  ->  f = restr f (free_vars x). 
  move => f /gfunctions_P2 [pha hb hc]. 
  apply: fgraph_exten; [ exact | fprops | by aw; rewrite e1 |].
  by move => t tdf /=; rewrite LgV// //e1 - hb.
move => H; set_extens t. 
  by move /H=> [ha [g gr]]; rewrite - (aux _ (formula_val_i pb gr)) => ->.
move => tb; move:(formula_val_i pb tb) => h1; apply/H; split => //; ex_tac.
Qed.



Definition formula_ex0 :=
  J val_not (J val_ex (J \0c (J val_eq (J \0c \0c)))).
Definition formula_ex1 :=
 J val_not (J  val_ex (J \0c (J val_not (J val_eq (J \0c \0c))))).

Lemma formula_ex0_pr (x := formula_ex0) X:
   nonempty X -> 
  [/\ formulap x, formula_len x = \2c, free_vars x = emptyset &
     (formula_val X x) = \0c].
Proof.
move => [w wX].
rewrite /x /formula_ex0.
set a := (J val_eq (J \0c \0c)).
set b := (J val_ex (J \0c a)).
set c := (J val_not b).
have v0: variablep \0c by apply:NS0.
move:(free_vars_eq v0 v0); rewrite -/a -/(singleton _) => fva.
case: (fkind_eq_p2 v0 v0); rewrite -/a => fa  fla.
move:(fkind_ex_p2 v0 fa); rewrite -/b fla succ_zero; move =>[fb flb].
move: (free_vars_ex v0 fa); rewrite -/b fva setC_v => fvb.
move:(fkind_not_p2 fb); rewrite -/fb -/c flb succ_one;move =>[fc flc].
move:(free_vars_not fb); rewrite -/fc -/c fvb => fvd.
split => //.
set Va:= (formula_val X a).
set Vb:= (formula_val X b).
set Vc := formula_val X c.
move:(proj33 (formula_val_eq X v0 v0)); rewrite -/a -/Va;move => Vap.
move: (proj33 (formula_val_ex X v0 fa)); rewrite -/b -/Vb fvb => Vbp.
move: (proj33(formula_val_not X fb)); rewrite -/Vc -/Vb -/c => Vcp.
case: (emptyset_dichot Vc) => // [][ f /Vcp [/gfunctions_P2 [ga gb gc]]]; case.
move: gb; rewrite fvd => /domain_set0_P ->; apply /Vbp; split.
  apply/gfunctions_P2; split; aw; fprops; apply: fgraph_set0.
set g := Lg (singleton \0c) (fun z => w).
exists g.
  move : (set1_1 \0c) => zz.
  rewrite /g;apply /Vap; rewrite LgV// Lgd; split;fprops.
by rewrite /restr /Lg funI_set0.
Qed.


Lemma formula_ex1_pr (x := formula_ex1) X:
  [/\ formulap x, formula_len x = \3c, free_vars x = emptyset &
     (formula_val X x) = \1c].
Proof.
rewrite /x /formula_ex1.
set a := (J val_eq (J \0c \0c)).
set b := (J val_not a).
set c := (J val_ex (J \0c b)).
set d := (J val_not c).
have v0: variablep \0c by apply:NS0.
move:(free_vars_eq v0 v0); rewrite -/a -/(singleton _) => fva.
case: (fkind_eq_p2 v0 v0); rewrite -/a => fa fla.
move:(fkind_not_p2 fa); rewrite -/fa -/b fla succ_zero;move =>[fb flb].
move:(free_vars_not fa); rewrite -/fb -/b fva => fvb.
move:(fkind_ex_p2 v0 fb); rewrite -/c flb succ_one; move =>[fc flc].
move: (free_vars_ex v0 fb); rewrite -/c fvb setC_v => fvc.
move:(fkind_not_p2 fc); rewrite -/fc -/d flc -/card_three;move =>[fd fld].
move:(free_vars_not fc); rewrite  -/fd -/d fvc => fvd.
split => //.
set Va:= (formula_val X a).
set Vb:= (formula_val X b).
set Vc := formula_val X c.
set Vd := formula_val X d.
move:(proj33 (formula_val_eq X v0 v0)); rewrite -/a -/Va;move => Vap.
move: (proj33(formula_val_not X fa)); rewrite -/Vb -/Va -/b => Vbp.
move: (proj33 (formula_val_ex X v0 fb)); rewrite -/c -/Vc fvc => Vcp.
move: (proj33(formula_val_not X fc)); rewrite -/Vd -/Vc -/d => Vdp.
have eq1: (formula_values X d) = \1c.
  by rewrite /formula_values fvd gfunctions_empty. 
have qa:inc emptyset (formula_values X d) by rewrite eq1; apply /set1_P.
apply: set1_pr; last by move => z /Vdp; rewrite eq1; move => [/set1_P].
apply/Vdp; split => // /Vcp [_ [g /Vbp [ ga gb] _]]; case: gb; apply/Vap.
move/gfunctions_P2: ga; rewrite fvb; move => [gb gc gd]; split => //.
apply: gd; apply /(range_gP gb); exists \0c => //; rewrite gc; fprops.
Qed.


Definition formula_ex2 :=
  J val_not (J val_ex (J \0c (J val_not (J val_or
     (J (J val_not (J val_in (J \0c \1c)))(J val_in (J \0c \2c))))))).


Lemma formula_ex2_pr (x := formula_ex2) X:
  transitive_set X ->
  [/\ formulap x, formula_len x = card_five, free_vars x = doubleton \1c \2c &
   forall f, inc f (formula_val X x) <-> 
     (inc f (formula_values X x) /\ sub (Vg f \1c) (Vg f \2c))].
Proof.
move => tsx.
rewrite /x /formula_ex2.
have v0: variablep \0c by apply:NS0.
have v1: variablep \1c by apply:NS1.
have v2: variablep \2c by apply:NS2.
set a := (J val_in (J \0c \1c)).
set na := (J val_not a).
set b := (J val_in (J \0c \2c)).
set onab := (J val_or (J na b)).
set nonab := (J val_not onab).
set enonab := (J val_ex (J \0c nonab)).
set phi:= (J val_not enonab).
have hb: csucc (cmax \1c \0c) = \2c by rewrite (cmax_yx cle_01) succ_one.
have hc: doubleton \0c \1c \cup doubleton \0c \2c  =
    (doubleton \1c \2c) +s1 \0c.
   set_extens t.
      case/setU2_P => /set2_P; case => ->; apply /setU1_P; fprops.
   case/setU1_P; last by move  ->; apply /setU2_P; left; fprops.
   case/set2_P => ->; apply/setU2_P; [left | right]; fprops.
have hd: csucc \2c = \3c by [].
have he: csucc \3c = \4c by [].
have hf: csucc \4c = card_five by [].
have hg: (doubleton \1c \2c +s1 \0c) -s1 \0c  =  (doubleton \1c \2c).
  apply:setU1_K => /set2_P; case; fprops. 
move:(free_vars_in v0 v1); rewrite -/a => fva.
move:(free_vars_in v0 v2); rewrite -/b => fvb.
case: (fkind_in_p2 v0 v1); rewrite -/a => fa fla.
case: (fkind_in_p2 v0 v2); rewrite -/b => fb flb.
move:(fkind_not_p2 fa); rewrite -/na fla succ_zero; move =>[fna flna].
move:(free_vars_not fa); rewrite -/na fva => fvna.
move:(fkind_or_p2 fna fb); rewrite -/onab flna flb hb; move =>[fc flc].
move:(free_vars_or fna fb); rewrite -/onab fvna fvb hc => fvc.
move:(fkind_not_p2 fc); rewrite -/nonab flc hd; move =>[fd fld].
move:(free_vars_not fc); rewrite -/nonab fvc => fvd.
move:(fkind_ex_p2 v0 fd); rewrite -/enonab fld he; move =>[fe fle].
move: (free_vars_ex v0 fd); rewrite -/enonab fvd hg => fvg.
move :(fkind_not_p2 fe); rewrite -/phi fle hf; move =>[ff flf].
move:(free_vars_not fe); rewrite -/phi fvg => fvf.
split => //.
set Va:= (formula_val X a).
set Vb:= (formula_val X b).
set Vc := formula_val X na.
set Vd := formula_val X onab.
set Ve := formula_val X nonab.
set Vf := formula_val X enonab.
move:(proj33 (formula_val_inc X v0 v1)); rewrite -/a -/Va;move => Vap.
move:(proj33(formula_val_inc X v0 v2)); rewrite -/b -/Vb;move => Vbp.
move: (proj33(formula_val_not X fa)); rewrite -/na -/Va -/Vc; move => Vcp.
move: (proj33(formula_val_or X fna fb)); rewrite -/onab fvna fvb -/Vd -/Vc -/Vb.
  move => Vdp.
move: (proj33(formula_val_not X fc)); rewrite -/nonab -/Vd -/Ve => Vep.
move: (proj33 (formula_val_ex X v0 fd)); rewrite -/enonab -/Ve -/Vf fvg.
move => Vfp.
move: (proj33(formula_val_not X fe)); rewrite -/phi -/Vf => Vgp.
have q1: inc \1c (doubleton \0c \1c) by fprops.
have q2: inc \0c (doubleton \0c \1c) by fprops.
have q3: inc \2c (doubleton \0c \2c) by fprops.
have q4: inc \0c (doubleton \0c \2c) by fprops.
move => f; split.
  move/Vgp => [sa sb]; split => //; ex_middle bad.
  have [t ta tb]: exists2 t, inc t (Vg f \1c)  & ~inc t (Vg f \2c).
    ex_middle bad2; case bad => t t1; ex_middle t3; case bad2; ex_tac.
  clear bad; case sb; apply /Vfp; split.
     by move: sa; rewrite /formula_values fvf fvg.
  set g := f +s1 (J \0c t).
  move/gfunctions_P2: sa; rewrite fvf; move => [fpa fpb fpc].
  have /fpc wf2: inc  (Vg f \2c) (range f). 
       apply/(range_gP fpa); exists \2c => //;rewrite  fpb; fprops.
  have /fpc wf1: inc  (Vg f \1c) (range f). 
       apply/(range_gP fpa); exists \1c => //;rewrite  fpb; fprops.
  have fpd: ~ inc \0c (domain f) by  rewrite fpb => /set2_P;case; fprops.
  have fgg: fgraph g by apply: fgraph_setU1.
  have dg: domain g = doubleton \1c \2c +s1 \0c.
    by move:(domain_setU1 f \0c t); rewrite fpb.
  have tX:=(tsx _ wf1 _ ta).
  have fpf:inc g (formula_values X nonab).
     apply/gfunctions_P2; rewrite fvd; split => //.
     rewrite /g (range_setU1) => s /setU1_P; case => //; first by apply: fpc.
     by move => ->.
  have fpg: f = restr g (doubleton \1c \2c).
  apply:fgraph_exten; aww => s sd; rewrite LgV//; last by ue.
    by symmetry;apply: setU1_V_in.
  have g0:  (Vg g \0c)  = t  by rewrite setU1_V_out.
  have g1:  (Vg g \1c)  = Vg f \1c  by rewrite setU1_V_in // fpb; fprops.
  have g2:  (Vg g \2c)  = Vg f \2c  by rewrite setU1_V_in // fpb; fprops.
  have vg0x:  inc (Vg g \0c) X by ue.
  have vg1x:  inc (Vg g \1c) X by ue.
  have vg2x:  inc (Vg g \2c) X by ue.
  have ea: inc (Vg g \0c) (Vg g \1c) by rewrite g0 g1.
  exists g => //; apply /Vep; split => //; move /Vdp => [ka]; case => kb.
    by move/Vcp: kb => [kc];case; apply /Vap; rewrite !LgV// Lgd; split; fprops.
  by move /Vbp: kb;  move => [_ _ _ _];rewrite !LgV// g0 g2.
move => [ga fp1]; apply/Vgp; split => // fif.
move/gfunctions_P2:ga => [fgf df rgf]; rewrite fvf in df.
move/Vfp:fif => [_ [g /Vep [/gfunctions_P2 [ga gb gc] gv] gw]]; case gv.
rewrite fvd in gb.
apply /Vdp; split; first by  apply /gfunctions_P2; rewrite fvc; split.
have g1: Vg g \1c = Vg f \1c by rewrite gw LgV; fprops.
have g2: Vg g \2c = Vg f \2c by rewrite gw LgV; fprops.
have g0x: inc (Vg g \0c) X. 
    apply: gc; apply /(range_gP ga);exists \0c =>//;ue.
have g1x: inc (Vg g \1c) X. 
    apply: gc; apply /(range_gP ga);exists \1c =>//;ue.
have g2x: inc (Vg g \2c) X. 
    apply: gc; apply /(range_gP ga);exists \2c =>//;ue.
case: (inc_or_not (Vg g \0c) (Vg g \1c)); [right  | left].
  apply /Vbp; rewrite Lgd !LgV//; split; fprops.
  by move: fp1; rewrite g2 - g1; apply.
have hw: fgraph (restr g (doubleton \0c \1c)) by fprops.
have hx: sub (range (restr g (doubleton \0c \1c))) X.
  move => t /(range_gP hw); rewrite Lgd; move => [s sa ->].    
  by rewrite LgV //;case /set2_P: sa => ->.
apply/Vcp; split.
   apply  /gfunctions_P2; rewrite Lgd fvna; split => //.
by move/Vap => [_ _ _ ]; rewrite !LgV.
Qed.

(** Formulas with parameters *)
Definition pformula x :=
  [/\ pairp x, formulap (P x), fgraph (Q x) 
     & sub (domain (Q x)) (free_vars (P x))].

Definition pformula_in X x := pformula x /\ sub (range (Q x)) X.

Definition pfree_vars x := (free_vars (P x)) -s (domain (Q x)).
Definition pclosed x := pfree_vars x = emptyset.

Definition pformulas_in X :=
   Zo (all_formulas \times (sub_fgraphs variables X)) (pformula_in X).
Definition pcformulas_in X :=
   Zo (all_formulas \times (sub_fgraphs variables X))
      (fun f => pformula_in X f /\ free_vars (P f) = domain (Q f)). 

Lemma pformulas_inP X f: inc f (pformulas_in X) <->  pformula_in X f.
Proof.
split; [by move /Zo_hi | move => h; apply /Zo_i => //].
move:h => [[pa pb pc pd] pe].
apply /setX_P; split => //.
apply/ sub_fgraphsP; exists (domain (Q f)).
  by apply: (sub_trans pd); apply:(proj1 (free_vars_variables pb)).
by apply/gfunctions_P2. 
Qed.

Lemma pcformulas_inP X f:
   inc f (pcformulas_in X) <->  (pformula_in X f /\ pclosed f).
Proof.
split.
  move =>/Zo_P [pa [pb pc]]; split => //.
  by rewrite /pclosed /pfree_vars pc setC_v.
move => [qa].
move:(qa) => [[pa pb pc pd] pe].
rewrite /pclosed /pfree_vars => /empty_setC pf.
move: (extensionality pd pf) => pg.
apply /Zo_i; [ apply/setX_P; split => // | by split]. 
apply/ sub_fgraphsP; exists (free_vars (P f)).
  by apply:(proj1 (free_vars_variables pb)).
by apply/gfunctions_P2. 
Qed.


Lemma aleph0_pr X (x := cardinal X) (c := x +c aleph0):
  [/\  aleph0 = cardinal Nat, aleph0 = cardinal variables,
       (x <=c aleph0 -> c = aleph0),   aleph0 <=c x -> c = x
    & [/\ infinite_c c,  aleph0 <=c c, cardinal X <=c c &
        (forall z, aleph0 <=c z -> cardinal X <=c z -> c <=c z ) ]].
Proof.
have ha: aleph0 = cardinal Nat by rewrite cardinal_Nat.
have hb: aleph0 = cardinal variables by rewrite /variables. 
have hc:= CIS_aleph0.
have ka: x <=c aleph0 -> c = aleph0.
  move => h; rewrite /c csumC;exact : (csum_inf h hc).
have kb:  aleph0 <=c x -> c = x.
  move => h; exact:  (csum_inf h (cle_inf_inf hc h)).
have hd: infinite_c c.
  case:(cleT_ee (CS_cardinal X) (proj1 hc)) => h.
      by rewrite(ka h).
  rewrite (kb h); exact (cle_inf_inf hc h).
move:  (csum_Mle0 (cardinal X) (proj1 hc)); rewrite  -/c => ua.
move: (csum_M0le omega0 (CS_cardinal X)); rewrite -/c => h7.
move: (csum_M0le (cardinal X) CS_omega); rewrite csumC -/c => h5.
have h6: (forall z, aleph0 <=c z -> cardinal X <=c z -> c <=c z ).
 move => z za zb; case:(cleT_ee (proj31 za) (proj31 zb)) => h.
   by rewrite (kb h).
   by rewrite (ka h).
split => //.
Qed.

Lemma cardinal_pformulas_in X :
  cardinal (pformulas_in X) = cardinal X +c aleph0.
Proof.
set Y :=  (pformulas_in X).
move: (aleph0_pr X) => /=; set c1 := cardinal X +c aleph0.
move => [h1 h2 h3 h4 [h5 h6 h7 h8]].
have hd: aleph0 <=c cardinal Y.
  pose phi i:= J (J val_eq (J i i)) emptyset.
  have ax: forall i, inc i variables -> inc (phi i) Y.
    move=> i iv; apply/pformulas_inP;rewrite /phi; split; first split;aww.
    + exact (proj1(fkind_eq_p2 iv iv)).
    + exact fgraph_set0.
  set f := Lf phi variables Y.
  have injf: injection f.
     apply:lf_injective => // u v _ _ h.
     exact: (pr1_def (pr2_def (pr1_def h))).
  move: (inj_source_smaller injf); rewrite /f; aw; ue.
have he: cardinal X <=c cardinal Y.
  pose phi i:= J (J val_eq (J \0c \0c)) (singleton (J \0c i)).
  have ax: forall i, inc i X -> inc (phi i) Y.
    move => i iv.
    move: (simple_fct NS0 iv ) => [pa pb pc pd [pe pf]].
    apply/pformulas_inP; rewrite /phi;split; first saw.
    + fprops.
    + exact (proj1(fkind_eq_p2 NS0 NS0)).
    + by rewrite (free_vars_eq NS0 NS0) pb.
    + by aw.
  set f := Lf phi X Y.
  have injf: injection f.
     apply:lf_injective => // u v _ _ h.
     exact: (pr2_def(set1_inj(pr2_def h))).
  by move: (inj_source_smaller injf); rewrite /f; aw. 
have hf: c1 <=c cardinal Y by exact: (h8 _ hd he).
set fa := (fun z => singleton z \times Zo 
       (sub_fgraphs variables X) (fun t => pformula_in X (J z t))).
have eq1 : Y = unionf all_formulas fa.
  set_extens t.
    move/pformulas_inP => h; move: (h) => [[pa pb pc pd] pe ].
    apply /setUf_P; exists (P t) => //; apply /setX_P; split => //.
        fprops.
    apply/ Zo_P; rewrite pa; split => //;apply/sub_fgraphsP.
    exists (domain (Q t)); last by apply/gfunctions_P2.
    exact:(sub_trans pd (proj1 (free_vars_variables pb))).
  move => /setUf_P [z za /setX_P [zb /set1_P zc /Zo_P [zd ze]]].
  by apply /pformulas_inP; rewrite - zb zc.
suff h: forall z, formulap z -> cardinal (fa z) <=c c1.
  move: (csum_pr1_bis all_formulas fa); rewrite - eq1 /csumb.
  set g := (Lg all_formulas (fun a : Set => cardinal (fa a))) => k1.
  move:countable_formulas => /countableP => uc.
  have ud: cardinal (domain g) <=c c1 by rewrite /g; aw;exact : (cleT uc h6).
  have ue:(forall i, inc i (domain g) -> Vg g i <=c c1). 
    by rewrite /g; aw => i idf; rewrite LgV//; apply: h.
  move: (notbig_family_sum h5 ud ue) => uf.
  exact: (cleA (cleT k1 uf) hf).
move => z fz; rewrite /fa cardinal_indexedr.
move: (free_vars_variables fz) => [sa /NatP sb].
set E := Zo _ _. 
set A := (\Po (free_vars z)); set B  := (fun u => gfunctions u X).
have : sub E (unionf A B).
  move => t /Zo_P [qa [[qb qc qd qe] qf]].
  rewrite pr1_pair in  qe; rewrite pr2_pair in qd qe qf.
  apply/setUf_P; exists (domain t); first by apply /setP_P.
  by apply/gfunctions_P2; split => //.
move/sub_smaller => le2.
move: (cleT le2 (csum_pr1_bis A B)); rewrite /csumb.
set f := (Lg A (fun a : Set => cardinal (B a))) => le1; apply: (cleT le1).
have k6: forall  t, inc t Nat -> t <=c c1.
  move => t k2; move /olt_omegaP: (k2) => k3.  
  exact: (cleT (proj1 (oclt3 (CS_nat k2) CS_omega k3)) h6).
have sc: cardinal (domain f) <=c c1.  
  rewrite /f/A; aw; rewrite card_setP - cpowcr; exact: (k6 _ (NS_pow NS2 sb)).
have sd: (forall i, inc i (domain f) -> Vg f i <=c c1).
   rewrite /f/A/B; aw; move => i ia; rewrite LgV//; move /setP_P: ia => ia.
   move: (Eq_fun_set i X) => /card_eqP <-;rewrite cpow_pr1.
   have hi := (NS_le_nat (sub_smaller ia) sb).
  case: (finite_or_infinite (proj31 he)) => fx.
     move/NatP: fx => fx; exact: (k6 _ (NS_pow fx hi)).
  exact: (cleT (cpow_inf1 fx hi) h7).
exact:(notbig_family_sum h5 sc sd). 
Qed.

Definition pformula_vals X x :=
  Zo (gfunctions (pfree_vars x) X) 
      (fun g => inc (Q x \cup g) (formula_val X (P x))).

Definition pformula_valid_on X f := pformula_vals X f = \1c.

Lemma pformula_vals_aux X x g:
  pformula_in X x -> inc g (gfunctions (pfree_vars x) X) ->
   inc (Q x \cup g) (formula_values X (P x)).
Proof.
move => [[pa pb pc pd] pe] /gfunctions_P2 [pf pg ph].
apply/gfunctions_P2; split.
+ apply: fgraph_setU2 => //; rewrite pg /pfree_vars; apply: set_I2Cr.
+ by rewrite domain_setU2 pg /pfree_vars setU2_C; apply/setCU_K.
+ rewrite range_setU2 => t/setU2_P; case; fprops.
Qed.

Lemma pfree_vars_closed_pr1 X x (V:= pformula_vals X x):
  pclosed x -> 
   (V = \0c \/ V = \1c) /\ (V = \1c <-> inc (Q x) (formula_val X (P x))).
Proof.  
rewrite /pclosed; move => h.
have sv1: sub V \1c.
  rewrite /V/pformula_vals h gfunctions_empty; apply: Zo_S.
have hb: inc emptyset \1c by  rewrite /card_one; fprops.
have sv2: V = \0c \/ V = \1c by move/setP_P: sv1; rewrite setP_1 => /set2_P.
split => //; split => ha.
  have: inc emptyset V by rewrite ha.
  by move => /Zo_hi; rewrite setU2_0.
have hc:  inc emptyset V. 
   apply /Zo_P; rewrite h gfunctions_empty  setU2_0; split; fprops.
by case sv2 => // hd;  move: hc; rewrite hd; case; case.
Qed.

Lemma pfree_vars_closed_pr X x: 
  pclosed x -> 
  (pformula_valid_on X x <-> inc (Q x) (formula_val X (P x))).
Proof. by move => /(pfree_vars_closed_pr1 X) [ _]. Qed.

Lemma pformula_ex a b X (x := formula_ex2)
   (g := variantL \1c \2c a b) (y := J x g):
  transitive_set X -> inc a X -> inc b X ->
  [/\  pformula y, pclosed y,  pformula_in X y &
  (pformula_vals X y) = \1c <-> (sub a b)].
Proof.
move => h ax bx.
move: (formula_ex2_pr h) => [pa pb pc pd].
have va: P y = x by rewrite /y; aw.
have vb: Q y = g by rewrite /y; aw.
have vfg: fgraph g by rewrite /g; fprops.
have dg: domain g = free_vars x by  rewrite variant_d.
have pe: pformula y.
  rewrite /pformula va vb dg /g /y;split => //;fprops.
have pf:pclosed y.
  by rewrite /pclosed /pfree_vars va vb dg setC_v.
have g1:  (Vg g \1c) = a by rewrite /g variant_V_a.
have g2:  (Vg g \2c) = b by rewrite /g variant_V_b  //; fprops.
have pg: sub (range g) X.
  move => t; move/(range_gP vfg).
   move => [u udf ->]; move: udf; rewrite dg pc; case/set2_P => ->; ue.
have ph: inc g (formula_values X formula_ex2) by apply/gfunctions_P2; split. 
split => //; first by split  => //; rewrite vb.
move: (pfree_vars_closed_pr X pf); rewrite va vb - g1 - g2 => H.
split; first by move /H /pd => [_ ].
move => h1; apply/H; apply/pd; split => //.
Qed.


Definition pformulas_in_val X P :=
   Zo (pcformulas_in P) (pformula_valid_on X).

Lemma pformulas_in_valP X P f:
 inc f (pformulas_in_val X P) <->
  [/\ pformula_in P f, pclosed f& pformula_valid_on X f]. 
Proof.
split; first by move /Zo_P => [/pcformulas_inP [pa pb] pc]; split.
by move => [pa pb pc];apply/Zo_P => //; split =>//; apply/pcformulas_inP. 
Qed.

Definition pformula_inst f :=
  J (J val_ex (J (union (pfree_vars f)) (P f))) (Q f).

Definition LS_setU X f (x:= (union (pfree_vars f))) :=
   Zo X (fun a => pformula_valid_on X (J (P f) ((Q f) +s1 (J x a)))).

Lemma LS_setU_p1 X f a (x:= (union (pfree_vars f)))
   (h:= (J (P f) ((Q f) +s1 (J x a)))):
  pformula_in X f -> (singletonp (pfree_vars f)) -> inc a X ->
  pformula_in X h /\ pclosed h.
Proof.
move => [[pa pb pc pd] pe] sf ax.
have qa: (pfree_vars f) = singleton x.
  by rewrite /x; move:sf => [t ->]; rewrite setU_1.
have dfx: domain (Q f) +s1 x = free_vars (P f).
  by move: qa; rewrite /pfree_vars => <-; rewrite (setU2_Cr pd).
move:(set1_1 x); rewrite - qa /pfree_vars => /setC_P [fvp xdq1].
have va: variablep x by exact :(proj1 (free_vars_variables pb) _ fvp).
have da: (domain (Q f +s1 J x a))  = free_vars (P f).
  by rewrite domain_setU1 dfx.
have ra: sub (range (Q f +s1 J x a)) X.
   rewrite range_setU1 => t /setU1_P; case; [ fprops | by move => ->].
have ha: pformula_in X (J (P f) (Q f +s1 J x a)).
  saw; saw; [fprops | by apply:fgraph_setU1 | ue].
by rewrite /pclosed /pfree_vars /h; aw; split => //;rewrite da setC_v.
Qed.

Lemma LS_setU_P X f a (x:= (union (pfree_vars f)))
   (h:= (J (P f) ((Q f) +s1 (J x a)))):
  pformula_in X f -> (singletonp (pfree_vars f)) ->
  ( inc a (LS_setU X f) <->
    [/\ inc a X, pformula_in X h,  pclosed h & pformula_valid_on X h] ).
Proof. 
move => pa pb; split.
  by move /Zo_P => [pc pd]; move: (LS_setU_p1 pa pb pc) => [pe pf]; split.
by move => [pc _ _ pd]; apply:Zo_i.
Qed.

Lemma pformula_inst_p1 f (g := pformula_inst f):
  pformula f -> (singletonp (pfree_vars f)) ->
  [/\ pformula g, pclosed g ,
    (forall X, pformula_in X f -> pformula_in X g) &
     forall X,  pformula_valid_on X g -> nonempty (LS_setU X f)].
Proof.
move => [pa pb pc pd] pe; rewrite /pformula_inst.
set x := union (pfree_vars f).
have qa: (pfree_vars f) = singleton x.
  by rewrite /x; move:pe => [t ->]; rewrite setU_1.
have dfx: domain (Q f) +s1 x = free_vars (P f).
  by move: qa; rewrite /pfree_vars => <-; rewrite (setU2_Cr pd).
move:(set1_1 x); rewrite - qa /pfree_vars => /setC_P [fvp xdq1].
have va: variablep x by exact :((proj1 (free_vars_variables pb)) _  fvp).
move:(free_vars_ex va pb); rewrite  - qa /pfree_vars (setC_K pd).
move:(proj1 (fkind_ex_p2 va pb)). 
set phi1 := (J val_ex (J x (P f))) => fp1 fv1.
have clg: pclosed g.
  by rewrite /pclosed /pfree_vars /g /pformula_inst -/x; aw; rewrite fv1 setC_v.
have pg: pformula g.
  have ff:=(proj1 (fkind_ex_p2  va pb)).
  rewrite /g /pformula /pformula_inst; aw; rewrite -/x fv1; split => //; fprops.
have ph: forall X, pformula_in X f -> pformula_in X g.
  by move => X [sa sb]; split => //; rewrite /g /pformula_inst; aw.
split => // X sb.
move:(formula_val_ex X va pb) => [_ sc sd].
move /(pfree_vars_closed_pr X clg): sb. 
rewrite/g /pformula_inst; aw; rewrite -/x => /sd [se [g1 sf sg]].
rewrite -/phi1 in se sg; rewrite  fv1 in sg.
move :(formula_val_i pb sf) =>/gfunctions_P2 [fg1 dg1 rg1].
set a := Vg g1 x.
have vaX: inc a X by apply: rg1; apply /(range_gP fg1); exists x => //; ue.
set g2 := (Q f +s1 J x a).
have gg: g1 = g2.
  by rewrite / g2 sg; symmetry; apply:setU1_restr => //; rewrite dg1.
have ra:pformula_in X (J (P f) g1).
  saw; saw; fprops; rewrite dg1; fprops.
have rb: pclosed (J (P f) g1). 
  by rewrite /pclosed/pfree_vars; aw; rewrite dg1 setC_v.
have rc: pformula_valid_on X (J (P f) g1).
  by  apply /(proj2(pfree_vars_closed_pr X rb)); aw.
by exists a; apply/Zo_P;split =>//; rewrite -/g2 - gg. 
Qed.

Definition LS_nextP_aux X P :=
 (Zo  (pformulas_in P) 
     (fun f => [/\ pformula f, (singletonp (pfree_vars f))  &
       pformula_valid_on X (pformula_inst f)])).

Definition LS_nextP X P :=
  fun_image (LS_nextP_aux X P) (fun z => rep (LS_setU X z)).
Definition LS_rec X P :=  induction_defined  (LS_nextP X) P.
Definition LS_res X P := union (target (LS_rec X P)).

Lemma LS_res_p0 X P x:
   inc x (LS_res X P) <-> (exists2 n, inc n Nat & inc x (Vf (LS_rec X P) n)).
Proof.
move:(induction_defined_pr (LS_nextP X) P).
rewrite -/LS_res; move => [h1 [ff h2] h3 h4].
split. 
  move/setU_P => [z za zb]; move: (h2 _ zb); rewrite h1.
  by move => [t ta tb]; exists t => //; rewrite /LS_rec - tb.
move => [n nN xv]; apply/setU_P; exists (Vf (LS_rec X P) n) => //.
by rewrite - h1 in nN; apply: Vf_target.
Qed.

Lemma card_LS_nextP X P :
   cardinal (LS_nextP X P) <=c cardinal P +c aleph0.
Proof.
have pa: cardinal (LS_nextP X P) <=c cardinal (LS_nextP_aux X P).
  apply: fun_image_smaller.
have: sub (LS_nextP_aux X P) (pformulas_in P) by apply: Zo_S.
by move/sub_smaller; rewrite cardinal_pformulas_in; apply: cleT.
Qed.

Lemma card_LS_res X P :
   cardinal (LS_res X P) <=c cardinal P +c aleph0.
Proof.
rewrite /LS_res.
move:(induction_defined_pr (LS_nextP X) P).
rewrite -/LS_res; move => [h1 h2 h3 h4].
have ff:= proj1 h2.
rewrite - (surjective_pr0 h2) (ImfE ff) -(setUb_alt(function_fgraph ff)).
move: (csum_pr1 (graph (induction_defined (LS_nextP X) P))).
rewrite (domain_fg (proj1 h2)) h1; rewrite /csumb.
set g := Lg Nat _ => h6.
move: (aleph0_pr P) => /=; set c1 := cardinal P +c aleph0.
move => [k1 k2 k3 k4 [k5 k6 k7 k8]].
have k9: cardinal (domain g) <=c c1 by rewrite /g; aw; rewrite - k1.
have hc:= CIS_aleph0.
have k10:(forall i, inc i (domain g) -> Vg g i <=c c1).
  rewrite /g;aw => i iN; rewrite LgV//; rewrite -/(Vf _  _); move: i iN.
  apply: Nat_induction; first by rewrite h3.  
  move => n nN; rewrite (h4 _ nN); set P1 := Vf  _ _ => Hrec.
  move:(card_LS_nextP  X P1) => h7.
  move: (csum_Mleeq aleph0 Hrec); rewrite /c1 - csumA csum_inf1 // => ha.
   exact: (cleT h7 ha).
by apply: cleT (notbig_family_sum k5 k9 k10). 
Qed.


Lemma formula_ext3 a X (z := J (J val_eq (J \0c \1c))(singleton (J \1c a))):
  inc a X -> 
  (LS_setU X z = singleton a /\ 
     forall Y, inc a Y -> (inc z (LS_nextP_aux Y X))).
Proof.
move => aX; rewrite /z; clear z.
set phi :=J val_eq (J \0c \1c).
move: (simple_fct NS1 aX); set f := (singleton (J \1c a)).
move => [fgf df rf sd1 [sd2 fv1]].
set phi0 := J phi f.
have v0: variablep \0c by apply: NS0.
have v1: variablep \1c by apply: NS1.
move:(free_vars_eq v0 v1); rewrite -/phi => fvphi.
case: (fkind_eq_p2 v0 v1); rewrite -/phi => fa _.
move: (proj33(formula_val_eq X v0 v1)); rewrite -/phi  => Ha.
have fphi0: pformula phi0. 
   rewrite /phi0 /pformula;split; aww.
   rewrite df fvphi => t /set1_P ->; fprops.
have fvphi0:pfree_vars phi0 = singleton \0c.
  rewrite /pfree_vars /phi0 pr1_pair pr2_pair fvphi df.
  apply: set1_pr; first by apply/setC1_P; split; fprops.
  by move => z /setC_P [/set2_P h /set1_P z1]; case: h.
have h1: (singletonp (pfree_vars phi0)) by rewrite fvphi0; exists \0c.
set phi' := (J val_ex (J \0c phi)).
move:(pformula_inst_p1 fphi0 h1).
rewrite /pformula_inst fvphi0 setU_1 /phi0; aw.
rewrite -/phi; move => [q1 q2 q3 q4].
have r1: pformula_in X (J phi f) by  split => //; aw. 
have fv3: free_vars (P phi0) = doubleton \0c \1c by rewrite /phi0; aw.
have fv2: domain (Q phi0) = singleton \1c  by rewrite /phi0; aw.
have va: (doubleton \0c \1c -s1 \1c) = singleton \0c.
   set_extens t; first by move => /setC1_P [/set2_P]; case => // -> _;fprops.
   move /set1_P => ->; apply /setC1_P; split; fprops.
have vd:  domain f +s1 \0c = doubleton \0c \1c.
   rewrite df; set_extens t. 
     case/setU1_P; [ move /set1_P => ->; fprops | move => ->; fprops ].
  case /set2_P => ->; apply /setU1_P; [by right | by left; fprops ].
have vb:(singleton \1c +s1 union (singleton \0c)) = doubleton \0c \1c.
  by rewrite setU_1 - df. 
have vc: (union (pfree_vars phi0)) = \0c.
   by rewrite /pfree_vars /phi0; aw; rewrite fvphi df va setU_1.
have sa: ~ inc \0c (domain f) by rewrite df => /set1_P; fprops.
have sb: inc \1c (domain f) by rewrite df; fprops. 
have r2: inc a (LS_setU X phi0).
   apply /Zo_P; split => //; apply/ pfree_vars_closed_pr.
     rewrite /pclosed /pfree_vars; aw; rewrite fv3 domain_setU1 fv2 va vb.
     by rewrite setC_v.
   aw; rewrite vc; rewrite /phi0; aw.
   move: (formula_val_eq X v0 v1) => []; rewrite -/phi => _ Hb Hc.
   apply /Hc; rewrite setU1_V_out // setU1_V_in // domain_setU1 vd.
   by split => //; apply: fgraph_setU1.
have r3: LS_setU X (J phi f) = singleton a. 
  apply set1_pr => // z /(LS_setU_P _ r1 h1); aw.
  rewrite fvphi0 setU_1;  move => [zx sc sd se].
  move /(pfree_vars_closed_pr X sd): se; aw; move /Ha => [_ _ Hb _].
  by move: Hb; rewrite setU1_V_out // setU1_V_in // fv1.
split => //.
move => Y aY; apply /Zo_P.
have r4: sub (range f) X by rewrite /f range_set1 => t /set1_P ->.
have r4': sub (range f) Y by rewrite /f range_set1 => t /set1_P ->.
have r5: inc (J phi f) (pformulas_in X).
  by  apply/pformulas_inP;split=> //; aw.
have r6: domain f = free_vars (J val_ex (J \0c phi)).
  rewrite (free_vars_ex v0 fa) df fvphi //; set_extens t.
    move => /set1_P ->; apply /setC1_P; fprops.
  move => /setC1_P [/set2_P]; case => // -> _; fprops.
have r7: inc f (formula_values Y (J val_ex (J \0c phi))).
  apply /gfunctions_P2; split => //.
split => //; split => //.
rewrite /pformula_inst fvphi0 setU_1; aw.
apply /(pfree_vars_closed_pr _ q2); aw.
move:(formula_val_ex Y v0 fa) => [_ sc sd]; apply/sd; split => //.
move :(restr_setU1 a fgf sa); set g := _ +s1 _ => r8.
exists g; last by rewrite - r6 r8.
move: (proj33(formula_val_eq Y v0 v1)); rewrite -/phi => Hb; apply /Hb.
rewrite /g domain_setU1 setU1_V_out // setU1_V_in // fv1 vd; split => //.
by apply: fgraph_setU1.
Qed.

Lemma rep_set1 a: rep (singleton a) = a.
Proof. by move: (rep_i(set1_ne a)) => /set1_P. Qed.


Lemma LS_nextP_pr1 X P: sub P X -> sub P (LS_nextP X P). 
Proof.
rename P into Pa.
move=> spx a ap; move: (spx a ap) => ax.
move: (proj1 (formula_ext3 ax))  (proj2 (formula_ext3 ap)).
set z := J _ _ => ha hb.
by apply/funI_P; exists z; [apply: (hb _ ax) | rewrite ha rep_set1 ].
Qed.

Lemma LS_nextP_pr2 X P n (Y:= (Vf (LS_rec X P) n)): 
   sub P X ->  natp n ->  sub P Y /\ sub Y X.
Proof.
move => pa pb; rewrite /Y {Y}.
move:(induction_defined_pr (LS_nextP X) P).
rewrite -/(LS_rec _ _); move => [h1 h2 h3 h4].
move: n pb; apply:Nat_induction; first by rewrite h3; split.
move => n nN [Hr1 Hr2]; rewrite (h4 _ nN). 
split; first by apply: (sub_trans Hr1); apply: (LS_nextP_pr1 Hr2).
rewrite /LS_nextP => t/ funI_P [z za ->].
move/Zo_P: za => [ha [hb hc hd]].
have he: pformula_in X z.
   move /pformulas_inP: ha => [ka kb]; split => //; exact: (sub_trans kb Hr2).
move: (pformula_inst_p1 hb hc) => [_ _ _ hf].
by move:(rep_i (hf _ hd)) => /Zo_S.
Qed.

Lemma LS_nextP_pr3 X P (Y:= LS_res X P):  sub P X ->  sub P Y /\ sub Y X.
Proof.
move => h; split.
  move => t tP; move:(proj1 (LS_nextP_pr2 h NS0) _ tP) => h1.
  apply/LS_res_p0; exists \0c; [exact NS0  | exact]. 
move => y /LS_res_p0 [n nN ha]; apply: (proj2 (LS_nextP_pr2 h nN) _ ha).
Qed.

Lemma LS_nextP_pr4 X P n m: sub P X -> n <=c m -> inc m Nat -> 
  sub  (Vf (LS_rec X P) n) (Vf (LS_rec X P) m).
Proof.
move => h0 nm mN.
move:(NS_le_nat nm mN) => nN.
move:(NS_diff n mN);rewrite -{2} (cdiff_pr nm); move:(m -c n).
apply: Nat_induction; first by rewrite (csum0r (proj31 nm)). 
move:(induction_defined_pr (LS_nextP X) P).
rewrite -/(LS_rec _ _); move => [h1 h2 h3 h4].
move => p pN hrec; rewrite (csum_nS _ pN) h4; fprops.
have hr1:= (proj2 (LS_nextP_pr2 h0 (NS_sum nN pN))).
by apply: (sub_trans hrec); apply: LS_nextP_pr1. 
Qed.

Lemma LS_nextP_pr5 X P E:
  sub P X -> finite_set E -> sub E (LS_res X P)  ->
  exists2 m, natp m & sub E (Vf (LS_rec X P) m).
Proof.
move => pa; move: E;  apply: finite_set_induction.
  move => _; exists \0c; fprops.
move => a b Hrec h1.
have [m mN mv]:= (Hrec(sub_trans (@sub_setU1 a b) h1)).
move: (h1 _ (setU1_1 a b)) => /LS_res_p0 [n nN nv].
move: (NS_sum nN mN)(Nsum_M0le n mN) (Nsum_M0le m nN); rewrite (csumC m).
set k := n +c m => ra rb rc; exists k => //.
move => t /setU1_P; case; first by move => /mv; apply:(LS_nextP_pr4 pa rb ra).
move => ->;  apply:(LS_nextP_pr4 pa rc ra nv).
Qed.



Lemma LS_main X P f (Y:=LS_res X P) : 
    sub P X -> pformula_in Y f -> pclosed f ->
   (pformula_valid_on X f <-> pformula_valid_on Y f).
Proof.
rename f into F; rename P into Pa;move => h0 pa pb.
move: (LS_nextP_pr3  h0) => []; rewrite -/Y => h1 h2.
set phi := P F; set f := Q F.
suff: inc f (formula_val X phi) <->  inc f (formula_val Y phi). 
  move => h; split.
    move  /(pfree_vars_closed_pr X pb) => /h.
    apply(pfree_vars_closed_pr Y pb).
  move /(pfree_vars_closed_pr Y pb) => /h.
  apply(pfree_vars_closed_pr X pb).
have df: domain f = free_vars phi.
  move:pa pb => [[vc vd ve vf] vg].
  by rewrite /pclosed /pfree_vars => /empty_setC vh; apply: extensionality.
move: pa => [[]]; rewrite -/f -/phi => _ fphi fgf _ rf.
move: f df fgf rf.
move: (formula_len_pr fphi) => [ua ub _];move: ua ub;clear pb. 
move: {1 2} (formula_len phi) => n na nb; move:n na phi nb fphi.
apply: Nat_induction.
   move => p pl0 fp f df fgf rg; move: pl0; rewrite formulas_rec0.
   move/atomic_formulaP => [ha hb hc hd he]; case: he => he.
     move: (formula_val_inc X hc hd)  (formula_val_inc Y hc hd).  
     move => [_ _ r1][_ _ r2]; move: r1 r2; rewrite hb - he ha => r1 r2.
     split;last by move/r2 => [q1 q2 q3 q4 q5]; apply/r1; split => //; apply h2.
     move/r1 => [q1 q2 q3 q4 q5]; apply/r2; split => //; apply: rg.
       apply/(range_gP q1); exists  (P (Q p)) => //; rewrite q2; fprops.
     apply/(range_gP q1); exists  (Q (Q p)) => //; rewrite q2; fprops.
  move: (formula_val_eq X hc hd)  (formula_val_eq Y hc hd).  
  move => [_ _ r1][_ _ r2]; move: r1 r2; rewrite hb - he ha => r1 r2.
  split; last by move/r2 => [q1 q2 q3 q4]; apply/r1; split => //; apply h2.
  move/r1 => [q1 q2 q3 q4]; apply/r2; split => //; apply: rg.
  apply/(range_gP q1); exists  (P (Q p)) => //; rewrite q2; fprops.
move => n nN Hrec p pr fp f df fgf rf.
have ha: inc f (formula_values X p). 
  by apply/gfunctions_P2;split => //; apply: (sub_trans rf h2).
have hb: inc f (formula_values Y p) by apply/gfunctions_P2. 
move: pr;rewrite(formulas_rec_succ nN); case /next_formulasP.
+ by move => r1;apply: Hrec.
+ move => [pc pd pe].
  have ka:= (formula_hi nN pe).
  move: (formula_val_not X ka) (formula_val_not Y ka).  
  move => [_ _ r1][_ _ r2]; move: r1 r2; rewrite -pd  pc=> r1 r2.
  have df1:domain f = free_vars (Q p).
    by rewrite - (free_vars_not ka) - pd pc.  
  have hr:= (Hrec (Q p) pe ka f df1 fgf rf).
  split. 
     by move/r1 => [sa sb]; apply/r2; split => // sc; case sb; apply/hr.
   by move/r2 => [sa sb]; apply/r1; split => // sc; case sb; apply/hr.
+ move => [pc pd pe pf pg].
  have ka:= (formula_hi nN pf).
  have kb:= (formula_hi nN pg).
  move: (formula_val_or X ka kb) (formula_val_or Y ka kb).  
  move => [_ _ r1][_ _ r2]; move: r1 r2; rewrite -pd pe pc => r1 r2.
  move: (free_vars_or ka kb);rewrite  -pd pe pc => fv.
  set f1:= (restr f (free_vars (P (Q p)))). 
  set f2:= (restr f (free_vars (Q (Q p)))).
  have f1d: (domain f1 = free_vars (P (Q p))) by rewrite /f1 restr_d.
  have f2d: (domain f2 = free_vars (Q (Q p))) by rewrite /f2 restr_d.
  have fg1: fgraph f1 by rewrite /f1; fprops.
  have fg2: fgraph f2 by rewrite /f2; fprops.
  have sd1: sub (free_vars (P (Q p))) (domain f). 
     by rewrite df fv => t ta; apply /setU2_P; left.
  have sd2: sub (free_vars (Q (Q p))) (domain f). 
     by rewrite df fv => t ta; apply /setU2_P; right.
  have rg1: sub (range f1) Y by exact (sub_trans (restr_range1 fgf sd1) rf).
  have rg2: sub (range f2) Y by exact (sub_trans (restr_range1 fgf sd2) rf).
  move: (Hrec _ pf ka f1 f1d fg1 rg1) => hr1.
  move: (Hrec _ pg kb f2 f2d fg2 rg2) => hr2.
  split.
    by move /r1 => [ra]; case; [move/hr1 => rb | move/hr2 => rb]; 
     apply /r2; split => //; [ left | right].
    by move /r2 => [ra]; case; [move/hr1 => rb | move/hr2 => rb]; 
     apply /r1; split => //; [ left | right].
+ move => [pa pb pc pd pe].
  have ka:= (formula_hi nN pe).
  move: (formula_val_ex X pd ka) (formula_val_ex Y pd ka)(free_vars_ex pd ka).
  rewrite - pb pc pa; move => [_ _ r1] [_ _ r2] fv;
  case: (inc_or_not (P (Q p)) (free_vars (Q (Q p)))) => hsimp; last first.
    move: (formula_ex_simp X pd ka hsimp) (formula_ex_simp Y pd ka hsimp).
    rewrite - pb pc pa => -> ->; apply: Hrec => //.
    by rewrite df fv; apply: setC1_eq.
  split; last first.
     move/r2 => [ua [g gv r3]]; apply/r1; split => //; exists g => //.
     move: (formula_val_i ka gv) => /gfunctions_P2 [sa sb sc].
     by apply/ (Hrec (Q (Q p)) pe ka _ sb sa sc).
  move => h3;move/r1: (h3) => [_ [g gv r3]]; apply/r2; split => //. 
  have[m mN ra]: exists2 m, inc m Nat & sub (range f) (Vf (LS_rec X Pa) m).
    have fa:= (proj2 (free_vars_variables fp)).
    have frf: finite_set (range f) by apply: finite_range => //;rewrite df.
    exact:(LS_nextP_pr5 h0 frf rf).
  set psi1 := J (Q (Q p)) f.
  have qa: pformula psi1.
    by rewrite /psi1;hnf; aw;split; fprops; rewrite df fv => t /setC1_P [].
  have qh:pformula_in X psi1.
    rewrite /psi1;split; [exact qa |  aw;apply:(sub_trans rf h2)].
  have qb:inc psi1 (pformulas_in (Vf (LS_rec X Pa) m)).
    by apply/pformulas_inP; rewrite /psi1;hnf; aw.
  have qc:pfree_vars psi1 = singleton (P (Q p)).
    rewrite /psi1/pfree_vars; aw; rewrite df fv; set_extens t.
        move => /setC_P [ta /setC1_P tb]; apply /set1_P; ex_middle bad.
        by case: tb.
    by move => /set1_P ->;apply /setC_P; split => // /setC1_P [].
  have qd: singletonp (pfree_vars psi1) by rewrite qc; exists (P (Q p)).
  set Pb := (Vf (LS_rec X Pa) m).
  case: (pformula_inst_p1 qa qd);  set gg := pformula_inst _.
  move => [ga gb gc gd ge gf gh].
  have qe: pformula_valid_on X gg. 
     apply/(pfree_vars_closed_pr X ge); rewrite /gg /pformula_inst /psi1; aw.
     rewrite qc setU_1 pc - pb pa //.
  have qf:inc psi1 (LS_nextP_aux X Pb) by apply:Zo_i. 
  set a := (rep (LS_setU X psi1)).
  have qg: inc a (LS_nextP X Pb) by apply/funI_P; ex_tac. 
  have aa: inc a (LS_setU X psi1) by apply: rep_i; apply: gh.
  have aY: inc a Y.  
    move:(induction_defined_pr (LS_nextP X) Pa).
    rewrite -/(LS_rec _ _); move => [_ _ _  h4'].
    move: qg; rewrite - (h4' _ mN) => aqg.
    by apply /LS_res_p0; exists (csucc m) => //; apply:NS_succ.
  move/(LS_setU_P a qh qd):aa; rewrite /psi1;aw; set g1 := _ +s1 _.
  have g1v: g1 = f +s1 J (P (Q p)) a by rewrite /g1 qc setU_1.
  have qi: ~ inc (P (Q p)) (domain f) by rewrite df fv => /setC1_P [].
  have Rf: f = restr g1 (free_vars p) by rewrite -(restr_setU1 a fgf qi) df g1v.
  move => [aX rc rd re]; exists g1 => //.
  move/(pfree_vars_closed_pr X rd): re; aw => g1X.
  move: rc => [[_ _]]; aw; move => ta tb tc.
  have dg1: domain g1 = free_vars (Q (Q p)).
    rewrite g1v domain_setU1 df fv; set_extens t.
      move => /setU1_P; case; [by move/setC1_P => [] | by move => ->].
    move => h; apply/setU1_P;case: (equal_or_not t (P (Q p))); fprops.
    by move => t1; left; apply /setC1_P.
  have rg1: sub (range g1) Y.
    rewrite range_setU1;move => t /setU1_P; case;[ apply: rf | by move => ->].
  by apply /(Hrec _ pe ka _ dg1 ta rg1).
Qed.

Theorem Lowenheim_Skolem X P (Y:=LS_res X P):
   sub P X ->
   [/\ sub P Y, sub Y X, cardinal Y <=c cardinal P +c aleph0 &
    forall F, inc F (pformulas_in_val X P) -> pformula_valid_on Y F].
Proof.
move => ha.
have hb:=(card_LS_res X P).
have [hc hd]:= (LS_nextP_pr3 ha).
split => // F /pformulas_in_valP [ [pa pb] p2 p3].
have p1: pformula_in Y F by split => //; apply: (sub_trans pb hc).
by apply/ (LS_main ha p1 p2).
Qed.




End Formulae.

End Realisation.





