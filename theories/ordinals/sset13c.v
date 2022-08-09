(** * Theory of Sets : Natural sum & product
  Copyright INRIA (2016)2018) Apics, Marelle Team (Jose Grimm).
*)

(* $Id: sset13c.v,v 1.4 2018/09/04 07:57:59 grimm Exp $ *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From gaia Require Export sset13b.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Ordinals3c.

(** Natural sum of ordinals *)

Definition cnf_nat_sum_mons x y :=
  fun_image (cnf_exponents x \cup cnf_exponents y)
            (fun i => J i (Vr x i +c Vr y i)).

Definition cnf_nat_sum x y := cnf_sort (cnf_nat_sum_mons x y).

Notation "x +#f y" := (cnf_nat_sum x y) (at level 50).


Lemma cnf_nat_sum_range x y: cnfp x -> cnfp y ->
   cnf_rangep (cnf_nat_sum_mons x y).
Proof.
move => ox oy.
have ha: finite_set (cnf_nat_sum_mons x y).
  have aux z: cnfp z -> finite_set (cnf_exponents z).
     move => [ha hb _ _].
     apply/finite_fun_image; apply: (finite_range ha).
     apply:(finite_set_nat hb).
  apply: finite_fun_image; apply: (setU2_finite (aux _ ox) (aux _ oy)).
have hb: sgraph (cnf_nat_sum_mons x y).
  move => t /funI_P [i ii ->]; fprops.
have hc: fgraph (cnf_nat_sum_mons x y).
  split; [exact |  move => t j /funI_P [a ii ->] /funI_P [b ji ->]].
  by rewrite 2! pr1_pair => ->.
split => // i  /funI_P [a ii ->]; case/setU2_P: ii.
   move/funI_P => [z zr zv].
   move/(range_gP (proj41 ox)): zr => [k kdx kv].
   rewrite {1 2} zv kv -/(oexp x k) (Vr_correct ox kdx). 
   move /cnfpP:(ox) =>/proj43 => mn; move: (mn _ kdx)=> [qa qb qc].
   split;aww; rewrite csumC.
   apply: (posnat_add (NS_Vr a oy) qc).
move/funI_P => [z zr zv].
move/(range_gP (proj41 oy)): zr => [k kdx kv].
rewrite {1 3} zv kv -/(oexp y k) (Vr_correct oy kdx). 
move /cnfpP:(oy) =>/proj43 => mn; move: (mn _ kdx)=> [qa qb qc].
split;aww;apply: (posnat_add (NS_Vr a ox) qc).
Qed.

Lemma cnfp_nat_sum x y: cnfp x -> cnfp y  -> cnfp (x +#f y).
Proof.
move => ox oy.
by case:(cnf_sort_correct (cnf_nat_sum_range ox oy)).
Qed.


Lemma cnf_nat_sumC x y: x +#f y = y +#f x.
Proof.
rewrite /cnf_nat_sum/cnf_nat_sum_mons setU2_C.
by apply: f_equal; apply: funI_exten => a _; rewrite csumC.
Qed.

Lemma cnf_nat_sum_p1 x y : cnfp x -> cnfp y -> 
  cnf_exponents (x +#f y) = cnf_exponents x \cup cnf_exponents y.
Proof.
move => ox oy.
move:(cnf_sort_correct (cnf_nat_sum_range ox oy)).
set z := cnf_sort _; move => [za zb].
rewrite {1}/cnf_exponents zb /cnf_nat_sum_mons; set_extens t.
  by move/funI_P =>[a /funI_P[b bE ->] ->]; rewrite pr1_pair.
move=> jE; apply/funI_P.
exists ( J t (Vr x t +c Vr y t)); last by aw.
apply/funI_P; ex_tac. 
Qed.

Lemma Vr_oor x e: ~inc e (cnf_exponents x) -> Vr x e = \0c.
Proof. by move => h; rewrite /Vr (Vg_out_of_range h). Qed.
  
Lemma cnf_nat_sum_p2 x y : cnfp x -> cnfp y ->  forall e,
   Vr (x +#f y) e =  (Vr x e) +c  Vr y e.
Proof.
move => ox oy e.
move:(cnf_sort_correct (cnf_nat_sum_range ox oy)).
rewrite/cnf_nat_sum; set z := cnf_sort _; move => [oz rz].
have dz: domain (range z) = domain (range x) \cup (domain (range y)).
  rewrite rz /cnf_nat_sum_mons; set_extens t.
    by move/funI_P =>[i /funI_P[j ja ->] ->]; aw.
  move => ta; apply /funI_P.
  exists (J t (Vr x t +c Vr y t)); aw; trivial.
  by apply/funI_P; ex_tac.
case: (inc_or_not e (domain (range z))) => iE; last first.
  case: (inc_or_not e (domain (range x))) => edx.
    by case iE; rewrite dz; apply: setU2_1.
  case: (inc_or_not e (domain (range y))) => edy.
    by case iE; rewrite dz; apply: setU2_2.
  by rewrite  (Vr_oor iE) (Vr_oor edx) (Vr_oor edy) (csum0l CS0).
set w := RHS; have pp: inc (J e w) (range z).
  by rewrite rz;apply/funI_P;exists e => //; rewrite - dz.
by rewrite  (pr2_def(in_graph_V (cnf_range_fgraph  oz) pp)); aw.
Qed.


Lemma cnf_nat_sum_p3 x y z : cnfp x -> cnfp y -> cnfp z ->
  (forall e, Vr z e =  (Vr x e) +c  Vr y e) -> z = x +#f y.
Proof.
move => ox oy oz hz.
move:(cnfp_nat_sum ox oy) (cnf_nat_sum_p2 ox oy); set t := cnf_nat_sum x y.
move => ot tp.
by apply:(Vr_exten oz ot) => e; rewrite tp.
Qed.

Lemma cnf_nat_sum0 x : cnfp x ->x +#f \0f = x.
Proof.
move => ox; symmetry; apply: (cnf_nat_sum_p3 ox cnfp0 ox) => e. 
by rewrite cnf_coef_or_e_zero (csum0r (CS_nat (NS_Vr e ox))).
Qed.

Lemma cnf_nat_sum0n x : cnfp x -> \0f +#f x = x.
Proof.
by move => ox; rewrite cnf_nat_sumC; apply: cnf_nat_sum0.
Qed.


Lemma cnf_nat_sumA x y z: cnfp x -> cnfp y -> cnfp z -> 
  x +#f (y +#f z) = (x +#f y)   +#f z.
Proof.
move => ox oy oz.
move: (cnfp_nat_sum oy oz) (cnfp_nat_sum ox oy) => oyz oxy.
apply: (cnf_nat_sum_p3 oxy oz (cnfp_nat_sum ox oyz)) => e.
rewrite (cnf_nat_sum_p2 ox oyz) (cnf_nat_sum_p2 oy oz) (cnf_nat_sum_p2 ox oy).
apply: csumA.
Qed.


Definition natural_sum x y :=  cnf_val ((the_cnf x) +#f (the_cnf y)).

Notation "x +#o y" := (natural_sum x y) (at level 50).

Lemma OS_natural_sum x y :
  ordinalp x -> ordinalp y -> ordinalp (x +#o y).
Proof.
move => ox oy.
move: (the_cnf_p0 ox)  (the_cnf_p0 oy) => [qa qb][qc qd].
exact: (OS_cnf_val(cnfp_nat_sum qa qc)).
Qed. 

Lemma natural_sum0 x : ordinalp x -> (x +#o \0o) = x.
Proof.
move => ox.
move: (the_cnf_p0 ox) => [qa qb]. 
by rewrite /natural_sum the_CNF_0  cnf_nat_sum0. 
Qed.

Lemma natural_sumC x y : (x +#o y) = (y +#o x).
Proof.
by rewrite / natural_sum cnf_nat_sumC.
Qed.

Lemma natural_sumA a b c : ordinalp a -> ordinalp b -> ordinalp c ->
  a +#o (b +#o c) = (a +#o b) +#o c.
Proof.
move => oa ob oc.
move: (the_cnf_p0 oa) => [qa qb].
move: (the_cnf_p0 ob) => [qa' qb'].
move: (the_cnf_p0 oc) => [qa'' qb'']. 
rewrite /natural_sum.  
rewrite {1} (proj43(cnf_and_val_pb (cnfp_nat_sum qa' qa''))).
rewrite (cnf_nat_sumA qa qa' qa'').
by rewrite {1} (proj43(cnf_and_val_pb (cnfp_nat_sum qa qa'))).
Qed. 

Lemma Vr_monomial n a e: Vr (Lg \1c (fun _ : Set => J n a)) e = Yo (e = n) a \0c. 
Proof.
rewrite /Vr Lg_range funI_set1 /Vg range_set1;case:(equal_or_not e n) => en; Ytac0.
  set_extens t.
      by move/setU_P => [y ty /Zo_P [/set1_P <-]] .
  rewrite en;move=> ti; apply/setU_P; exists a => //; apply/Zo_P; fprops.
apply/set0_P => u.
by move => /setU_P [y yu /Zo_P[/set1_P -> ]] /set1_P /pr1_def.
Qed.

Lemma cnfnat_sum_mon n a b: ordinalp n -> a <o omega0 -> b <o omega0->
  (oopow n *o a +#o oopow n *o b) = (oopow n *o (a +o b)).
Proof.
move => on lao lbo.
move: (proj31_1 lao) (proj31_1 lbo) => oa ob.
have ooa:= (OS_prod2 (OS_oopow on) oa).
have oob:= (OS_prod2 (OS_oopow on) ob).
case: (ozero_dichot oa) => az.  
  by rewrite az (osum0l ob) oprod0r natural_sumC (natural_sum0 oob).
case: (ozero_dichot ob) => bz.
  by rewrite bz (osum0r oa) oprod0r (natural_sum0 ooa). 
have pa: posnatp a by  apply/ posnat_ordinalp.
have pb: posnatp b by  apply/ posnat_ordinalp.
move: (cnf_one_term on pa); set A := Lg _ _; move => [cA _ eqA1 eqA2].
move: (cnf_one_term on pb); set B := Lg _ _; move => [cB _ eqB1 eqB2].
have eab: a +o b = a +c b by rewrite osum2_2int //; apply/olt_omegaP.
have pc:  posnatp (a +o b) by rewrite eab; apply: (posnat_csum2 pa pb).
move: (cnf_one_term on pc); set C := Lg _ _; move => [cC _ eqC1 eqC2].
rewrite  /natural_sum eqA1 eqB1 - eqC2; congr cnf_val.
symmetry; apply: (cnf_nat_sum_p3 cA cB cC) => e.
rewrite ! Vr_monomial.
by case: (equal_or_not e n) => en; Ytac0; Ytac0; Ytac0 => //; rewrite (csum0r CS0).
Qed.

Lemma cnfnat_sum_rem n a x: ordinalp n -> a <o omega0 -> x <o oopow n ->
  (oopow n *o a +o x) = (oopow n *o a +#o x).
Proof.
move => on lao lxo.
have ox := proj31_1 lxo.
have oa := proj31_1 lao.
have ooa:= (OS_prod2 (OS_oopow on) oa).
case: (ozero_dichot oa) => az.
  by rewrite az oprod0r (osum0l ox) natural_sumC (natural_sum0 ox).
have pa: posnatp a by  apply/ posnat_ordinalp.
case: (ozero_dichot ox) => xp.
  by rewrite xp (osum0r ooa) (natural_sum0 ooa).
move: (cnf_one_term on pa); set A := Lg _ _; move => [cA _ eqA1 eqA2].
move: (the_cnf_p0_nz xp) => [qa qb].
have qc: \0c <c domain A by rewrite /A Lgd; fprops.
have  i01: inc \0c \1c by apply: set1_1.
have qd1: cnf_degree (the_cnf x) <o n.
  by move:(the_cnf_p6 on xp lxo); rewrite /odegree (Y_false (nesym (proj2 xp))).
have qd: cnf_degree (the_cnf x) <o oexp A \0c.
   by rewrite /A/oexp LgV//; aw.
have qe:  (\0c = \0c \/ oexp A (cpred \0c) <o cnf_degree (the_cnf x)) by left.
move: (CNF_sum_pr1 cA qa qc qd qe); rewrite eqA2 qb; move ->.
have ->: (cnf_ns A \0c) = A. 
  rewrite /cnf_ns/cnf_s /A Lgd (cdiff_n0 NS1); apply: Lg_exten.
  move => i i1 /=; rewrite LgV//(csum0r) //; move/set1_P: i1 => ->; fprops.
have qa1 := proj1 qa.
have qf1 i:i <c domain (the_cnf x) -> oexp (the_cnf x) i <=o cnf_degree (the_cnf x).
   move: (cnf_size_nz qa) => [ra rb] idx.
  have nN:= proj42 qa1.
  apply: (CNF_exponents_M nN  (proj1(proj44 qa1))).
     apply/(cltSleP ra); ue.
  by rewrite rb; apply/cltS.
have qf: cnfp (cnf_nm (the_cnf x) A).
  apply: (cnfp_cnf_nm qa1 cA) => i j; rewrite /A Lgd;move => idx /clt1 ->.
  rewrite {2}/oexp LgV//; aw; apply: (ole_ltT (qf1 _ idx)  qd1).
congr cnf_val.
rewrite eqA1; apply: (cnf_nat_sum_p3 cA (proj1 qa) qf) => e.
rewrite Vr_monomial /Vr (cnfp_cnf_nm_range qa1 cA) /A Lg_range funI_set1.
move: (cnf_range_fgraph (proj1 qa)); set R := range _ => fgr.
have qg: ~ inc n (domain R). 
  move/funI_P => [z /(range_gP (proj41 qa1)) [i idx ->]] => nv.
  have ii:  i <c (domain (the_cnf x)) by apply/(NltP (proj42 qa1)).
  by case:(oltNge qd1); rewrite nv; exact: (qf1 i ii). 
case: (equal_or_not e n) => en; Ytac0.
  by rewrite en (setU1_V_out _ fgr qg) (Vg_out_of_range qg) (Nsum0r (proj1 pa)).
case: (inc_or_not e (domain R)) => edr.
  have qh: (natp (Vg R e)). apply: (NS_Vr _ qa1).
  by rewrite (setU1_V_in _ fgr qg edr) (Nsum0l qh).
have qh: ~ inc e (domain (R +s1 J n a)) by rewrite domain_setU1 => /setU1_P; case. 
by rewrite (Vg_out_of_range edr) (Vg_out_of_range qh) (csum0r CS0).
Qed.
  
Lemma cnf_le_prop x y: cnfp x -> cnfp y -> (forall e, Vr x e <=c Vr y e) ->
   x <=f y.
Proof.
move => ox oy h.
case: (cnf_le_total ox oy) => // - [_ _ ]; case.
  by move ->; apply:cnf_leR.
by move => [e /cltNge]; case; apply: h.
Qed.


Lemma cnf_compare_nat_sum1 x y: cnfp x -> cnfp y -> x <=f x +#f y.
Proof.
move => ox oy; apply: (cnf_le_prop ox (cnfp_nat_sum ox oy))=> e.
rewrite (cnf_nat_sum_p2 ox oy);  apply: (csum_M0le _ (CS_nat (NS_Vr e ox))).
Qed.  

(* deplacer  et noter *)
Lemma Vr_in_range z m: cnfp z -> inc m (range z) -> Vr z (P m) = Q m.
Proof.  by move => ha hb; rewrite /Vr - (pr2_V (cnf_range_fgraph ha) hb). Qed.

  
Lemma cnf_compare_nat_sum2 x y: cnfp x -> cnfp y -> x +f y <=f x +#f y.
Proof.
move => ox oy.
case: (equal_or_not y \0f) => ynz.
  by rewrite ynz cnf_sum0r (cnf_nat_sum0 ox); apply: (cnf_leR ox).
move: (cnfp_nat_sum ox oy)(cnfp_sum ox oy) => os2 os1.
apply: (cnf_le_prop os1 os2) => e.
rewrite (cnf_nat_sum_p2 ox oy).
case: (inc_or_not e (cnf_exponents (x  +f y))) => h; last first.
  rewrite (Vr_oor h); apply: cle0x; fprops.
move /funI_P: h => [z zr ->].
move:(CS_nat(NS_Vr (P z) os1));  rewrite (Vr_in_range os1 zr) => ov.
case /(cnf_sum_rangeP ox (conj oy ynz)): zr.
- by move => [qa _]; rewrite (Vr_in_range oy qa); apply:csum_Mle0.
- by move => [qa _]; rewrite (Vr_in_range ox qa); apply:csum_M0le.
- move => ->; aw; apply:cleR; fprops.
Qed.
 

Lemma cnf_compare_nat_sum3 x y: cnfp_nz x -> cnfp_nz y ->
  cnf_degree y <=o oexp x \0c ->  x +f y = x +#f y.
Proof.
move => xp yp mt1.
move: (proj1 xp) (proj1 yp) => ox oy.
move: (cnfp_nat_sum ox oy)(cnfp_sum ox oy) => os2 os1.
apply: (cnf_nat_sum_p3 ox oy os1) => e.
set Ha := (cnf_sum_rangeP ox yp).
case: (inc_or_not e (cnf_exponents x)) => eex.
  move: (CS_nat(NS_Vr e ox)).
  move/funI_P:eex =>[m mr ->].
  move/(range_gP (proj41 ox)):(mr) => [i idx iv].
  move/(NltP (proj42 ox)): idx => ilx.
  move: (cle0x (proj31_1 ilx)) => ip.
  move: (CNF_exponents_M (proj42 ox) (proj1(proj44 ox)) ip ilx) => la.
  move: (oleT mt1 la); case /ole_eqVlt => lv.
     have: inc  (J (P m)  (Vr x (P m) +c Vr y (P m))) (range (x +f y)).        
       by apply/Ha; constructor 3; rewrite iv lv. 
    by move/(Vr_in_range os1); aw.
  have: inc (Vg x i)  (range (x +f y)).
     by apply/Ha; constructor 2; rewrite -{1} iv.
  rewrite (Vr_in_range ox mr) iv; move/(Vr_in_range os1) => -> cc.
  case: (inc_or_not (oexp x i) (cnf_exponents y)). 
    move/funI_P => [mm /(range_gP (proj41 oy)) [j jdy jv] mmv].
    by case: (proj2 (ole_ltT (cnf_degree_greatest oy jdy) lv)); rewrite mmv jv.
  by move/Vr_oor => ->; by rewrite  (csum0r cc). 
move: (cnf_size_nz yp) => [nN nv].
have he: inc (cnf_size y) (domain y) by rewrite nv; apply: Nsucc_i.
have hc: inc (Vg y (cnf_size y)) (range y).
  by apply/(range_gP (proj41 oy)); ex_tac.
case: (inc_or_not e (cnf_exponents y)) => eey.
  move/funI_P:eey =>[m mr -mv].
  move/(range_gP (proj41 oy)):(mr) => [i idy iv].
  move/(NltP (proj42 oy)): (idy); rewrite nv => /(cltSleP nN).
  case /(cle_eqVlt) => isy.
    have: inc (J e ((Vr x e) +c Vr y e)) (range (x +f y)).        
      by apply/Ha; constructor 3; rewrite mv iv isy.
    by move/(Vr_in_range os1); aw.
  move: (cnf_degree_greatest_bis oy isy) => l1.
  have mr1 : (inc m (range (x +f y))).
    by apply/Ha;constructor 1; split => //; rewrite iv.
  rewrite (Vr_oor  eex) (csum0l (CS_nat(NS_Vr e oy))).
  by rewrite mv (Vr_in_range os1 mr1) (Vr_in_range oy mr).
rewrite (Vr_oor  eex) (Vr_oor eey) (csum0l CS0).
case: (inc_or_not e (cnf_exponents (x +f y))) => eez; last by rewrite Vr_oor. 
move: eex eey;
move:eez => /funI_P [z /Ha ze ->]; case: ze.
- by move => [zy _]; move => _; case; apply/funI_P; ex_tac.
- by move => [zy _]; case; apply/funI_P; ex_tac.
- by move => -> _; aw; case;  apply/funI_P; ex_tac.
Qed.

Lemma cnf_compare_nat_sum4 x y: cnfp_nz x -> cnfp_nz y ->
   oexp x \0c <o cnf_degree y  ->  x +f y <f x +#f y.
Proof.
move => xnz ynz lt1;move: (proj1 xnz) (proj1 ynz) => ox oy.
split; first by apply: (cnf_compare_nat_sum2 ox oy).
move => sv.
move: (f_equal (Vr  ^~(oexp x \0c)) sv).
rewrite (cnf_nat_sum_p2 ox oy); 
move: (cnf_size_nz_ter xnz) => [qc qd].
have har: inc (Vg x \0c) (range x) by apply: (inc_V_range (proj41 ox) qc).
rewrite (Vr_in_range ox har);set e := oexp x \0c.
move/cnfpP:(ox) =>/proj43 h; move:(proj33 (h _ qc)) => [cN cp]; clear h.
move:(nesym (proj2 cp)) => cnz.
have os:= (cnfp_sum ox oy).
case: (inc_or_not e (cnf_exponents  (x +f y))).
  move/funI_P => [m md mv].
  move: (NS_Vr e os); rewrite mv (Vr_in_range os md) => qN.
  case/(cnf_sum_rangeP ox ynz): md => mv1.
  - rewrite (Vr_in_range oy (proj1 mv1)) csumC.
    by move:(proj2 (csum_M0lt qN cnz)).
  - case: (proj2(olt_ltT lt1 (proj2 mv1))).
    by rewrite - (proj2(cnf_range_fgraph ox) _ _  har (proj1 mv1) mv).
  - by case: (proj2 lt1); rewrite - /e mv mv1; aw.
move/Vr_oor => -> /esym /csum_nz; case => cz; by case:cp.
Qed.


Lemma cnf_compare_nat_sum5 x y z: cnfp x -> cnfp y -> cnfp z ->
  (x +#f z <=f y +#f z <->  x <=f y).                         
Proof.
move => ox oy oz.
have H: forall a b, a <f b -> a +#f z <f b +#f z.
  clear x y ox oy => a b [[oa ob etc] nab]; case: etc => // - [e ea eb].
  apply/(cnf_lt_prop (cnfp_nat_sum oa oz)(cnfp_nat_sum ob oz)).
  exists e.
   rewrite (cnf_nat_sum_p2 oa oz) (cnf_nat_sum_p2 ob oz).
   exact: (csum_Mlteq (NS_Vr e oz) ea).
  by move => e' h; rewrite (cnf_nat_sum_p2 oa oz) (cnf_nat_sum_p2 ob oz) eb.
have tv:  x +#f z <=f x +#f z by apply: (cnf_leR (cnfp_nat_sum ox oz)).
case: (cnf_le_total ox oy) => lxy; split.
- exact.
- move => _; case: (equal_or_not x y) => exy; first  by rewrite - exy. 
  exact: (proj1 (H _ _ (conj lxy exy))).
- move => l1;  case: (equal_or_not y x) => exy; first by move: lxy; rewrite exy.
  by move: (H _ _ (conj lxy exy)) => [ra]; case; apply: (cnf_leA).
-  by move =>h; rewrite (cnf_leA lxy h). 
Qed.

Lemma ord_compare_nat_sum1 x y: ordinalp x -> ordinalp y -> x <=o x +#o y.
Proof.
move => ox oy.
move: (the_cnf_p0 ox) (the_cnf_p0 oy) => [oa av] [ob bv].
rewrite /natural_sum - {1} av.
apply/(cnf_le_compat oa (cnfp_nat_sum oa ob)).
by  apply:cnf_compare_nat_sum1.
Qed.  


Lemma ord_compare_nat_sum2 x y: ordinalp x -> ordinalp y -> x +o y <=o x +#o y.
Proof.
move => ox oy.
move: (the_cnf_p0 ox) (the_cnf_p0 oy) => [oa av] [ob bv].
move: (the_cnf_p0 (OS_sum2 ox oy)) => [ixy].
rewrite /natural_sum (cnf_osum ox oy) => <-.
apply/(cnf_le_compat (cnfp_sum oa ob)  (cnfp_nat_sum oa ob)).
apply:(cnf_compare_nat_sum2 oa ob).
Qed.
 

Lemma ord_compare_nat_sum3 x y: \0o <o x -> \0o <o y ->
  odegree y <=o ovaluation x ->  x +o y = x +#o y.
Proof.
move => xp yp.
move: (the_cnf_p0_nz xp) (the_cnf_p0_nz yp) => [oa av] [ob bv].
rewrite /ovaluation/odegree (Y_false (nesym (proj2  yp))) => h.
rewrite /natural_sum -  (cnf_compare_nat_sum3 oa ob h).
move: (proj32_1 xp) (proj32_1 yp) => ox oy.
by rewrite  -(cnf_osum ox oy)  (proj2 (the_cnf_p0 (OS_sum2 ox oy))).
Qed.

Lemma ord_compare_nat_sum4 x y: \0o <o x -> \0o <o y ->
  ovaluation x <o odegree y  ->  x +o y <o x +#o y.
Proof.
move => xp yp hyp.
move: (proj32_1 xp) (proj32_1 yp) => ox oy.
split; first by apply:ord_compare_nat_sum2.
move: hyp.
rewrite /ovaluation/odegree (Y_false (nesym (proj2  yp))) => h.
move: (the_cnf_p0_nz xp) (the_cnf_p0_nz yp) => [oa av] [ob bv].
move: (proj2(cnf_compare_nat_sum4 oa ob h)).
rewrite /natural_sum -(cnf_osum ox oy) => u v; case: u.
move: (the_cnf_p0 (OS_sum2 ox oy)) => [qa qb].
apply: (cnf_val_inj qa (cnfp_nat_sum (proj1 oa) (proj1 ob))).
by rewrite qb.
Qed.

Lemma ord_compare_nat_sum5 x y z: ordinalp x -> ordinalp y -> ordinalp z ->
  (x +#o z <=o y +#o z <->  x <=o y).                         
Proof.
move => ox oy oz.
move: (the_cnf_p0 ox) (the_cnf_p0 oy) => [oa av] [ob bv].
move: (the_cnf_p0 oz) => [oc cv].
move: (cnf_le_compat oa ob); rewrite av bv => H1; apply: iff_trans H1.
rewrite /natural_sum.
move: (cnf_le_compat (cnfp_nat_sum oa oc) (cnfp_nat_sum ob oc)) => H2.
by apply: (iff_trans (iff_sym H2)); apply: cnf_compare_nat_sum5.
Qed.



Lemma natural_small x y e (v := oopow e):
  ordinalp e -> x <o v -> y <o v ->  (x +#o y) <o v.
Proof.
move => oe qa qb.
have ox:= proj31_1 qa.
have oy:= proj31_1 qb.
case: (ozero_dichot ox); first by move ->; rewrite natural_sumC natural_sum0.
case: (ozero_dichot oy); first by move ->; rewrite natural_sum0.
move => yp xp.
move: (the_cnf_p6 oe xp qa)  (the_cnf_p6 oe yp qb).
rewrite /odegree  (Y_false (nesym (proj2 xp))) (Y_false (nesym (proj2 yp))).
move => dx dy.
move: (olt_leT xp (ord_compare_nat_sum1 ox oy)) => zp.
suff: odegree (x +#o y)  <o e.
   move/oleSltP => /opow_Mo_le; apply: olt_leT.
   exact: (proj2 (the_cnf_p4 zp)).
move: (proj1 (the_cnf_p0_nz zp)).
rewrite /odegree (Y_false (nesym (proj2 zp))) /natural_sum.
move: (the_cnf_p0 ox)(the_cnf_p0 oy) =>[oa av][ob bv].
rewrite (proj43 (cnf_and_val_pb (cnfp_nat_sum oa ob))).
set s :=  (the_cnf x +#f the_cnf y) => sp.
have : inc (cnf_degree s) (cnf_exponents s).
  apply/funI_P; exists (Vg s (cnf_size s)) => //.
  by apply: (inc_V_range (proj41 (proj1 sp)) (cnf_size_nz_bis sp) ).
rewrite (cnf_nat_sum_p1 oa ob); case/setU2_P => /funI_P [t  tr ->].
  move/(range_gP (proj41 oa)): tr => [i idx ->].
  exact: (ole_ltT (cnf_degree_greatest oa idx) dx).
move/(range_gP (proj41 ob)): tr => [i idx ->].
exact: (ole_ltT (cnf_degree_greatest ob idx) dy).
Qed.

Lemma cnf_coefficients_monotone x y:
  cnfp x -> cnfp y ->  (forall e, Vr x e <=c Vr y e) ->
   cnf_val x <=o cnf_val y.
Proof.
move => ox oy hyp.
case: (cnf_le_total ox oy).
  by move /(cnf_le_compat ox oy).
move => [_ _]; case.
  move ->; apply: (oleR (OS_cnf_val ox)).
move => [e /cltNge]; case; apply: hyp.
Qed.

Definition cnf_subset E c :=
  fun_image (Zo (\Po (E \times (csucc c))) cnf_rangep) cnf_sort.

Definition cnf_subset1 x :=
  cnf_subset (cnf_exponents x) (\csup (range (range x))).


(* Noter et utiliser *)
Lemma finite_Zo E p: finite_set E -> finite_set (Zo E p).
Proof. by apply: sub_finite_set; apply :Zo_S. Qed.

  (* Noter et utiliser *)
Lemma setP_finite E : finite_set E -> finite_set (\Po E).
Proof.
move => /NatP h.
rewrite /finite_set card_setP; apply/NatP; rewrite - cpowcr; fprops.
Qed.

Lemma cnf_subset_finite E c: finite_set E -> natp c ->
  finite_set (cnf_subset E c).
Proof.
move => ha nN.
apply: finite_fun_image; apply finite_Zo;  apply: setP_finite.
apply (finite_prod2 ha). apply/NatP; rewrite (card_card); fprops.
Qed.

Lemma  cnf_subset_prop E c x: finite_set E -> natp c ->
   inc x (cnf_subset E c) ->
   [/\ cnfp x, sub (cnf_exponents x) E & forall e, Vr x e <=c c].
Proof.
move => rF cN /funI_P [z /Zo_P [/setP_P qa qb] xv ].
move: (cnf_sort_correct qb); rewrite - xv; move =>[qc qd]; split.
- exact.
- by rewrite /cnf_exponents qd => t/funI_P [k /qa /setX_P [_ h _] -> ].
- move => e; case: (inc_or_not e (cnf_exponents x)) => eE.
    move: eE => /funI_P [k ka ->]; rewrite (Vr_in_range qc ka).   
    by move: ka; rewrite /cnf_exponents qd => /qa /setX_P [_ _ q];apply /NleP.
  by rewrite (Vr_oor eE);apply: cle0n.
Qed. 

Lemma cnf_subset_sum_prop x y (F :=  (cnf_subset1 (x +#f y))):
  cnfp x -> cnfp y -> (inc x F /\ finite_set F).
Proof.
move => ox oy. 
move: (cnfp_nat_sum ox oy) => oz.
move: (proj1(cnf_exponents_of oz)).
rewrite /F/cnf_subset1; set E := cnf_exponents _ => fsE.
set K := range _; set c := \csup K.
have fr z: cnfp z -> finite_set (range z). 
  move => h; apply: (finite_range (proj41 h)).
  apply: (finite_set_nat (proj42 h)).
have nsk: forall t, inc t K -> natp t.
  move => t/funI_P [u /(range_gP (proj41 oz)) [o idz ->] ->].
  by move/cnfpP: oz => /proj43 h; move:(proj1 (proj33(h _ idz))).
have csK: cardinal_set K by move => t/nsk/CS_nat.
have cN: natp c.
  case: (emptyset_dichot K) => kne; first by rewrite /c kne setU_0; apply: NS0.
  have osK: ordinal_set K by move => t/nsk/OS_nat.
  have fsK: finite_set K by apply: finite_fun_image; apply: fr.
  move:(finite_subset_ord fsK kne osK) => [n nK nv].
  have nN: natp n by apply: nsk.
  suff: n = c  by move <-.
  apply: (cleA (card_sup_ub csK nK)).
  apply: (card_ub_sup (CS_nat nN)) => t tk.
  by apply: (ocle3 (csK _ tk)  (csK _ nK) (nv _ tk)).
split; last by apply: (cnf_subset_finite fsE cN). 
have aux: cnf_rangep (range x). 
  split; [ exact: (fr _ ox) | exact: (cnf_range_fgraph ox) | ].
  move => t /(range_gP (proj41 ox)) [i idx ->].
  by move/cnfpP: ox => /proj43; apply.
move: (cnf_sort_correct aux) =>[qa qb].
move: (cnf_same_range qa ox qb) => xsr.
apply/funI_P; exists (range x) => //;apply/Zo_P; split => //; apply/setP_P.
move => t tr; move: (tr) => /(range_gP (proj41 ox)) [i idx tv].
have exE: inc (oexp x i) E.
  rewrite/E (cnf_nat_sum_p1 ox oy); apply: setU2_1.
  by apply/funI_P; ex_tac; rewrite tv.
have le1: ocoef x i <=c Vr (x +#f y) (oexp x i).
  rewrite (cnf_nat_sum_p2 ox oy (oexp x i)) - (Vr_correct ox idx).
  apply: (csum_M0le _ (CS_nat (NS_Vr (oexp x i) ox))).
rewrite tv - (proj43 ox _ idx); apply: (setXp_i exE).
apply/(NleP cN) /(cleT le1); apply: (card_sup_ub csK).
move/funI_P:  exE =>[z  zr ->];rewrite (Vr_in_range oz zr).
by apply/funI_P; ex_tac.
Qed.

  
Lemma natural_finite_cover x e (E:= oopow e):
  ordinalp e -> inc x E ->
  let n := cardinal (Zo (coarse E) (fun z => (P z) +#o (Q z) = x)) in
  natp n /\ n <> \0c.
Proof.
move=> oe xE; set F := Zo _ _ => n.
have oE :=(OS_pow OS_omega oe).
have ox:= (Os_ordinal oE xE). 
move: (the_cnf_p0 ox) =>[ou uv].
move: (proj2 (cnf_subset_sum_prop  ou cnfp0)); rewrite (cnf_nat_sum0 ou).
set G1:= (cnf_subset1 _) => h0.
set G := fun_image G1 cnf_val.
have h1: finite_set G by apply /finite_fun_image.
move: (finite_prod2 h1 h1) => h2.
have h3: sub F (G \times G).
  move => t /Zo_P [/setX_P [pt Pt Qt]].
  move: (Os_ordinal oE Pt)  (Os_ordinal oE Qt) => op oq.
  move: (the_cnf_p0 op)(the_cnf_p0 oq) =>[oa av][ob bv].
  rewrite /natural_sum - uv; move/(cnf_val_inj (cnfp_nat_sum oa ob) ou) => s.
  move: (proj1(cnf_subset_sum_prop oa ob)); rewrite s => sa.
  move: (proj1(cnf_subset_sum_prop ob oa)); rewrite cnf_nat_sumC s => sb.
  by rewrite - pt -av - bv; apply: setXp_i; apply: funI_i.
split; first by move: (sub_finite_set h3 h2) => /card_finite_setP.
apply: card_nonempty1.
have zE: inc \0o E by  apply /(oltP oE); apply:(oopow_pos oe). 
exists (J x \0o); apply: Zo_i;first by apply :setXp_i.
by rewrite pr1_pair pr2_pair  natural_sum0.
Qed.


(*  Double induction *)


Definition doubleI_E a b :=
  (singleton a \times b) \cup (a \times singleton b) \cup (a\times b).
Definition doubleI_F a b :=
  (singleton a \times b) \cup (a \times singleton b).

Lemma doubleI_E_pair a b x: inc x (doubleI_E a b) -> pairp x.
Proof.  case/setU2_P; first case/setU2_P; apply:setX_pair. Qed.

Lemma doubleI_E_P1 a b: ordinalp a -> ordinalp b ->
  forall x y, inc (J x y)  (doubleI_E a b) <->
     [\/ x = a /\ y <o b, x <o a /\ y = b | x <o a /\ y <o b].
Proof.
move => oa ob x y; split.
  case/setU2_P; first case/setU2_P.
  - by move/setXp_P => [/set1_P -> /(oltP ob) lyb]; constructor 1.
  - by move/setXp_P => [/(oltP oa) lxa /set1_P -> ]; constructor 2.
  - by move/setXp_P => [/(oltP oa) lxa /(oltP ob) lyb ]; constructor 3.
case => - [pa pb]; apply/setU2_P.
- rewrite pa;left; apply/setU2_P; left; apply:setXp_i; fprops.
  by apply/(oltP ob).
- rewrite pb;left; apply/setU2_P; right; apply:setXp_i; fprops.
   by apply/(oltP oa).
- by right; apply:setXp_i; [ apply/(oltP oa) | apply/(oltP ob) ].
Qed.
   
Lemma doubleI_E_P2 a b: ordinalp a -> ordinalp b ->
  forall x y, inc (J x y)  (doubleI_E a b) <->
     [/\ x <=o a, y <=o b & (x <> a \/ y <> b)].                                Proof.
move => oa ob x y.
apply:(iff_trans (doubleI_E_P1 oa ob x y)); split.
  case.
  - move => [-> [leyb ynb]]; split;fprops.
  - move => [[lexa xna] ->]; split;fprops.
  - move => [ [lexa xna] [leyb ynb]]; split;fprops.
move => [/ole_eqVlt eq1 /ole_eqVlt eq2 eq3].
case: eq1 => xa.
  constructor 1; case: eq2 => yb; [by case: eq3 | done].
by case: eq2 => yb; [constructor 2 | constructor 3].
Qed.

Lemma doubleI_E_sub A B a b:
  ordinalp A -> ordinalp B -> inc a A -> inc b B ->
  sub (doubleI_E a b) (A \times B).
Proof.
move => oA oB /(oltP oA) laA /(oltP oB) lbB.
move => t tE.
have tp:=(doubleI_E_pair tE).
move: tE; rewrite - tp => /(doubleI_E_P2 (proj31_1 laA)(proj31_1 lbB)).
move => [ha hb _]; apply:setXp_i.
  apply/(oltP oA); exact:(ole_ltT ha laA).
  apply/(oltP oB); exact:(ole_ltT hb lbB).
Qed.

Definition otrans_def a (T: fterm) f :=
  [/\ surjection f, source f = a &
                    forall x, x <o a ->  Vf f x = T (restriction1 f x)].
Definition otrans_defined a := transfinite_defined (ordinal_o a).

Lemma otrans_def_prop a T f: ordinalp a ->
  (otrans_def a T f  <-> transfinite_def (ordinal_o a) T f).
Proof.
move => oa; rewrite / otrans_def /transfinite_def.
rewrite ordinal_o_sr; split; move =>[ha hb hc]; split => // x xa.
  by rewrite (ordinal_segment oa xa); apply: hc; apply/(oltP oa).
by move/(oltP oa): (xa) => ixa; rewrite (hc _ ixa) (ordinal_segment oa ixa).
Qed.


Lemma otrans_pr a f T:
   ordinalp a -> otrans_def a T f -> otrans_defined a T = f. 
Proof.
move => ox H.
move:(ordinal_o_wor ox) => wo .
by apply:(transfinite_pr wo); move/(otrans_def_prop _ _ ox):H.
Qed.


Lemma otrans_defined_pr a T: ordinalp a ->
  otrans_def a T ( otrans_defined a T).
Proof.
move => ox; apply/(otrans_def_prop _ _ ox).
apply: (transfinite_defined_pr _ (ordinal_o_wor ox)).
Qed.


Definition Lfs (f: fterm) s := Lf f s (fun_image s f).

Lemma Lfs_surjective f s: surjection (Lfs f s).
Proof.
apply:lf_surjective; first by move => t ts; apply:funI_i.
by move => y /funI_P.
Qed.

Lemma Lfs_V f s x : inc x s -> Vf (Lfs f s) x = f x.
Proof. by rewrite /Lfs => xs; rewrite LfV// => t tE; apply:funI_i. Qed.

Lemma Lfs_source f s :source (Lfs f s) = s.
Proof. by rewrite /Lfs; aw.  Qed.

Lemma Lfs_restriction1 f x: function f -> sub x (source f) ->
   restriction1 f x = Lfs (Vf f) x.
Proof.
move => ha hb; apply:function_exten4.
- by rewrite Lfs_source /restriction1; aw.
- apply: (restriction1_fs ha hb).
- apply:Lfs_surjective.
- rewrite{1}/restriction1; aw => t tx; rewrite (restriction1_V ha hb tx).
  by rewrite Lfs_V.
Qed.

Lemma Lfs_exten f1 f2 x: (forall t, inc t x -> f1 t = f2 t) ->
   Lfs f1 x  = Lfs f2 x.
Proof.
move => eq; apply: function_exten4.
- by rewrite !Lfs_source.
- apply:Lfs_surjective.
- apply:Lfs_surjective.
- by rewrite Lfs_source => t tx; rewrite !Lfs_V // eq.
Qed.


Definition fterm3 := Set -> Set -> Set -> Set.
Notation "f =2o g" := (forall x y, ordinalp x -> ordinalp y -> f x  y = g x y)
  (at level 70, format "'[hv' f '/ '  =2o  g ']'", no associativity).

Definition doubleI_restr (f:fterm2) a b :=
  Lfs (fun p => f (P p) (Q p)) (doubleI_E a b).
Definition doubleI_fix1 (T: fterm3) (f:fterm2) :=
  f =2o fun a b => T a b (doubleI_restr f a b).


Definition doubleI_def A B (T: fterm2) f :=
  [/\ surjection f,  source f = A \times B &
   forall p, inc p (A\times B) ->
             Vf f p = T p (restriction1 f (doubleI_E (P p) (Q p)))].


Lemma doubleI_unique A B T f1 f2: ordinalp A -> ordinalp B ->
  doubleI_def A B T f1 ->  doubleI_def A B T f2 ->
  f1 = f2.
Proof.                                
move => oA oB [f1a f1b f1c] [f2a f2b f2c].
apply: function_exten4 => //; first ue.
set U := Zo A (fun a => forall b, inc b B -> Vf f1 (J a b) = Vf f2 (J a b)). 
suff UA: U = A.
  hnf; rewrite f1b => p /setX_P [pp pa pb]; rewrite - pp. 
  by move: pa; rewrite - UA => /Zo_P [pa pc]; apply: pc.
apply: extensionality; first by apply: Zo_S.
move => t tA; ex_middle tU.
move: (least_ordinal3 (Os_ordinal oA tA) tU (p := fun z => inc z U)).
set y := least_ordinal _ _; move=> [oy ynU ym].
case: (oleT_el oA oy) => cAy.
  by apply: ym; apply:olt_leT cAy; apply/(oltP oA).
have yA: inc y A  by apply/(oltP oA).
case: ynU; apply/Zo_P; split; first exact.
set V := Zo B (fun b => Vf f1 (J y b) = Vf f2 (J y b)).
move => b bB; case: (inc_or_not b V); first by case /Zo_P.
move => nbV.
move: (least_ordinal3 (Os_ordinal oB bB) nbV (p := fun z => inc z V)).
set z := least_ordinal _ _; move=> [oz znV zm].
case: (oleT_el oB oz) => cBz.
  by case: nbV; apply: zm; apply:olt_leT cBz; apply/(oltP oB).
have zB: inc z B by apply/(oltP oB).
have pab:inc (J y z) (A \times B) by apply: setXp_i.
case: znV; apply/Zo_P; split => //.
rewrite (f1c _ pab) (f2c _ pab); congr T; aw.
set E := doubleI_E y z.
have sx1: sub E (source f1) by rewrite f1b; apply:doubleI_E_sub. 
have sx2: sub E (source f2) by rewrite f2b - f1b.
move: (restriction1_fs (proj1 f1a) sx1) (restriction1_fs (proj1 f2a) sx2).
move => sj1 sj2.
apply: function_exten4 => //; first by rewrite/restriction1; aw.
rewrite {1}/restriction1; aw; move => x xE /=.
rewrite (restriction1_V (proj1 f1a) sx1 xE) (restriction1_V (proj1 f2a) sx2 xE).
case/setU2_P: xE.
  case/setU2_P.
    move => /setX_P [pp /set1_P px qx]; rewrite - pp px.
    have: inc (Q x) V by apply: zm; apply/(oltP oz).
    by move/Zo_P =>[_].
  move => /setX_P [pp px /set1_P qx].   
  have: inc (P x) U by apply: ym; apply/(oltP oy).
  move/Zo_P => [pa pb]; rewrite - pp; apply: pb; apply/(oltP oB).
  by rewrite qx.
move => /setX_P[px xy xz].
have: inc (P x) U by apply: ym; apply/(oltP oy).
move/Zo_P => [pa pb]; rewrite - px; apply: pb; apply/(oltP oB).
by apply: olt_ltT cBz; apply/(oltP oz).
Qed.

Definition doubleI_transdef A B (T: fterm2) :=
  let T1 a f g x y := Yo (x <o a) (Vf (Vf f x) y) (Vf g y) in
  let T2 a f g p := T1 a f g (P p) (Q p) in
  let T4 a b f g := Lfs (T2 a f g) (doubleI_E a b) in
  let T5 fa fb := T (J (source fa) (source fb))
                    (T4 (source fa) (source fb) fa fb) in
  let T6 fa := otrans_defined B (T5 fa) in
  let f := otrans_defined A T6 in
  Lfs (fun p => Vf (Vf f (P p)) (Q p)) (A\times B).


Lemma doubleI_correct A B T : ordinalp A -> ordinalp B ->
  doubleI_def A B T  (doubleI_transdef A B T).
Proof.
move => oA oB.
split; [ apply:Lfs_surjective | by rewrite Lfs_source | ].
move=> p pt; rewrite  (Lfs_V _ pt).
move/setX_P: (pt) => [pp pxA pyB]; set a := P p;  set b := Q p.
move/(oltP oA):(pxA); rewrite -/a => lxA.
move/(oltP oB):(pyB); rewrite -/b => lyB.
set T6 := fun fa:Set => _.
move:(otrans_defined_pr T6 oA) => [sjf sf fv]; rewrite (fv _ lxA).
rewrite {1} /T6; set T5 := fun fb: Set => _.
move:(otrans_defined_pr T5 oB) =>[ha hb hc].
have Sr u v: source (restriction1 u v) = v by rewrite /restriction1; aw.
rewrite (hc b lyB) /T5 -/(T6 _) Sr Sr pp; congr (T p).
set g := (doubleI_transdef A B T).
have adm:sub (doubleI_E a b) (A \times B) by apply:doubleI_E_sub.
have hd: sub (doubleI_E a b) (source g) by rewrite Lfs_source.
have ssg: surjection g by apply: Lfs_surjective.
rewrite (Lfs_restriction1 (proj1 ssg) hd); apply:Lfs_exten => q qE.
rewrite (Lfs_V _ (adm _ qE)) -/T6.
move: (proj1 sjf) => ff.
move: (proj31_1 lxA) (proj31_1 lyB) => oa ob.
move: (proj33 (proj1 lxA)); rewrite - {1} sf => sas.
move: (proj33 (proj1 lyB)); rewrite - {1} hb => sbs.
move: (doubleI_E_pair qE) => pq; rewrite - pq in qE.
case /(doubleI_E_P1 oa ob):qE.
- move => [h1 h2]; move/(oltP ob):(h2) => h3.
  have nf: ~ P q <o a by case.
  by rewrite (Y_false nf) (restriction1_V (proj1 ha) sbs h3) h1 (fv a lxA).
- by move => [h1 h2]; move/(oltP oa):(h1) => h3; Ytac0; rewrite restriction1_V.
- by move =>[h1 h2]; move/(oltP oa):(h1) => h3; Ytac0; rewrite restriction1_V.
Qed.


Lemma doubleI_unique2 T A1 A2 B1 B2 f: A1 <=o A2 -> B1 <=o B2 ->
  doubleI_def A2 B2 T f -> 
  doubleI_def A1 B1 T (restriction1 f (A1 \times B1)).
Proof.
move => le1 le2 [ha hb hc].
have sp1: sub (A1 \times B1) (A2 \times B2).
  apply: setX_Slr; [ exact (proj33 le1) | exact (proj33 le2)].
have sp2:sub (A1 \times B1) (source f) by ue.
have rs1 :=(restriction1_fs (proj1 ha) sp2).
split.
    exact.
  by rewrite /restriction1; aw.
move => p pAB.
rewrite (restriction1_V (proj1 ha) sp2 pAB).
rewrite (hc _ (sp1 _ pAB));congr T.
have sp3: sub (doubleI_E (P p) (Q p))  (A1 \times B1). 
  move/setX_P: pAB => [_ pa qbØ].
  by apply: (doubleI_E_sub (proj31 le1) (proj31 le2)).
have sp4:= sub_trans sp3 sp2.
rewrite (Lfs_restriction1 (proj1 ha) (sub_trans sp3 sp2)).
rewrite (Lfs_restriction1 (proj1 rs1)); last by rewrite /restriction1; aw.
by apply:Lfs_exten => t ts; rewrite (restriction1_V (proj1 ha) sp2 (sp3 _ ts)).
Qed.


Lemma doubleI_unique3 T A1 A2 B1 B2 f g: A1 <=o A2 -> B1 <=o B2 ->
  doubleI_def A2 B2 T f -> doubleI_def A1 B1 T g -> 
  g = (restriction1 f (A1 \times B1)).
Proof.
move => ha hb hc hd.
exact: (doubleI_unique (proj31 ha) (proj31 hb) hd (doubleI_unique2 ha hb hc)).
Qed.

Definition doubleI_tdef (T: fterm3) a b :=
  let T' := fun p f => T (P p) (Q p) f in
  Vf (doubleI_transdef (osucc a) (osucc b) T') (J a b).


Lemma doubleI_tdef_rec T: doubleI_fix1 T (doubleI_tdef T).
Proof.
move => a b oa ob.
move:(OS_succ oa) (OS_succ ob) => h1 h2.
pose T' := (fun p f => T (P p) (Q p) f).
move:(doubleI_correct T' h1 h2)=>h; move:(h) => [/proj1 ha hb hc]. 
set E := (osucc a \times osucc b).
have H: forall p, inc p E ->
   doubleI_tdef T (P p) (Q p) = Vf (doubleI_transdef (osucc a) (osucc b) T') p. 
  move => p /setX_P[ pp /(oltP h1) /oleSltP ua /(oltP h2) /oleSltP vb].
  move:(doubleI_correct T' (proj31 ua) (proj31 vb)) => h'.
  rewrite  /doubleI_tdef (doubleI_unique3 ua vb h h') restriction1_V // ? pp //.
  rewrite hb; apply/setX_Slr; [ exact (proj33 ua) | exact (proj33 vb)].
  rewrite -{1} pp;apply:setXp_i; fprops. 
have h5:inc (J a b) E by apply:setXp_i; fprops.
have h6: sub (doubleI_E a b) E by  apply:doubleI_E_sub; fprops.
rewrite  -{1} (pr2_pair a b) -{1} (pr1_pair a b)  (H _ h5) (hc _ h5) /T'; aw.
rewrite (Lfs_restriction1 ha); try ue;congr T.
by apply:Lfs_exten => p /h6 pe; rewrite (H _ pe).
Qed.




Lemma doubleI_tdef_unique T f g :
  doubleI_fix1 T f ->  doubleI_fix1 T g -> f =2o  g.
Proof.
move =>  fp gp a b oa ob.
set A := osucc a; set B := osucc b.
set AB:= A \times B.
have abAB: inc (J a b) AB. apply:setXp_i; rewrite /A/B; fprops.
pose fv p := f (P p) (Q p); pose gv p := g (P p) (Q p); 
set F :=  Lfs fv AB; set G :=  Lfs gv AB.
have ->: f a b = Vf F (J a b) by rewrite /F (Lfs_V _ abAB) /fv;aw.
have ->: g a b = Vf G (J a b) by rewrite /G (Lfs_V _ abAB) /gv;aw.
suff: F = G by move ->.
have oA: ordinalp A by apply:OS_succ.
have oB: ordinalp B by apply:OS_succ.
have aux h:  doubleI_fix1 T h -> 
 doubleI_def A B (fun p => T (P p) (Q p)) (Lfs (fun p => h (P p) (Q p)) AB).
  move => hp.
  split; [ apply:Lfs_surjective | by rewrite Lfs_source | move => p pAB].
  move/setX_P:(pAB) => [pp pxa pxb].
  move:(Os_ordinal oA pxa) (Os_ordinal oB pxb) => op oq.
  rewrite (Lfs_V _ pAB) (hp _ _ op oq); congr T.
  move:(doubleI_E_sub oA oB pxa pxb) => ss.
  rewrite Lfs_restriction1 ?Lfs_source //.
     apply: Lfs_exten => t tE //;rewrite Lfs_V; fprops.
  apply:surj_function; apply:Lfs_surjective.
exact: (doubleI_unique oA oB (aux _ fp) (aux _ gp)).
Qed.

Definition doubleI_restr2 (f:fterm2) a b :=
  Lfs  (fun p => f (P p) (Q p)) (doubleI_F a b).

Definition doubleI_tdef2 (T: fterm3) :=
  doubleI_tdef (fun a b F => T a b (restriction1 F (doubleI_F a b))).


Definition doubleI_fix2 (T: fterm3) (f:fterm2) :=
  f =2o fun a b =>  T a b (doubleI_restr2 f a b).


Lemma  doubleI_tdef_rec2 T: doubleI_fix2 T  (doubleI_tdef2 T). 
Proof.
move => a b oa ob.
rewrite /doubleI_tdef2 (doubleI_tdef_rec _ oa ob);congr T.
set f := doubleI_restr _ _ _.
have sjf: surjection f by apply:Lfs_surjective.
have sEF: sub (doubleI_F a b) (doubleI_E a b).
  by move => t tf; apply/setU2_P; left.
have ss: sub (doubleI_F a b) (source f) by rewrite Lfs_source.
rewrite (Lfs_restriction1 (proj1 sjf) ss).
by apply: Lfs_exten => t tF; rewrite (Lfs_V _ (sEF _ tF)).
Qed.


Lemma  doubleI_tdef2_unique T f g :
  doubleI_fix2 T f ->  doubleI_fix2 T g -> f =2o g.
Proof.
move =>  fp gp.
have H a b h: ordinalp a -> ordinalp b ->
  (doubleI_restr2 h a b) = restriction1 (doubleI_restr h a b) (doubleI_F a b).
  move => oa ob.
  have ss: sub  (doubleI_F a b)  (doubleI_E a b).
    by move => t tF; apply/setU2_P; left.
  have [ff _]: surjection (doubleI_restr h a b) by apply: Lfs_surjective.
  rewrite (Lfs_restriction1 ff); last by rewrite Lfs_source.
  by apply: Lfs_exten => t tE; rewrite (Lfs_V _ (ss _ tE)).
pose T' a b h := T a b (restriction1 h (doubleI_F a b)) .
apply:(doubleI_tdef_unique (T := T')) => a b oa ob.
   by rewrite (fp _ _ oa ob) (H _ _ _ oa ob) /T'.
by rewrite (gp _ _ oa ob) (H _ _ _ oa ob).
Qed.



Definition osups X:= let x := \osup X in Yo (inc x X) (osucc x) x.

Lemma OS_sups X: ordinal_set X -> ordinalp (osups X).
Proof.
move /OS_sup => ox; rewrite /osups; Ytac h => //; fprops.
Qed.

Lemma osup_ub X x: ordinal_set X -> inc x X ->  x <o osups X.
Proof.
move => ha hb.
move: (ord_sup_ub ha hb); rewrite /osups; Ytac hc; first by move/oltSleP.
by move => lex; split => // eq; case : hc; rewrite - eq.
Qed.

Lemma osups_least X x: ordinalp x -> (forall y, inc y X -> y <o x) ->
  osups X <=o x.
Proof.
move => ox ha.
rewrite /osups. Ytac h; first by  apply/oleSltP; apply: ha.
by apply:(ord_ub_sup ox) => y /ha [].
Qed.

Lemma osups_max X x: ordinalp x -> (forall y, inc y X -> y <=o x) -> inc x X ->
  osups X = osucc x.
Proof.
move => ox xp xX.
have osX: ordinal_set X by move => t /xp /proj31.
by rewrite /osups (oleA (ord_ub_sup ox xp)  (ord_sup_ub osX xX)); Ytac0.
Qed.

Lemma osups_set0: osups emptyset = \0o.
Proof. rewrite/osups setU_0; Ytac h => //; case/in_set0:h. Qed.


Lemma osups_ordinal a : ordinalp a -> osups a = a.
Proof.
move => oa; move:(ord_sup_ordinal oa); rewrite /osups.
case => ha; first by rewrite - ha (Y_false (ordinal_irreflexive oa)).
rewrite -ha Y_true // {2} ha; fprops.
Qed.

Definition is_natural_sum (f: fterm2) :=
 [/\ forall a b, ordinalp a -> ordinalp b -> ordinalp (f a b),
     forall a b, ordinalp a -> ordinalp b ->  (f a b) = f b a,
     forall a b c, ordinalp a -> ordinalp b -> ordinalp c ->
                   f a (f b c) = f (f a b) c,
     forall a, ordinalp a -> f a \0o = a &
     forall a b c, ordinalp a -> ordinalp b -> ordinalp c ->
        (f c a <=o f c b <->  a <=o b)].

Definition natural_sum_auxp (f: fterm2)  :=
  forall a b m n, a <=o b -> natp m -> natp n ->
  f ((oopow b) *o n) ((oopow a) *o m) = ((oopow b) *o n) +o ((oopow b) *o n).


Lemma is_natural_sum_nat: is_natural_sum natural_sum.
Proof.
split.
- apply: OS_natural_sum.
- move => a b _ _;apply: natural_sumC.
- apply: natural_sumA.
- apply: natural_sum0.
- move => a b c oa ob oc.  
  by rewrite  (natural_sumC c) (natural_sumC c); apply:ord_compare_nat_sum5.
Abort.

  

Section OsumS.
Let S := doubleI_tdef2 (fun _ _ f => (osups (target f))). 

Lemma nsv_prop0: S =2o fun a b => osups (target (doubleI_restr2 S a b)).
Proof. by apply:doubleI_tdef_rec2. Qed.

Definition doubleI_rg f a b :=
   fun_image a (f ^~ b) \cup fun_image b (f a). 

Lemma doubleI_rgP f a b x:
  inc x (doubleI_rg f a b) <->
     ((exists2 y, inc y b & x = f a y) \/ (exists2 y, inc y a & x = f y b)).
Proof.
split.
  case/setU2_P => /funI_P [z zab ->]; [ right; ex_tac | left; ex_tac].
by case => - [y yb ->]; apply/setU2_P; [right | left ]; apply: funI_i.
Qed.


Lemma nsv_rec: S =2o fun a b => osups (doubleI_rg S a b).
Proof.
move => a b oa ob. rewrite  {1}/S (doubleI_tdef_rec2 _ oa ob); congr osups.
rewrite /doubleI_restr2; set f := Lfs _ _.
have ha: surjection f by apply:Lfs_surjective.
have hb: source f = (doubleI_F a b) by rewrite Lfs_source.
rewrite - (surjective_pr0 ha).
set_extens t.
   move/(Imf_P (proj1 ha)) => [u uF ->]; rewrite hb in uF.
   rewrite (Lfs_V _ uF); apply/setU2_P; case/setU2_P: uF.
    by move/setX_P =>[pp /set1_P -> ub]; right;apply:funI_i.
   by move/setX_P =>[pp ua /set1_P ->]; left;apply:funI_i.
case/setU2_P=>/funI_P [z zab ->];apply /(Imf_P (proj1 ha)). 
  have h: inc (J z b) (doubleI_F a b).
    by apply/setU2_P; right; apply:setXp_i; fprops.
  by exists (J z b); [  ue | rewrite (Lfs_V _ h); aw].
have h: inc (J a z) (doubleI_F a b).
  by apply/setU2_P; left; apply:setXp_i; fprops.
by exists (J a z); [  ue | rewrite (Lfs_V _ h); aw].
Qed.

  
Lemma OS_nsv a b: ordinalp a -> ordinalp b -> ordinalp (S a b).
Proof.
move => oa; move: a oa b.
apply:least_ordinal2' => a oa ap.
apply:least_ordinal2' =>b ob bp.
rewrite (nsv_rec oa ob); apply:OS_sups => t /doubleI_rgP; case.
   by move => [y yb ->]; apply: bp.
by move => [y ya ->]; apply: ap.
Qed.

Lemma nsv_lt_prop z a b: ordinalp a -> ordinalp b -> z <o S a b ->
   (exists2 x, x <o a & z <=o S x b) \/ (exists2 x, x <o b & z <=o S a  x).
Proof.
move => oa ob; rewrite (nsv_rec oa ob); set E := doubleI_rg _ _ _ => lt.
have oz := (proj31_1 lt).
case: (p_or_not_p (exists2 x, inc x E & z <=o x)); last first.
  move => h.
  have oE: ordinal_set E.
     move=> t /setU2_P; case => /funI_P [u ux ->]; apply:OS_nsv => //.
       apply: (Os_ordinal oa ux).
       apply: (Os_ordinal ob ux).
   have zmax: (forall x, inc x E -> x <o z).
      move => x xE; case: (oleT_el oz (oE _ xE)) => // lezx; case:h; ex_tac.
  case:(oleNgt (osups_least oz zmax) lt).
move => [x /setU2_P xE le]; case: xE =>  /funI_P [u ux uv].
  left; exists u; [ by apply/(oltP oa) |  ue].
right; exists u; [ by apply/(oltP ob) |  ue].
Qed.
  
Lemma nsv_le_prop z a b: ordinalp a -> ordinalp b -> ordinalp z ->
  (forall x, x <o a -> S x b <o z) ->
  (forall x, x <o b -> S a x <o z) ->
  S a b <=o z.
Proof.
move => oa ob oz ha hb.
rewrite (nsv_rec oa ob). 
apply:(osups_least oz) => y /doubleI_rgP; case; move => [t ti ->].
  by apply: hb; apply/oltP.
by apply: ha; apply/oltP.
Qed.
  
Lemma nsvC a b: ordinalp a -> ordinalp b -> (S a b) = (S b a).
Proof.
move => oa; move: a oa b.
apply: least_ordinal2' => a oa ap.
apply: least_ordinal2' => b ob bp.
rewrite (nsv_rec oa ob) (nsv_rec ob oa); congr osups.
set_extens t.
  move/doubleI_rgP; case => - [y yi ->]; apply /doubleI_rgP.
    right; ex_tac.
    left; ex_tac.
move/doubleI_rgP;case => - [y yi ->]; apply /doubleI_rgP.
  by right; ex_tac; symmetry; apply: ap.
  by left; ex_tac; symmetry; apply: bp.
Qed.


Lemma nsv_00: S \0o \0o = \0o.
Proof.
rewrite (nsv_rec OS0 OS0).
suff: (doubleI_rg S \0o \0o) = emptyset by move ->; rewrite osups_set0.
by apply/set0_P => t/doubleI_rgP [] [y /in_set0].
Qed.  


Lemma nsv_n0 a: ordinalp a -> S a \0o = a.
Proof.
move: a; apply: least_ordinal2' => a oa ap.
rewrite (nsv_rec oa OS0).
suff : doubleI_rg S a \0o  = a by move ->; apply:osups_ordinal.
set_extens t.
  case/doubleI_rgP; first by move => [y /in_set0].
    by move => [y ya ->]; rewrite (ap _ ya).
by move => ta1; apply/doubleI_rgP; right; ex_tac;rewrite (ap _ ta1).
Qed.

Lemma nsv_0n a: ordinalp a -> S \0o a = a.
Proof.
by move => oa; rewrite (nsvC OS0 oa) (nsv_n0 oa). 
Qed.

Lemma nsv_ltl a1 a2 b: a1 <o a2 -> ordinalp b -> (S a1 b) <o (S a2 b).
Proof.
move => la1a2 ob; move: (proj32_1 la1a2) => oa2.
rewrite (nsv_rec oa2 ob); apply:osup_ub.
   move => t /doubleI_rgP  [][y yi ->]; apply:OS_nsv => //.
   apply: (Os_ordinal ob yi).
   apply: (Os_ordinal oa2 yi).
by apply/doubleI_rgP; right; exists a1 => //; apply:olt_i.
Qed.

Lemma nsv_ltr a b1 b2: ordinalp a -> b1 <o b2 -> (S a b1) <o (S a b2).
Proof.
move => oa lt1; rewrite (nsvC oa (proj31_1 lt1))(nsvC oa (proj32_1 lt1)).
by apply:nsv_ltl.
Qed.

Lemma nsv_lel a1 a2 b: a1 <=o a2 -> ordinalp b -> (S a1 b) <=o (S a2 b).
Proof.
move => leaa ob; case: (ole_eqVlt leaa).
  move ->;apply: oleR; apply:(OS_nsv (proj32 leaa) ob).
move=> ltaa; exact:(proj1 (nsv_ltl ltaa ob)).
Qed.

Lemma nsv_ler a b1 b2: ordinalp a -> b1 <=o b2 -> (S a b1) <=o (S a b2).
Proof.
move => oa lt1; rewrite (nsvC oa (proj31 lt1))(nsvC oa (proj32 lt1)).
by apply:nsv_lel.
Qed.

Lemma nsvA a b c: ordinalp a -> ordinalp b -> ordinalp c ->
   S a (S b c) = S (S a b) c. 
Proof.
move => oa ob oc; move: a oa c oc b ob.
apply: least_ordinal2 => a oa ap.
apply: least_ordinal2 => c oc cp.
apply: least_ordinal2 => b ob bp.
apply: oleA.
  apply: (nsv_le_prop oa (OS_nsv ob oc) (OS_nsv (OS_nsv oa ob) oc)).
    move => z za;rewrite (ap _ za _  oc _ ob).
    by apply:(nsv_ltl (nsv_ltl _ ob) oc).
  move => z /(nsv_lt_prop ob oc); case; move => [x lt1 lt2].
    apply: (ole_ltT (nsv_ler oa lt2)).
    by rewrite (bp _ lt1); apply: (nsv_ltl (nsv_ltr oa lt1) oc).
  move: (nsv_ler oa lt2);rewrite (cp _ lt1 b ob) => ha.
  apply: (ole_ltT ha); apply: (nsv_ltr (OS_nsv oa ob) lt1).
apply: (nsv_le_prop (OS_nsv oa ob) oc (OS_nsv oa (OS_nsv ob oc))).
  move => z /(nsv_lt_prop oa ob); case; move  => [x lt1 lt2].
    rewrite (nsvC (proj31 lt2) oc) (nsvC oc (proj31 lt2)).
    apply: (ole_ltT (nsv_lel lt2 oc)).
    rewrite - (ap _ lt1 _ oc _ ob); exact: (nsv_ltl lt1 (OS_nsv  ob oc)).
  apply:(ole_ltT (nsv_lel lt2 oc)).
  by rewrite - (bp _ lt1); apply: (nsv_ltr oa (nsv_ltl lt1 oc)).
by move => x lxc; rewrite - (cp _ lxc b ob); apply:(nsv_ltr oa (nsv_ltr ob _)).
Qed.

Lemma nsvACA a b c d: ordinalp a -> ordinalp b -> ordinalp c -> ordinalp d ->
  S (S a b) (S c d) = S (S a c) (S b d).
Proof.
move => oa ob oc od.
have h :=  (OS_nsv oa oc).
rewrite (nsvC oa ob)- (nsvA ob oa (OS_nsv oc od)) (nsvA oa oc od).
by rewrite (nsvC ob (OS_nsv h od)) - (nsvA h od ob) (nsvC od ob).
Qed.  

Lemma nsv_natsum: is_natural_sum S.
Proof.
split.
- apply: OS_nsv.
- apply: nsvC.
- by move => a bc oa ob oc; apply: nsvA.  
- apply:nsv_n0.   
- move => a b c oa ob oc; split => h; last exact:(nsv_ler oc h).
  by case: (oleT_el oa ob)=> // /(nsv_ltr oc) /oltNge; case.
Qed.
  
Lemma nsv_Sn a b: ordinalp a -> ordinalp b -> S (osucc a) b = osucc (S a b).
Proof.
move => oa; move:b; apply: least_ordinal2 => b ob bp.
apply: oleA; last by apply /oleSltP; exact: (nsv_ltl (oltS oa) ob).
apply: (nsv_le_prop (OS_succ oa) ob (OS_succ (OS_nsv oa ob))) => x.
  by move/oltSleP => sxa; apply/oltSleP; apply:nsv_lel.
by move => xb; rewrite (bp _ xb); apply/oltSSP; apply:nsv_ltr.
Qed.

Lemma nsv_nS a b: ordinalp a -> ordinalp b ->  S a (osucc b) = osucc (S a b).
Proof.
by move => oa ob; rewrite (nsvC oa (OS_succ ob))  (nsv_Sn ob oa)  (nsvC oa ob).
Qed.

Lemma nsv_nat a b: ordinalp a -> b <o omega0 -> S a b = a +o b.
Proof.
move => oa  /(oltP OS_omega) bN; move: b bN a oa ; apply:Nat_induction.
  by move => a oa; rewrite (nsv_n0 oa) (osum0r oa).
move => n nN Hr a oa.
rewrite (succ_of_nat nN) (nsv_nS oa (OS_nat nN)) (Hr _ oa).
by rewrite (osum2_succ oa (OS_nat nN)).
Qed.

Lemma nsv_ge_sum a b: ordinalp a -> ordinalp b -> a +o b <=o (S a b).
Proof.  
move => oa; move:b; apply: least_ordinal2' => b ob bp.
case:(ordinal_limA
        ob).
- move => ->; rewrite (osum0r oa) (nsv_n0 oa); fprops.
- move => [c oc cv]; rewrite cv - (osum2_succ oa oc) (nsv_nS oa oc).
  by apply/oleSSP; apply: bp; rewrite cv; fprops.
- move => lb.
  rewrite (proj2 (osum_normal oa) b lb).
  apply: (ord_ub_sup (OS_nsv oa ob)).
  move => c /funI_P [z zb1 ->]; move/(oltP ob): (zb1) => /proj1 le1.
  exact:(oleT (bp _ zb1) (nsv_ler oa le1)).
Qed.

Lemma nsv_aux u d: \0o <o u -> odegree u <=o d -> exists c r,
  [/\ c <o omega0, r <o oopow d   & u = oopow d *o c +o r].
Proof.
move => up /ole_eqVlt; case => dxy. 
  move/the_cnf_split:up;  move => [ha hb hc hd]; rewrite - dxy.
  by exists (the_cnf_lc u), (the_cnf_rem u). 
exists \0o, u; split.
- apply:olt_0omega.
- by apply:(olt_leT (proj2 (the_cnf_p4 up))); apply: opow_Mo_le;apply/oleSltP.
- by rewrite oprod0r (osum0l (proj32_1 up)).
Qed.


Lemma nsv_cantor_p1 p: ordinalp p -> 
  (forall q, q <o p ->
   (forall a b x y, a <o omega0 -> b <o omega0 -> 
    x <o oopow q -> y <o oopow q -> 
  S (oopow q *o a +o x) (oopow q *o b +o y) = oopow q *o (a +o b) +o S x y)) ->
  forall x y,  x <o oopow p -> y <o oopow p ->
  S x y <o oopow p.
Proof.
move => op Hp.
move: (oleR op); move: op.
move: {-3}(p); apply:least_ordinal2 => t ot tp lt1p x y xlt ylt.
move: (proj31_1 xlt) (proj31_1 ylt) => ox oy. 
case: (ozero_dichot ox); first by  move => ->; rewrite nsv_0n.
case: (ozero_dichot oy); first by  move => ->; rewrite nsv_n0.
move => yp xp.
move: (the_cnf_p6 ot xp xlt)(the_cnf_p6 ot yp ylt) => dx dy.
case: (omax_p1 (proj31_1 dx) (proj31_1 dy)).
set d := omax (odegree x) (odegree y) => lext leyt.
have lt: d <o t by  rewrite /d/omax/Gmax; Ytac h.
move: (nsv_aux xp lext) => [c1 [r1 [lc1 r1s xv]]].
move: (nsv_aux yp leyt) => [c2 [r2 [lc2 r2s yv]]].
move:(Hp _  (olt_leT lt lt1p) _ _ _ _ lc1 lc2 r1s r2s).
rewrite xv yv; move ->.
have hu:= (opow_Mo_lt lt).
move: (olt_ltT  (tp _ lt  (oleT (proj1 lt) lt1p) _ _  r1s r2s) hu) => lt2.
apply: indecomp_prop2 lt2 (indecomp_prop4 ot).
move/(oltP OS_omega): lc1 => c1N.
move/(oltP OS_omega): lc2 => c2N.
rewrite (osum2_2int c1N c2N).
move:(NS_sum c1N c2N); move:(c1 +c c2);  apply: Nat_induction.
  by rewrite oprod0r; apply: oopow_pos.
move => n nN H; rewrite (succ_of_nat nN).
rewrite (oprod2_succ (OS_oopow  (proj31_1 lt)) (OS_nat nN)).
apply: (indecomp_prop2 H hu  (indecomp_prop4 ot)).
Qed.

Lemma nsv_cantor_p2 p: ordinalp p ->
  forall a b x y, a <o omega0 -> b <o omega0->
  x <o oopow p -> y <o oopow p -> 
  S (oopow p *o a +o x) (oopow p *o b +o y) = oopow p *o (a +o b) +o S x y.
Proof.
move: p; apply:least_ordinal2 => p op pp.
have Ha x y:  x <o oopow p -> y <o oopow p ->   S x y <o oopow p.
  by apply: nsv_cantor_p1.
have oop:=(OS_oopow op).
have Hb a y: a <o omega0 -> y <o oopow p ->
   S (oopow p *o a) y  = (oopow p) *o a  +o y.
  move => lao; move: (proj31_1 lao) => oa;move: a oa lao y.
  apply:least_ordinal2 => b ob bp lbo y ys.
  move:(OS_prod2 oop ob) (proj31_1 ys) => of1 oy.
  move: y oy ys; apply:least_ordinal2 => y oy yp ys.
  apply: oleA; last exact: (nsv_ge_sum of1 oy).
  apply: (nsv_le_prop of1 oy (OS_sum2 of1 oy)); last first.
     move => x lxy; move:(olt_ltT lxy ys) => xs.
     rewrite (yp x lxy xs); apply: (osum_Meqlt lxy of1).
  move => x lxs.
  suff: S x y <o oopow p *o b.
    move => aux; apply: (olt_leT aux  (osum_Mle0 of1 oy)).
  case:(ozero_dichot ob) => cbz.
    by move: lxs; rewrite cbz oprod0r => /olt0.
  have bN: natp b by apply/(oltP OS_omega).
  move: (cpred_pr bN (nesym (proj2 cbz))) => [pN pv].
  have bv1: b = osucc (cpred b) by rewrite - succ_of_nat.
  have ox := proj31_1 lxs.
  move: (OS_nat pN) => opr.
  have cNN: cpred b <o omega0 by apply/(oltP OS_omega).
  have ps: cpred b <o b by rewrite {2}bv1; apply/oltS.
  have oopc:=  (OS_prod2 oop opr).
  have eq1: oopow p *o b = oopow p *o (cpred b) +o (oopow p). 
    by rewrite {1} bv1 (oprod2_succ oop opr). 
  case: (oleT_el (OS_prod2 oop opr) ox) => cpx.
    move: (odiff_pr cpx) ; set d := _ -o _ ; move => [od dv].
    move:(osum_Meqltr od oop oopc); rewrite - dv -eq1.
    move => h; move: (h lxs) => ds.
    move: (bp _ ps cNN _ ds); rewrite - dv => <-.
    move: (Ha _ _ ds ys)=> sdys.
    rewrite - (nsvA oopc od (proj31_1 ys)) (bp _ ps cNN _ sdys).
    by rewrite eq1; apply: osum_Meqlt.
  apply: (olt_ltT (nsv_ltl cpx (proj31_1 ys))); rewrite (bp _ ps cNN _ ys).
  by rewrite eq1; apply:osum_Meqlt.
have Hc a b: a <o omega0 -> b <o omega0 ->
   S ((oopow p) *o a) ((oopow p) *o b) = oopow p *o (a +o b).
  move => alo; move:(proj31_1 alo) => oa.
  move: a oa alo b; apply:least_ordinal2 => a oa ap alo b blo.
  move:(proj31_1 blo) => ob; move: b ob blo.
  apply:least_ordinal2 => b ob bp blo.
  move:(OS_prod2 oop oa) (OS_prod2 oop ob) => of1 of2.
  apply: oleA; last by rewrite (oprodD oa ob oop); exact: (nsv_ge_sum of1 of2). 
  apply: (nsv_le_prop of1 of2 (OS_prod2 oop (OS_sum2 oa ob))) => x xlt.
    have H u v: u <o omega0 -> v <o omega0 -> u +o v = v +o u.
      move => /(oltP OS_omega) uN /(oltP OS_omega) vN. 
      by rewrite !osum2_2int // csumC.
    move: (odivision_exists oop oa xlt).
    set a1 := oquo _ _; set r := orem _ _.
    move => [[oa1 or xv rs] a1s].
    have a1N := olt_ltT a1s alo.
    have of11 := OS_prod2 oop oa1.
    have a1bo: a1 +o b <o omega0 by apply: osum2_lt_omega.
    rewrite xv -  (Hb _ _ a1N rs).
    rewrite (nsvC of11 or) - (nsvA or of11 of2) (ap _ a1s a1N _ blo).
    rewrite (nsvC or (OS_prod2 oop (OS_sum2 oa1 ob))) (Hb _ _  a1bo rs).
    apply: (olt_leT (osum_Meqlt rs (OS_prod2 oop (proj31_1 a1bo)))).
    rewrite - (oprod2_succ oop (proj31_1 a1bo)) (H _ _ a1N blo) (H _ _ alo blo).
    by apply: (oprod_Meqle _  oop); apply/oleSltP;apply/osum_Meqlt.
  move: (odivision_exists oop ob xlt).
  set b1 := oquo _ _; set r := orem _ _.
  move => [[ob1 or xv rs] b1s].
  have b1N := olt_ltT b1s blo.
  have of11 := OS_prod2 oop ob1.
  have a1bo: a +o b1 <o omega0 by apply: osum2_lt_omega.
  rewrite xv -  (Hb _ _ b1N rs).
  rewrite (nsvA of1 of11 or) (bp _ b1s b1N) (Hb _ _  a1bo rs). 
  apply: (olt_leT (osum_Meqlt rs (OS_prod2 oop (OS_sum2 oa ob1)))).
  rewrite - (oprod2_succ oop (proj31_1 a1bo)).
  by apply: (oprod_Meqle _  oop); apply/oleSltP; apply/osum_Meqlt.
move => a b x y aN bN xs ys.
move: (proj31_1 aN) (proj31_1 bN) => oa ob.
move: (proj31_1 xs) (proj31_1 ys) => ox oy.
have abs:  a +o b <o omega0  by apply: osum2_lt_omega.
have xys:=(Ha _  _ xs ys).
have ooab:= (OS_prod2 oop (OS_sum2 oa ob)).
move:(OS_prod2 oop oa) (OS_prod2 oop ob) => of1 of2.
hnf; rewrite - (Hb _ _  aN xs) - (Hb _ _  bN ys).
by rewrite nsvACA // (Hc _ _ aN bN) Hb.
Qed.


Lemma nsv_cantor_p3 p x y : ordinalp p -> x <o oopow p -> y <o oopow p ->
  S x y <o oopow p.
Proof.
move => op.
by apply: (nsv_cantor_p1 op) => q /proj31_1 oq; apply:nsv_cantor_p2.
Qed.


Lemma nsv_cantor_p2_ww p: ordinalp p ->
  forall a b x y, a <o omega0 -> b <o omega0->
  x <o oopow p -> y <o oopow p -> 
  (oopow p *o a +o x) +#o (oopow p *o b +o y) = oopow p *o (a +o b) +o (x +#o y).
Proof.
move => op a b x y ha hb hx hy.
rewrite (cnfnat_sum_rem op ha hx) (cnfnat_sum_rem op hb hy).
have ox := (proj31_1 hx).
have oy := (proj31_1 hy).
have oa := (proj31_1 ha).
have ob := (proj31_1 hb).
move: (OS_prod2 (OS_oopow op) oa) (OS_prod2 (OS_oopow op) ob) => ooa oob.
have abs: a +o b <o omega0 by apply: osum2_lt_omega.
have eab : (b +o a) = (a +o b).
   move/olt_omegaP: ha => aN; move/olt_omegaP: hb => bN.
   by rewrite osum2_2int // osum2_2int // csumC.
have ow: ordinalp (oopow p *o a +#o x) by apply: OS_natural_sum.
rewrite (natural_sumC _ y)(natural_sumA ow oy oob).
rewrite - [in X in (X +#o _ = _)]   (natural_sumA ooa ox oy) natural_sumC.
rewrite (natural_sumA oob ooa (OS_natural_sum ox oy)).
move: (natural_small op hx hy) => ss.
rewrite (cnfnat_sum_mon op hb ha) eab.
by rewrite (cnfnat_sum_rem op abs ss). 
Qed.

Lemma nsv_cantor_ok x y: ordinalp x -> ordinalp y ->
   S x y = x +#o y.
Proof.
move => ox oy.
have Hu u v: u = \0c -> ordinalp v -> S u v = u +#o v.
   by move => -> ou; rewrite (nsv_0n ou) natural_sumC natural_sum0.
have Hv u v: v = \0c -> ordinalp u -> S u v = u +#o v.
   by move => -> ou; rewrite (nsv_n0 ou) natural_sum0.
move: (omax_p1 (OS_degree ox) (OS_degree oy)).
set n := omax(odegree x) (odegree y); move => [h1 h2].
move: (proj32 h1) => on.
move: n on  ox oy h1 h2 => n0 on0.
pose hyp n := forall x y, ordinalp x -> ordinalp y -> 
  odegree x <=o n -> odegree y <=o n -> S x y = x +#o y.
move: x y; suff: hyp n0 by apply.
case: (least_ordinal6 hyp on0) => //.
set n := least_ordinal _ _; move => [on mleast] [] x y ox oy ldx ldy.
case: (ozero_dichot ox) => xz; first by apply: Hu.
case: (ozero_dichot oy) => yz; first by apply: Hv.
move: (nsv_aux xz ldx) => [a [rx [la lrx ->]]].
move: (nsv_aux yz ldy) => [b [ry [lb lry ->]]].
rewrite (nsv_cantor_p2 on la lb lrx lry).                     
rewrite (nsv_cantor_p2_ww on la lb lrx lry).
move: (proj31_1 lrx) (proj31_1 lry) => orx ory.
apply: f_equal.
  case: (ozero_dichot orx) => xrz; first by apply: Hu.
  case: (ozero_dichot ory) => yrz; first by apply: Hv.
  move: (the_cnf_p6 on xrz lrx) (the_cnf_p6 on yrz lry) => d1 d2.
  move: (omax_p1 (proj31_1 d1) (proj31_1 d2)) => [qa qb].
  have /(oltP on): omax (odegree rx) (odegree ry) <o n.
    by rewrite/omax /Gmax; Ytac h.
  by move/mleast; apply.
Qed.


End OsumS. 


Section NatSum2.
Variables (rA rB A B: Set).
Hypotheses (wor1: worder_on rA A) (wor2: worder_on rB B). 
Let C := canonical_du2 A B.

Definition ns_compare_r x x' := 
  [/\ Q x = C0, Q x' = C0 & gle rA (P x) (P x')] 
  \/ [/\ Q x <> C0, Q x' <> C0 & gle rB (P x) (P x')].

Definition ns_compare := graph_on ns_compare_r C.

Lemma ns_order1: order_on ns_compare C.
Proof.
move: wor1 =>[[or1 _] sr1].
move: wor2 =>[[or2 _] sr2].
have rr a :inc a C -> ns_compare_r a a.
  move=> /candu2P [pa h]; case: h =>- [ha hb].
   left; split => //; order_tac; ue.
  have hh: Q a <> C0 by rewrite hb; fprops.
  right; split => //; order_tac; ue.
have esr: substrate ns_compare = C by apply: graph_on_sr. 
split => //.
apply: order_from_rel1. 
- move => w u v; case => -[ha hb hc];case => -[ha' hb' hc'].
  + left;split => //; order_tac.
  + by case: ha'.
  + by case: ha.
  + right; split => //; order_tac.
- move => u v /candu2P [pa qa] /candu2P [pb qb].
  case => -[ha hb hc];case => -[ha' hb' hc'].
  + apply: (pair_exten pa pb); [ order_tac | by  rewrite ha hb].
  + by case: ha'.
  + by case: ha.
  + apply: (pair_exten pa pb); first by order_tac.
    case: qa; first by move => [_ w]; case:ha.
    by move=> /proj2 ->; case qb => - [_]. 
- exact.
Qed.

Definition ns_extensions:=
  Zo (\Po(coarse C)) (fun z => sub ns_compare z /\ worder z).



Lemma ns_extensions_prop1 z: inc z  ns_extensions <->
  sub ns_compare z /\ worder_on z C.
Proof.
split.
  move => /Zo_P[/setP_P ha [hb hc]];split => //; split => //.
  set_extens t.
    by move/(order_reflexivityP (proj1 hc)) => ti; case/setXp_P: (ha _ ti).
  move => tC. 
  suff: inc (J t t) ns_compare by move/hb => ti; substr_tac.
  by move: ns_order1  => [qa qb]; order_tac; ue.
move => [qa [qb qc]]; apply: Zop_i => //; rewrite - qc.
apply: (sub_graph_coarse_substrate (proj41 (proj1 qb))).
Qed.
  

Lemma ns_extensions_prop2 z: inc z  ns_extensions <->
  [/\ sub ns_compare z, order_on z C & total_order z].
Proof.
split.
  move =>/ns_extensions_prop1 [ha [hb hc]];split => //; first  by case:hb.
  by apply: worder_total.
move => [ha [hb hc] hd]; apply/ns_extensions_prop1; split => //; split => //.
apply: (worder_prop_rev hb); rewrite hc => X XC neX. 
set X0 := Zo X (fun z => Q z = C0).
set X1 := Zo X (fun z => Q z = C1).
have nes: nonempty X0 \/ nonempty X1.
  case: neX => t tX; case/candu2P: (XC t tX) => pt; case => -[qa qb].
    by left; exists t; apply: Zo_i.
    by right; exists t; apply: Zo_i.
move: (wor1)  (wor2) => [wo1 sr1] [wo2 sr2].
have Ha: nonempty X0 -> exists2 a, inc a X0 & forall b, inc b X0 -> gle z a b.
  move => nex0; pose Y := fun_image X0 P.
  have neY: nonempty Y by apply: funI_setne.
  have sY:sub Y (substrate rA).
    rewrite sr1; move => t /funI_P [u /Zo_P[uX qu] ->].
    move /candu2P:(XC _ uX) => [_]; case; case => //; rewrite qu => _ bb.
    by case:C1_ne_C0.
  move:(worder_prop  wo1 sY neY) =>[a aY av].
  move/funI_P:aY => [b bX bp]; ex_tac.
  move/Zo_P: bX => [bX Qb].
  move => c /Zo_P [qa qb]; apply: ha; apply/graph_on_P1; split.
     by apply: XC.
     by apply: XC.
  left; split => //; rewrite - bp; apply:av; apply/funI_P; exists c => //.
  by apply: Zo_i.
have Hb: nonempty X1 -> exists2 a, inc a X1 & forall b, inc b X1 -> gle z a b.
  move => nex0; pose Y := fun_image X1 P.
  have neY: nonempty Y by apply: funI_setne.
  have sY:sub Y (substrate rB).
    rewrite sr2; move => t /funI_P [u /Zo_P[uX qu] ->].
    move /candu2P:(XC _ uX) => [_]; case; case => //; rewrite qu => _ bb.
    by case:C1_ne_C0.
  move:(worder_prop  wo2 sY neY) =>[a aY av].
  move/funI_P:aY => [b bX bp]; ex_tac.
  move/Zo_P: bX => [bX Qb].
  move => c /Zo_P [qa qb]; apply: ha; apply/graph_on_P1; split.
     by apply: XC.
     by apply: XC.
  have qbz:  Q b <> C0 by rewrite Qb; fprops.
  have qcz:  Q c <> C0 by rewrite qb; fprops.
  right; split => //; rewrite - bp; apply:av; apply/funI_P; exists c => //.
  by apply: Zo_i.
case: (emptyset_dichot X0) => x0e.
  have eq1: X = X1.
     set_extens t; [ move => tx; apply:Zo_i => // | by move/Zo_S ].
     move/candu2P:(XC _ tx) =>[_]; case; case => _ qa //.
     by empty_tac1 t; apply: Zo_i.
  rewrite eq1; apply: Hb; ue.
case: (emptyset_dichot X1) => x1e.
  have eq1: X = X0.
     set_extens t; [ move => tx; apply:Zo_i => // | by move/Zo_S ].
     move/candu2P:(XC _ tx) =>[_]; case; case => _ qa //.
     by empty_tac1 t; apply: Zo_i.
  rewrite eq1; apply: Ha; ue.
move: (Ha x0e) (Hb x1e) =>[a ax0 ap][b bx0 bp].
have ap1 x: inc x X -> Q x = C0 -> gle z a x.
  by  move => sa sb; apply: ap; apply:Zo_i.
have bp1 x: inc x X -> Q x <> C0 -> gle z b x.
  move => sa sb; apply: bp; apply:Zo_i => //.
  move/candu2P:(XC _ sa) =>[_];case;case => //.
move: (Zo_S ax0)  (Zo_S bx0) => aX bX.
have asz: inc a (substrate z) by rewrite hc; apply: XC.
have bsz: inc b (substrate z) by rewrite hc; apply: XC.
case: (proj2 hd a b asz bsz) => le.
  exists a => //x xX; case: (equal_or_not (Q x) C0) => qx.
  by apply: ap1.
  by move:(bp1 x xX qx) => ll; order_tac.
exists b => //x xX; case: (equal_or_not (Q x) C0) => qx.
  by move:(ap1 x xX qx) => ll; order_tac.
  by apply: bp1.
Qed.  

Definition ns_restrAB r x y := gle r (J x C0) (J y C1). 
Definition ns_extend1 (p: relation) x y:=
  [/\ Q x = C0, Q y = C1 & p (P x) (P y)]
  \/ [/\ Q x = C1, Q y = C0 & ~p (P y) (P x)].

Definition ns_extend (p: relation) :=
  Zo (coarse C) (fun z =>  ns_extend1 p (P z) (Q z)).

Lemma ns_restrAB_prop1 r (p:= ns_restrAB r): inc r ns_extensions ->
  forall x y,
    gle r x y <->
  [/\ inc x C, inc y C &  
  [\/ [/\ (Q x) = C0, Q y = C0 &  gle rA (P x) (P y)],
      [/\ (Q x) = C0, Q y = C1 &  p (P x) (P y)],
      [/\ (Q x) = C1, Q y = C0 &  ~p (P y) (P x)] |
      [/\ (Q x) = C1, Q y = C1 &  gle rB (P x) (P y)]]].
Proof.
move => /ns_extensions_prop2 [ha [or sr] tor] x y.
move: wor1 =>[wo1 sr1]; move:(proj2 (worder_total wo1)); rewrite sr1 => tr1.
move: wor2 =>[wo2 sr2]; move:(proj2 (worder_total wo2)); rewrite sr2 => tr2.
split.
  move => le1.
  have aux: gle r y x -> x = y by move => hb; move:(proj44 or _ _ le1 hb).
  have xC: inc x C by rewrite - sr; order_tac.
  have yC: inc y C by rewrite - sr; order_tac.
  split => //.
  move/candu2P: (xC) =>  [px xC1]; move/candu2P: (yC) =>  [py yC1].
  case: xC1; case: yC1.
  - move => [qa qb] [qc qd]; constructor 1; split => //.
    case:(tr1 _ _ qa qc) => // lab.
    have: inc (J y x) ns_compare.
       by apply/graph_on_P1; split => //; left.
    by move/ha /aux => eq1; move: lab; rewrite eq1.
  -  move => [qa qb] [qc qd]; constructor 2; split => //.
     by rewrite /p /ns_restrAB -qd -qb  px py.
  -  move => [qa qb] [qc qd]; constructor 3; split => //.
     rewrite /p /ns_restrAB -qd -qb  px py => /aux eq1.
     by move: C0_ne_C1; rewrite -qb - qd eq1.
  - move => [qa qb] [qc qd]; constructor 4; split => //.
    case:(tr2 _ _ qa qc) => // lab.
    have: inc (J y x) ns_compare.
      move: C1_ne_C0 => hh.
      by apply/graph_on_P1; split => //; right; rewrite qb qd.
    by move/ha /aux => eq1; move: lab; rewrite eq1.
move =>[xC yC]; case.
- by move => [pa pb pc]; apply: ha; apply/graph_on_P1; split => //; left.
- move => [pa pb]; rewrite /p/ns_restrAB -pa -pb.
  by move/candu2P:xC =>[-> _]; move/candu2P:yC =>[-> _].
- move => h;move: (proj2 tor); rewrite sr=> h1; case: (h1 _ _ xC yC) => //.
  move:h => [pa pb]; rewrite /p/ns_restrAB -pa -pb.
  by move/candu2P:xC =>[-> _]; move/candu2P:yC =>[-> _].
- move => [pa pb pc]; apply: ha; apply/graph_on_P1; split => //; right.
  by move: C1_ne_C0 => hh; rewrite pa pb.
Qed.


Lemma ns_restrAB_prop2 r (p:= ns_restrAB r): inc r ns_extensions ->
  r =  ns_compare \cup ns_extend (ns_restrAB r).
Proof.
move => h.
move: (ns_restrAB_prop1 h) => p1.
move:h => /ns_extensions_prop2 [ha [or sr] tor].
move: ns_order1 => [qa qb].
set_extens t.
  move => tr. move: (proj41 or t tr) => pt.
  move: tr; rewrite - pt; move/p1 =>[pC qC]; case; move=> [ra rb rc].
  - by apply/setU2_P; left; apply/graph_on_P1; split => //; left.
  - apply/setU2_P; right; apply: Zo_i; first by  apply: setXp_i.
    by left; aw.
  - apply/setU2_P; right; apply: Zo_i; first by  apply: setXp_i.
    by right; aw.
  - apply/setU2_P; left; apply/graph_on_P1; split => //; right.
    by move: C1_ne_C0 => hh; rewrite ra rb.
case/setU2_P.
  move=> /Zo_P [/setX_P [pt pta ptb]]  => h; rewrite - pt; apply/p1.
  split => //; case:h => h; first by constructor 1.
  move: h =>[pa pb pc].
  case:(candu2_pr2 pta) => // ->.
  case:(candu2_pr2 ptb) => // ->.
  by constructor 4.
move => /Zo_P [/setX_P [pt pta ptb]] => h; rewrite - pt; apply/p1.
split => //; case:h => h; [  by  constructor 2 | by constructor 3].
Qed.

            

                                         
Lemma ns_extensions_prop3: inc (order_sum2 rA rB) ns_extensions.
Proof.
apply/ns_extensions_prop1.
move: wor1 wor2 =>[wo1 sr1][wo2 sr2].
move: (orsum2_wor wo1 wo2) => wor3.
move: (orsum2_sr (proj1 wo1) (proj1 wo2)) ; rewrite sr1 sr2 -/C => h.
split => //.
move => t /Zo_P [/setX_P[qa qb qc] qd]; rewrite - qa; apply orsum2_gleP.
rewrite sr1 sr2; split => //; case: qd => qe; in_TP4.
Qed.


Lemma ns_extensions_prop4
  (swap0 := variant C0 C1 C0)
  (swap1 := fun x => (J (P x) (swap0 (Q x))))
  (swap2 := fun x => (fun_image x swap1)) 
  (swap3 := fun x => fun_image x (fun z => J (swap1 (P z))(swap1 (Q z))))
  (r3 := order_sum2 rB rA):
  r3 \Is swap3 r3 /\ inc (swap3 r3)  ns_extensions.
Proof.
move: wor1 wor2 =>[wo1 sr1][wo2 sr2].
move: (orsum2_wor wo2 wo1) => wor3.
move: (orsum2_sr (proj1 wo2) (proj1 wo1)) ; rewrite sr1 sr2=> sr4.
pose C' := canonical_du2 B A.
move: C1_ne_C0 C0_ne_C1 => c01 c10.
have eq1: swap2 C' = C.
   set_extens t.
     move=> /funI_P [z /candu2P [pa pb] ->]; apply/candu2P.
     rewrite/swap1;aw; split; first fprops.
     case: pb.  
       by move =>[pc ->]; right; split => //; rewrite /swap0 variant_true.
     by move =>[pc ->]; left; split => //; rewrite /swap0 variant_false.
   move/candu2P => [pp]; case.
     move=>[pa pb]; apply/funI_P.
     exists (J (P t) C1); first by apply:candu2_prb.
     by rewrite /swap1/swap0; aw; rewrite  -pb pp.
   move=>[pa pb]; apply/funI_P.
   exists (J (P t) C0); first by apply:candu2_pra.
   by rewrite /swap1/swap0; aw; rewrite  -pb pp.
pose f := Lf swap1 C' C.
have sf: source f = C'  by rewrite /f; aw.
have tf : target f = C by rewrite /f; aw.
have ax0: lf_axiom swap1 C' C.
  by rewrite - eq1; move => t rx; apply/funI_P; ex_tac.
have bf:  bijection f.
  rewrite /f - eq1; apply: lf_bijective.
  - move => t rx; apply/funI_P; ex_tac.
  - move => u v /candu2P [pp1 pu] /candu2P [pp2 pv] eq2.
    move: (pr1_def eq2) (pr2_def eq2) => eq3 eq4.
    apply: pair_exten => //; move: eq4; rewrite/swap0.
    case: pu; case: pv ;move => [_ ->] [_ ->] //.
      by rewrite (variant_false _ _ c01) variant_true.
      by rewrite (variant_false _ _ c01) variant_true.
  - move => y /funI_P [z zC ->]; ex_tac.
have eq2 : Vfs (f \ftimes f) r3 = (swap3 r3).
   have ff := proj1 (proj1 bf).
   have fff := ext_to_prod_f ff ff.
   have sff: source (f \ftimes f ) = coarse C' by rewrite /ext_to_prod sf; aw.
   have ss:   sub r3 (source (f \ftimes f)).
     rewrite sff /C' - sr4; apply sub_graph_coarse_substrate.
     exact (proj41 (proj1 wor3)).
   have ax: lf_axiom (fun z => J (Vf f (P z)) (Vf f (Q z)))
     (source f \times source f) (target f \times target f).
     by move => t /setX_P [pt ha hb]; apply: setXp_i; Wtac.
   set_extens t. 
      move/(Vf_image_P fff ss) => [u ur3 ->].
      move: (ss _ ur3); rewrite sff - sf => ucf.
      move/setX_P: (ucf); rewrite sf; move => [_ p1c p2c].
      rewrite /ext_to_prod; aw; rewrite/swap3/f !LfV//.
      apply/funI_P; ex_tac.
   move=>/funI_P [z zr3 -> ]; apply/(Vf_image_P fff ss); ex_tac.
   move: (ss _ zr3); rewrite sff - sf => ucf.
   move/setX_P: (ucf); rewrite sf; move => [_ p1c p2c].
   by rewrite /ext_to_prod; aw; rewrite/swap3/f ! LfV.
have sf': substrate   (order_sum2 rB rA) = source f by rewrite /f; aw.
move:(order_transportation bf (conj (proj1 wor3) sf')); rewrite eq2 => oif.
have is1: r3 \Is swap3 r3 by exists f.
have sr3: substrate (swap3 r3) = C.
  by move: (proj33 (proj43 oif)); rewrite tf.
move: (worder_invariance is1 wor3)=> wor4.
split => //; apply/ns_extensions_prop1; split => //.
move => t /Zo_P [/setX_P[qa qb qc] qd]; rewrite - qa; apply/funI_P.
move/candu2P: qb => [sa sb].
move/candu2P: qc => [sa' sb'].
case: qd.
  move => [ha hb hc].
  exists (J (J (P (P t)) C1) (J (P (Q t)) C1)).
     apply /orsum2_gleP. rewrite sr1 sr2; split.
    - by apply: candu2_prb; case: sb; case => //; rewrite ha.
    - by apply: candu2_prb; case: sb'; case => //; rewrite hb.
    - by constructor 2; aw.
  by rewrite /swap1/swap0; aw; rewrite - {1} ha sa - hb sa'.
move => [ha hb hc].
case: sb; [ by move => [_ bb]; case: ha | move => [ra rb]]. 
case: sb'; [ by move => [_ bb]; case: hb | move => [ra' rb']].
exists (J (J (P (P t)) C0) (J (P (Q t)) C0)).
  apply /orsum2_gleP; rewrite sr1 sr2; split.
    - by apply: candu2_pra. 
    - by apply: candu2_pra. 
    - by constructor 1; aw.
by rewrite /swap1/swap0; aw; rewrite  - {1} rb sa -rb' sa'.
Qed.


Definition ns_extensions_ord:=
  fun_image ns_extensions ordinal.


Lemma ns_extensions_prop5:
  inc ((ordinal rA) +o (ordinal rB)) ns_extensions_ord.
Proof.
move:ns_extensions_prop3=> ha;
  apply/funI_P;  ex_tac.
have oa := proj1 wor1; have ob := proj1 wor2.
apply:(orsum_invariant5 oa ob); apply: orderIR.
exact: (proj1 (orsum2_wor oa ob)).
Qed.

Lemma ns_extensions_prop6:
  inc ((ordinal rB) +o (ordinal rA)) ns_extensions_ord.
Proof.
move:ns_extensions_prop4 => [pa pb].
  apply/funI_P;  ex_tac.
have oa := proj1 wor1; have ob := proj1 wor2.
apply:(orsum_invariant5 ob oa pa). 
Qed.


Lemma ns_extensions_prop7:
  ordinal_set ns_extensions_ord.
Proof.
by move => t /funI_P [z /Zo_hi [_ oz] ->]; apply: OS_ordinal.
Qed.





End NatSum2.



End Ordinals3c.
Export Ordinals3c.
