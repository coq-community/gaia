(** * Theory of Sets : Natural sum & product
  Copyright INRIA (2016-2018) Apics, Marelle Team (Jose Grimm).
*)

(* $Id: sset13b.v,v 1.4 2018/09/04 07:57:59 grimm Exp $ *)

From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Export sset13a.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Ordinals3b.
  
(** cnf and operations *)



Lemma CNF_sum_pr1 x y n: cnfp x -> cnfp_nz y -> n <c domain x ->
   cnf_degree y <o oexp x n ->
   (n = \0c \/  oexp x (cpred n) <o cnf_degree y) ->
   cnf_val x +o cnf_val y = cnf_val (cnf_nm y (cnf_ns  x n)).
Proof.                                      
move => ox ynz lnd ha hb.
have od := (proj31_1 ha).
have Ha i j: i <c (domain x) -> cardinalp j -> oexp x i <o oexp x j -> i <c j.
  move => idx cj lt1; case: (cleT_el cj (proj31_1 idx)) => // lji.
  move:(CNF_exponents_M (proj42 ox) (proj1 (proj44 ox)) lji idx).
  by move/(oltNge lt1).
have nN := NS_lt_nat lnd (proj42 ox).
have lt3:= (cle_ltT (cpred_le (CS_nat nN)) lnd).
have kb:  position_in_cnf x (cnf_degree y) = n.
  move:(position_in_cnf_prop ox od) => [ka kb kc].
  have ck := (proj31 ka).
  case: (cleT_ell  (proj31_1 lnd) ck); first exact.
     by move/kb => /proj1 /oleNgt;case.
  move => lkn;case: (equal_or_not n \0c) => nz.
    by move: lkn; rewrite nz => /clt0.
  case: hb => hb; first by case: nz.
  case: kc; first by move => kd; case: (cleNgt (proj1 lnd)); rewrite - kd.
  move => le1; move:(olt_leT hb le1) => eq2.
  move: (cpred_pr nN nz) =>[mN mv].
  move:(Ha (cpred n) (position_in_cnf x (cnf_degree y)) lt3 ck eq2).  
  by move/(cleSltP mN); rewrite - mv => /cleNgt; case.
case: (inc_or_not (cnf_degree y) (domain (range x))) => hc.
  move/funI_P: hc =>[ p/(range_gP (proj41 ox)) [i idx iv] pv].
  rewrite pv in ha hb; rewrite iv in ha hb.
  move/(NltP (proj42 ox)): idx => ilx.
  move: (Ha i n ilx (proj31_1 lnd) ha) => lin.
  case: (equal_or_not n \0c) => nz.
    by move: lin; rewrite nz => /clt0.
  move: (cpred_pr nN nz) =>[mN mv].
  case: hb => // lt2. move:(Ha (cpred n) i lt3 (proj31_1 lin) lt2).
  by move/(cleSltP mN); rewrite - mv => /cleNgt; case.
move: (cnf_sum_prop9 ox ynz hc); rewrite kb => <-.
symmetry;apply:(cnf_sum_compat_prop ox (proj1 ynz)).
Qed.

Lemma CNF_sum_pr2 x y n: cnfp x -> cnfp_nz y ->
   n <c (domain x) -> oexp x n = cnf_degree y ->
   cnf_val x +o cnf_val y = cnf_val(cnf_ncms x y n).
Proof.
move => ox ynz lnd ha.
rewrite - (cnf_ncms_prop ox ynz lnd ha).
by rewrite (cnf_sum_compat_prop ox (proj1 ynz)).
Qed.

Lemma CNF_sum_pr3 x y: cnfp_nz x -> cnfp_nz y -> 
  cnf_degree x = cnf_degree y -> 
  cnf_val x +o cnf_val y = cnf_val(cnf_nc y (cnf_lc x)).
Proof.
move => xnz ynz sd.
rewrite - (cnf_ncms_prop_sd xnz ynz sd).
by rewrite (cnf_sum_compat_prop (proj1 xnz) (proj1 ynz)).
Qed.

Definition cnf_nck y k :=
  Lg (domain y) (cnf_c (Vg y) (cnf_size y) (J (cnf_degree y)
                                              ((cnf_lc y) *c k))).

Lemma cnf_nck_prop1 y k : natp k ->
   cnf_nck y (csucc k) = cnf_nc y ((cnf_lc y) *c k).
Proof.
by move => kN; rewrite /cnf_nck cprod_nS //.
Qed.

Lemma cnf_nck_prop2 x: cnfp_nz x -> cnf_nck x \1c = x.
Proof.
move => xnz; rewrite/cnf_nck.
move:(posnat_lc xnz) => /proj1/CS_nat cl; rewrite (cprod1r cl).
apply: fgraph_exten.
- fprops.
- exact (proj41 (proj1 xnz)).
- by aw.
- aw => i idx; rewrite /cnf_c LgV//; Ytac h => //.
- by rewrite /cnf_lc /cnf_degree - h  (proj43 (proj1 xnz) i idx).
Qed.

Lemma cnf_nck_prop3 x k: cnfp_nz x ->   natp k ->
      cnfp (cnf_nck x (csucc k)).
Proof.
move => xnz kN.
rewrite (cnf_nck_prop1 _ kN).
move:(NS_prod (proj1 (posnat_lc xnz)) kN) => aux.
by case:(cnf_nc_prop xnz aux).
Qed.

Lemma CNF_prod_pr1 x k : cnfp_nz x -> posnatp k -> 
  (cnf_val x) *o k = cnf_val (cnf_nck x k).
Proof.
move => xnz pnk.
move: (OS_cnf_val (proj1 xnz)) => oox.
move:(posnat_lc  xnz) => pnlc.
move:pnk => [kN kp].
move: (cpred_pr kN (nesym (proj2 kp))) => [nN ->].
move: (cpred k) nN; clear kN kp; apply: Nat_induction.
  by rewrite succ_zero (oprod1r oox) (cnf_nck_prop2 xnz).
move => n nN Hr.
move: (NS_succ nN) => snN.
have eq1 := (succ_of_nat snN).
rewrite eq1 (oprod2_succ (OS_cnf_val (proj1 xnz)) (OS_nat snN)) Hr - eq1.
set y := (cnf_nck x (csucc n)).
have hu: domain y = domain x by  rewrite /y/cnf_nck Lgd.
have hv := (cnf_size_nz_bis xnz).
have sd:  cnf_degree (cnf_nck x (csucc n)) = cnf_degree x.
   rewrite /cnf_degree/cnf_size hu /cnf_nck/oexp LgV//.
   by rewrite /cnf_c/cnf_size; Ytac0; aw.
have hw: (cnf_lc y) = (cnf_lc x *c csucc n).
  rewrite /cnf_lc /cnf_size hu /y /cnf_nck /ocoef LgV //.
  by  rewrite /cnf_c/cnf_size; Ytac0; aw.
have ynz: y <> emptyset.
  by  move => /domain_set0_P; rewrite hu => /domain_set0_P/(proj2 xnz).
have oy := (cnf_nck_prop3 xnz nN).
rewrite (CNF_sum_pr3 (conj oy ynz) xnz sd).
by rewrite (cnf_nck_prop1 _ snN) - hw; reflexivity.
Qed.

Definition cnf_shift_expo x d :=
  Lg (domain x) (fun i =>  J (d +o (oexp x i)) (ocoef x i)).

Lemma cnfp_shift_expo x d: cnfp x -> ordinalp d -> cnfp(cnf_shift_expo x d).
Proof.
rewrite/cnf_shift_expo; move => /cnfpP [ha hb hc hd] od; apply/cnfpP; split.
- fprops.
- by aw.
- aw => i idx; rewrite LgV//; move:(hc _ idx) => [qa qb qc]; split; aww.
- aw; move => i iN idx; move:(hd i iN idx) => lt1.
  move/(NltP hb): (clt_ltT (cltS iN) idx) => qa.
  move/(NltP hb):  idx => idx.
  rewrite /oexp !LgV//; aw; apply: (osum_Meqlt lt1 od).
Qed.
  
Lemma CNF_prod_pr0 x d: cnfp x -> ordinalp d ->
  cnf_val (cnf_shift_expo x d) =  oopow d  *o  (cnf_val x).
Proof.
move => ox od.
rewrite /cnf_val/cnf_shift_expo/CNFbvo/CNFbv Lgd.
move: (proj42 ox)(proj44 ox);set n := domain x => nN ax.
pose e' i := d +o oexp x i.
transitivity (osumf (cantor_mon omega0 e' (ocoef x)) n).
  apply: (osumf_exten nN) => i /(NltP nN)lin; aw.
  by rewrite/cantor_mon/ oexp/ocoef LgV//; aw.
move: n nN ax; apply:Nat_induction; first by rewrite ! osum_f0 oprod0r.
move => n nN Hrec axn.
have ax:=(CNFb_p5 nN axn).
have ood := (OS_oopow od).
have ooe:=(OS_oopow (CNFb_p8 axn nN)).
rewrite (osum_fS _ nN) (osum_fS _ nN) (Hrec ax).
rewrite (oprodD (CNFq_p0 (proj1 axn) (cltS nN)) (OS_CNFb nN ax) ood).
rewrite/cantor_mon (oprodA ood ooe (proj32_1(proj2 axn _ (cltS nN)))).
by rewrite (opow_sum OS_omega od (CNFb_p8 axn nN)). 
Qed.

Lemma ovaluation6 x: \0o <o x ->
  exists2 z, osuccp z & x = oopow (ovaluation x)  *o z.
Proof.
move => xp.
move:(the_cnf_p0_nz xp); set y := the_cnf x; move=> [ynz yv].
have oy := proj1 ynz.
rewrite/ovaluation;move.
move: (cnf_size_nz ynz); set m := cnf_size y; move => [mN mv].
set v := oexp y \0c.
set z := Lg (domain y) (fun i =>  J ( (oexp y i) -o v) (ocoef y i)).
have nN := (proj42 oy).
have Ha k: k <c domain y -> v <=o oexp y k.
  move => lkn; move:(cle0x (proj31_1 lkn)) => kp.
  exact: (CNF_exponents_M nN (proj1 (proj44 oy)) kp lkn). 
have Hb1 k:  k <c (domain y) -> oexp z k = (oexp y k) -o v.
  by move => /(NltP nN) kdx ; rewrite/z/oexp LgV//; aw.
have Hb k: k <c (domain y) ->
     ordinalp (oexp z k) /\ oexp y k = v +o  (oexp z k).
  move => kdx; rewrite (Hb1 _ kdx); exact: (odiff_pr (Ha _ kdx)).
have ody:= (proj1(cnf_size_nz_ter ynz)).
have ov: ordinalp v.
  by move/cnfpP: oy => /proj43 h; case : (h _ ody). 
have oz: cnfp z.
  rewrite/z; move/cnfpP:oy =>[ha hb hc hd]; apply/cnfpP; split.
  - fprops.
  - by aw.
  - aw =>i idy;rewrite LgV //; move:(hc i idy) =>[qa qb qc]; split; aww.
    have ->: (oexp y i -o v) = oexp z i by rewrite /z/oexp LgV//; aw.
    by move/(NltP hb): idy => /Hb/proj1.
  - aw;move => i iN lin.
    move: (clt_ltT (cltS iN) lin) => liin.
    move: (Hb _ lin) (Hb _ liin) =>[oe1 -v1][oe2 v2].
    apply:(osum_Meqltr oe2 oe1 ov); rewrite - v1 - v2; exact: (hd i iN lin).
move:(cnf_and_val_pb oz) =>[]; set t := cnf_val z. move => _ ot  zv _.
have ovt: ovaluation t = \0o.
  by rewrite /ovaluation zv /z/oexp LgV//; aw; rewrite (odiff_wrong (oleR ov)).
have xv: x = oopow v *o t.
  rewrite -(CNF_prod_pr0 oz ov) - yv; rewrite/cnf_val/CNFbvo /CNFbv.
  have dz: domain z = domain y by rewrite /z Lgd.
  have ->: (domain (cnf_shift_expo z v)) = domain y.
      rewrite /cnf_shift_expo Lgd//.
  apply: (osumf_exten  nN) => i ily;rewrite /cantor_mon/oexp /ocoef.
  move/(NltP nN): (ily) => idy; move:(idy); rewrite - dz => idz.
  rewrite /cnf_shift_expo LgV//; aw.
  by rewrite -(proj2 (Hb _ ily)) /z /ocoef LgV//; aw.
have tp: \0o <o t.
   by apply: (ord_ne0_pos ot) => tz; case: (proj2 xp); rewrite xv tz oprod0r.
move: (ovaluation2 tp ovt) => ost.
by rewrite xv; exists t.
Qed.

Lemma ovaluation7 e x e' x' :
  ordinalp e -> ordinalp e' -> osuccp x -> osuccp x' ->
  oopow e  *o x = oopow e'  *o x' ->
  (e = e' /\ x = x').
Proof.
move => oe oe' [y oy ->] [y' oy' ->].
move:(OS_pow OS_omega oe) (OS_pow OS_omega oe') => op op' => eq1.
move: (eq1);rewrite (oprod2_succ op oy) (oprod2_succ op' oy') => eq2.
move:(f_equal ovaluation eq2).
rewrite (ovaluation4 (OS_prod2 op oy) oe).
rewrite (ovaluation4 (OS_prod2 op' oy') oe') => ee'.
rewrite ee'  in eq1;split => //. 
apply:(oprod2_simpl (OS_succ oy) (OS_succ oy') (oopow_pos oe') eq1).
Qed.


Lemma CNF_prod_pr2 x : cnfp_nz x ->
  cnf_val x *o omega0 = oopow (cnf_degree x) *o omega0.
Proof.
move=> xnz.
have od:= OS_cnf_degree  xnz.
have h4:= (OS_oopow od).
have h5:= OS_prod2 h4 OS_omega.
apply: oleA; last first.
  rewrite (cnf_sum_prop5 xnz); apply: (oprod_Mleeq _ OS_omega).
  move/posnat_ordinalp: (posnat_lc xnz) => [pa _].
  move:  (OS_prod2 h4 (proj32_1 pa)) => h6.
  apply: (oleT (oprod_Mle1 h4 pa)).
  apply: (osum_Mle0 h6  (OS_cnf_rem (proj1 xnz))).
have pc':= (OS_cnf_valp  xnz).
have ov := proj32_1 pc'.
move: (oprod_normal pc') => [pg pk].
rewrite (pk _ (omega_limit)); clear pk.
apply: ord_ub_sup => //.
move=> i /funI_P [z zo ->].
move: zo => /(oltP OS_omega) zo.
have oz:= proj31_1 zo.
case: (ozero_dichot oz) => zno. 
  by rewrite zno (oprod0r); apply: ole0x.
move: (cnf_size_nz xnz) => [qa qb].
move: (proj44 (proj1 xnz)) => axo.
move: (cnf_size_nz_bis  xnz) => sd1.
move /(NltP (proj42 (proj1 xnz))):(sd1) => sd.
move: (axo) => [[_ h1 h2 _] h3].
move: (oprod2_lt_omega (h2 _ sd) zo) => /oleSltP so.
have pnz: posnatp z by apply/posnat_ordinalp.
rewrite (@CNF_prod_pr1 x z xnz pnz). 
rewrite /cnf_val/CNFbvo {3}/cnf_nck Lgd qb  (CNFq_p1 _ _ _ qa).
rewrite {1 2} /cnf_nck /cantor_mon /oexp/ocoef/cnf_c LgV//; Ytac0; aw.
set w := CNFbv _ _ _ _.
have lt1: w <o omega0 ^o (oexp x (cnf_size x)). 
  move: (pnz) => [za zb]; move: (cpred_pr za (nesym (proj2 zb))) => [zc zd].
  move: (proj44 (cnf_nck_prop3 xnz zc)); rewrite - zd.
  move/ proj1; rewrite {3}/cnf_nck Lgd qb => ax1.
  apply:(CNFq_pg3 qa (CNFq_p5 qa ax1) (h1 _ sd)).
  have aux: cnf_size x <c csucc (cnf_size x) by rewrite - qb.
  move => k kn. 
  move: (CNF_exponents_sM (NS_succ qa) ax1  kn aux).
  by rewrite {2} /cnf_nck {2}/oexp /cnf_c LgV//; Ytac0; aw.
have oy1 := (OS_prod2  (proj32_1 (proj2 (proj44  (proj1 xnz)) _ sd)) oz).
have hh4:=  (OS_prod2 h4 oy1).
move: (osum_Meqlt lt1  (OS_prod2 h4 oy1)); rewrite - (oprod2_succ h4 oy1).
have eq0: (ocoef x (cnf_size x) *o z) = (cnf_lc x *c z). rewrite -/(cnf_lc _).
   by rewrite (oprod2_2int (proj1 (posnat_lc  xnz)) (proj1 pnz)). 
rewrite {1} eq0.
move => [le1 _]; apply: (oleT le1 (oprod_Meqle so h4)).
Qed.



Lemma CNF_prod_pr2bis x: \0o <o x->
  x *o omega0 = oopow (odegree x) *o omega0.
Proof.
move => [/proj32 ox /nesym xp].
move: (the_cnf_p0 ox)=> [ha hb].
have unz: the_cnf x <> emptyset by move => h;case: xp; rewrite - hb h cnf_val0.
rewrite - hb (CNF_prod_pr2 (conj ha unz)).
by rewrite /odegree hb (Y_false xp). 
Qed.


Lemma CNF_prod_pr3 x y: \0o <o x -> limit_ordinal y ->
  x *o y = oopow (odegree x) *o y.
Proof.
move=> xnz ly; move:(proj32_1 xnz) => ox.
have oy:=(proj31 ly).
move/(limit_ordinal_P4 oy): ly => [z /proj32_1 oz yv].
have ot := (OS_pow OS_omega (OS_degree ox)).
by rewrite yv (oprodA ox OS_omega oz) (CNF_prod_pr2bis xnz)
  (oprodA ot OS_omega oz).
Qed.

Lemma oprod_crit_aux n x (y := oopow (oopow n)):
  ordinalp n ->  \1o <=o x ->  x <o y -> x *o y = y.
Proof.
move => on x1 xy.
move: OS_omega OS1 olt_1omega => oo o1 lt1o. 
have oy1:= OS_pow OS_omega on.
have oy:= OS_pow OS_omega oy1.
have xp: \0o <o x by apply/oge1P.
rewrite (CNF_prod_pr3 xp (indecomp_limit2 (oopow_pos on))).
have ox:= proj32 x1.
have od:=(OS_degree ox).
rewrite - (opow_sum OS_omega od oy1).
rewrite (indecomp_prop1 (indecomp_prop4 on)) //.
by apply: the_cnf_p6.
Qed.

Lemma CNF_prod_pr4 x y: cnfp_nz x -> cnfp_nz y -> \0o <o oexp y \0c -> 
  cnf_val x *o cnf_val y =  oopow (cnf_degree x) *o cnf_val y.
Proof.
move=>  xnz ynz pnz; set Y := cnf_val y.
move: (cnf_and_val_pb (proj1 ynz)) => [_ ha hb _].
move: (cnf_and_val_pb (proj1 xnz)) => [_ _ hc _].
have vp: \0o <o ovaluation Y by rewrite/ovaluation /Y hb. 
move:(OS_cnf_valp xnz) (OS_cnf_valp ynz) => xp Yp.
move: (ovaluation3 Yp vp) => ly.
rewrite(CNF_prod_pr3 xp ly) /cnf_degree. 
by rewrite (odegree_of_nz (nesym (proj2 xp))) hc.
Qed.

Lemma CNF_prod_pr5 x y: cnfp_nz x -> cnfp_nz y -> \0o <o oexp y \0c -> 
  (cnf_val x) *o (cnf_val y)= cnf_val (cnf_shift_expo y (cnf_degree x)).
Proof.
move=> xnz ynz vp. 
rewrite (CNF_prod_pr4 xnz ynz vp).
by rewrite (CNF_prod_pr0 (proj1 ynz)(OS_cnf_degree xnz)).
Qed.

  
Definition cnf_prod_gen x y :=
  cnf_nm (cnf_nck x (ocoef y \0c)) 
         (cnf_shift_expo (cnf_ns y \1c) (cnf_degree x)).


Lemma cnfp_prod_gen x y : cnfp_nz x -> cnfp_nz y -> cnfp( cnf_prod_gen x y).
Proof.
move => xnz ynz.
have [od1 od2]:=  (cnf_size_nz_ter ynz).
have ody: \1c <=c (domain y) by apply/cge1P.
move/cnfpP:(proj1 ynz) =>[_ _ ew _ ].
move: (proj33 (ew _ od1))=> pny0 {ew}.
have cnk: cnfp(cnf_nck x (ocoef y \0c)).
  move:pny0 =>[ua ub];move: (cpred_pr ua (nesym (proj2 ub)))=> [uc ud].
  by rewrite /ocoef ud; apply:cnf_nck_prop3.
move: (cnfp_cnf_ns (proj1 ynz) ody) => or.
move: (cnfp_shift_expo or (OS_cnf_degree xnz)) => oo.
apply: (cnfp_cnf_nm cnk oo).
move => i j. rewrite /cnf_nck /cnf_shift_expo 2! Lgd.
have d1: domain (cnf_ns y \1c) = domain y -c \1c by  rewrite/cnf_ns Lgd.
move: (proj42 (proj1 xnz)) => dxN.
move: (proj42 (proj1 ynz)) => dyN.
move: (NS_diff \1c dyN); rewrite - d1  => dzN. 
move => idx jdy.
move/(NltP dzN): (jdy); rewrite d1 => jiy.
move/(NltP dxN): (idx) => iix; set u := oexp _ _.
have -> : u = oexp x i
  by rewrite /u/oexp/cnf_c LgV//; Ytac foo;aw; trivial; rewrite foo.
apply: (ole_ltT (cnf_degree_greatest (proj1 xnz) iix)).
rewrite /oexp/cnf_ns/cnf_s !LgV//; aw.
have od:= (OS_cnf_degree xnz).
rewrite -{1} (osum0r od); apply:(osum_Meqlt _ od).
move:(NS_lt_nat jdy dzN) => jN.
have sjf: csucc j <c domain y.
  move: (cpred_pr dyN (nesym( proj2 od2)))=> [ha hb].
  rewrite hb; apply/cltSS; rewrite (cpred_pr4  (proj32_1 od2)).
  by apply/NltP => //; rewrite - d1.
move:(proj44 (proj1(proj44 (proj1 ynz))) j jN sjf).
rewrite - (csucc_pr4 (proj31_1 jdy)) => h.
exact:(ole_ltT  (ole0x (proj31_1 h)) h).
Qed.
  


Lemma CNF_prod_pr6 x y: cnfp_nz x -> cnfp_nz y ->  oexp y \0c = \0o ->  
  (cnf_val x) *o (cnf_val y) = cnf_val (cnf_prod_gen x y).
Proof.
move => xnz ynz vz.
have [od2 od1] := cnf_size_nz_ter ynz.
have ody: \1c <=c (domain y) by apply/cge1P.
move: (proj44 (proj1 ynz)) => [[_ qb qc _] _].
move: (proj31_1 (qc _ od1)) (OS_cnf_val (proj1 xnz)) => ra rb.
move/cnfpP:(proj1 ynz) =>[_ _ ew _ ].
move: (proj33 (ew _ od2))=> pny0 {ew}.
move: (cnfp_cnf_ns (proj1 ynz) ody) => or.
rewrite (cnf_sum_rec ynz) vz oopow0 (oprod1l ra).
rewrite (oprodD (OS_cnf_val or) ra rb).
have cnk: cnfp(cnf_nck x (ocoef y \0c)).
  move:pny0 =>[ua ub];move: (cpred_pr ua (nesym (proj2 ub)))=> [uc ud].
  by rewrite /ocoef ud; apply:cnf_nck_prop3.
rewrite(CNF_prod_pr1 xnz pny0).
have aux t: cnfp t -> cnf_nm t emptyset = t.
  move => [ha hb hc hd]; rewrite/cnf_nm domain_set0 (csum0r (CS_nat hb)).
  apply: fgraph_exten; aww => i idt; rewrite LgV//.
  by rewrite/cnf_m Y_true//; apply/(NltP hb).
case: (equal_or_not (domain y) \1c) => dy1.
  have eq0:(cnf_ns y \1c) = emptyset.
    by rewrite/cnf_ns dy1 cdiff_nn /Lg funI_set0.
  rewrite /cnf_prod_gen eq0 cnf_val0 oprod0r (osum0l (OS_cnf_val cnk)).
  by rewrite /cnf_shift_expo domain_set0 /Lg funI_set0 (aux _ cnk).
have qd: \1c <c domain y by split; fprops.
have dsnz: (domain y -c \1c) <> \0c by  apply: cdiff_nz. 
have cys: cnfp_nz (cnf_ns y \1c).
   by split =>// /domain_set0_P ;rewrite /cnf_ns Lgd.
have nep: \0o <o oexp (cnf_ns y \1c) \0c.
   have qe: inc \0c (domain y -c \1c).
      apply/(NltP (NS_diff \1c (proj42(proj1 ynz)))).
      by apply: (card_ne0_pos (CS_diff _ _)).
  rewrite - vz /oexp /cnf_ns/cnf_s LgV// (csum0l CS1) - succ_zero.
  have qf: csucc \0c <c domain y by rewrite succ_zero.
  by move:(proj44(proj1 (proj44(proj1 ynz))) _ NS0 qf). 
rewrite (@CNF_prod_pr5 x (cnf_ns y \1c) xnz cys nep).
rewrite cnf_sum_prop1 //; apply: (cnfp_shift_expo or (OS_cnf_degree xnz)).
Qed.  


Lemma odegree_prod a b: \0o <o a -> \0o <o b ->
  odegree (a *o b) = odegree a +o odegree b.
Proof.
move => ap bp.
rewrite (odegree_of_nz (nesym(proj2 (oprod2_pos ap bp)))).
rewrite (odegree_of_nz (nesym(proj2 ap))).
rewrite (odegree_of_nz (nesym(proj2 bp))).
move:(the_cnf_p0_nz ap) (the_cnf_p0_nz bp).
set x := the_cnf a; set y := the_cnf b.
move=> [xnz <-][ynz <-] . 
rewrite -/(cnf_degree x) -/(cnf_degree y).
have dxN := (proj42 (proj1 xnz)).
move: (cnf_size_nz xnz)(cnf_size_nz ynz) => [sxN sxv] [syN syv].
have ody:= (proj2 (cnf_size_nz_ter ynz)).
move: (proj42(proj1 (proj44 (proj1 ynz))) \0c ody) => oox.
have odx:=(OS_cnf_degree xnz).
case: (ozero_dichot oox)  => cz. 
  rewrite (CNF_prod_pr6 xnz ynz cz).
  rewrite (proj43 (cnf_and_val_pb (cnfp_prod_gen xnz ynz))).
  rewrite /cnf_prod_gen /cnf_ns.
  have ->: (domain y -c \1c) = cnf_size y.
    by rewrite syv - cpred_pr4; fprops; rewrite cpred_pr2.
  set d1 := (domain x +c (cnf_size y)).
  have eq1: d1 = csucc ((cnf_size x) +c (cnf_size y)). 
     by rewrite - (csum_Sn _  sxN) - sxv.
  have d1N: natp d1 by apply:(NS_sum dxN syN).
  have eq2: cpred d1 = (cnf_size x +c cnf_size y).
     rewrite eq1 cpred_pr2; fprops.
  have idd: inc (cpred d1) d1 by rewrite eq2 eq1; apply:Nsucc_i; fprops.
  rewrite/ cnf_prod_gen {1}/oexp /cnf_size /cnf_nm Lgd.
  rewrite /cnf_nck /cnf_shift_expo /cnf_ns !Lgd -/d1.
  rewrite LgV // eq2 /cnf_m; Ytac lt1.
    move/(NltP dxN):(lt1)=> lt2.
    move: lt1; rewrite sxv => /(cltSleP sxN).
    move: (Nsucc_i sxN)=> i3.
    rewrite -{2}(csum0r (CS_nat sxN)) => /(csum_le2l sxN syN NS0) /cle0 sy0.
    rewrite sy0 (csum0r (CS_nat sxN)) /cnf_c {3} /cnf_degree sy0 cz.
    by rewrite LgV//;Ytac0; aw; rewrite(osum0r odx).
  case:(NleT_el dxN (NS_sum sxN syN)) => //; rewrite sxv.
  rewrite {1} (csucc_pr4 (CS_nat sxN)) => /(csum_le2l sxN NS1 syN) /cge1P.
  move => /proj2/nesym snz.
  move:(cpred_pr syN snz); set c := cpred _; move => [cN cv].
  rewrite cv (csum_nS _ cN) -(csum_Sn _ sxN) csumC (cdiff_pr1 cN (NS_succ sxN)).
  rewrite syv (cpred_pr2 syN) /oexp/cnf_s.
  have i3: inc c (cnf_size y) by rewrite cv; apply: Nsucc_i.
  by rewrite !LgV// pr1_pair -  (csucc_pr4 (CS_nat cN)) - cv.
rewrite (CNF_prod_pr5 xnz ynz cz).
rewrite (proj43 (cnf_and_val_pb (cnfp_shift_expo (proj1 ynz) odx))).
rewrite /oexp/cnf_shift_expo /cnf_size Lgd LgV//; aw; trivial.
by rewrite syv (cpred_pr2 syN); apply: Nsucc_i.
Qed.
  

Definition oleading_coef x := let y := the_cnf x in ocoef y (cnf_size y).

Lemma oleading_coef_sum x y (a :=oleading_coef x) (b:=oleading_coef y):
  \0o <o x -> \0o <o y ->
  oleading_coef (x +o y) =
     Yo (odegree x <o odegree y) b (Yo (odegree y <o odegree x) a (a +c b)).
Proof.
move => xp yp.
move: (the_cnf_p0_nz xp); set xc := the_cnf x; move => [xnz xv].
move: (the_cnf_p0_nz yp); set yc := the_cnf y; move => [ynz yv].
rewrite (odegree_of_pos xp) (odegree_of_pos yp).
rewrite /a /b/oleading_coef(cnf_osum (proj32_1 xp) (proj32_1 yp)).
rewrite -/xc -/yc -/(cnf_degree xc) -/(cnf_degree yc).
move: (OS_cnf_degree xnz)(OS_cnf_degree ynz) => edx edy.
case: (oleT_ell edx edy) => lt.
- have ha: ~cnf_degree xc <o cnf_degree yc  by rewrite lt;case.
  have hb: ~cnf_degree yc <o cnf_degree xc  by rewrite lt;case.
  rewrite (Y_false ha) (Y_false hb).
  rewrite(cnf_ncms_prop_sd xnz ynz lt).
  rewrite/cnf_nc/cnf_c /cnf_size Lgd /ocoef LgV//; aw.
    by Ytac0; aw; trivial.
  move: (cnf_size_nz ynz) => [syN ->].
  by rewrite cpred_pr1; fprops; apply:Nsucc_i.
- by rewrite (cnf_sum_small_deg xnz ynz lt); Ytac0.
- Ytac0; rewrite (Y_false (oleNgt (proj1 lt))).
  rewrite/ocoef; congr Q.
  set ms := Vg _ _; set mx := Vg _ _.
  move: (proj1 xnz)(proj1 ynz) => ox oy.
  have os := (cnfp_sum ox oy).
  have snz:= (conj os (cnf_sum_nz ox ynz)).
  have: inc mx (range (xc +f yc)).
    apply/(cnf_sum_rangeP ox ynz); constructor 2; split  => //.
    move: (cnf_size_nz_bis xnz) => r1.
    apply/(range_gP (proj41 (proj1 xnz))); ex_tac.
  move/(range_gP (proj41 os)) => [i idx mv].
  move:(cnf_size_nz snz); set s := cnf_size _; move => [ra rb].
  move: idx; rewrite rb => /(NleP ra); case/cle_eqVlt => lis.
    by rewrite mv lis.
  move:(cnf_degree_greatest_bis os lis); rewrite /oexp - mv => lt1.
  move:(inc_V_range (proj41 os) (cnf_size_nz_bis snz)).
  move:(olt_ltT lt lt1) => lt2.
  case/(cnf_sum_rangeP ox ynz).
  + by move/proj2 => dd; case: (olt_ltT lt2 dd).
  + move => [ha _ ].
    move/(range_gP (proj41 (proj1 xnz))): ha => [j jdx jv].
     move:(cnf_size_nz xnz); set sx := cnf_size _; move => [wra wrb].
    move: jdx; rewrite wrb => /(NleP wra);case/cle_eqVlt => liw //.
      by rewrite /ms jv liw.
    move:(oleNgt (proj1 (cnf_degree_greatest_bis (proj1 xnz) liw))).
    by rewrite /oexp - jv.
  + by move => ea; case: (proj2 lt2); move: (f_equal P ea); aw; move <-.
Qed.


Lemma oleading_coef_prod1 x y: \0o <o x -> posnatp y -> 
   oleading_coef (x *o y) =(oleading_coef x) *c y.
Proof.
move => xp kp.
rewrite/oleading_coef. 
move:(the_cnf_p0_nz xp) => [sa sb].
move:(CNF_prod_pr1 sa kp); rewrite sb => ha.
move: (cpred_pr (proj1 kp) (nesym(proj2(proj2 kp)))) => [qa  qb].
move: (cnf_nck_prop3 sa qa); rewrite - qb => ax.
move: (proj43 (cnf_and_val_pb ax)); rewrite - ha => ->.
rewrite /cnf_nck/cnf_size Lgd/ocoef.
have id: inc (cpred (domain (the_cnf x))) (domain (the_cnf x)).
   move: (cnf_size_nz sa)=> [qc qd].
   by rewrite qd cpred_pr1; fprops; apply: Nsucc_i.
by rewrite LgV ///cnf_c; Ytac0; aw.
Qed.

Lemma oleading_coef_prod2 a b: \0o <o a -> omega0 <=o b -> 
  oleading_coef (a *o b) = oleading_coef b.
Proof.
move => ap bi.
move:(olt_leT olt_0omega bi) => bp.
move : (odegree_infinite bi).
clear bi.
rewrite (odegree_of_nz (nesym(proj2 bp))).
rewrite /oleading_coef /odegree.
move:(the_cnf_p0_nz ap) (the_cnf_p0_nz bp).
set x := the_cnf a; set y := the_cnf b.
move=> [xnz <-][ynz <-] . 
rewrite -/(cnf_degree x) -/(cnf_degree y).
have dxN := (proj42 (proj1 xnz)).
move: (cnf_size_nz xnz)(cnf_size_nz ynz) => [sxN sxv] [syN syv].
have ody:= proj2(cnf_size_nz_ter ynz).  
move: (proj42(proj1 (proj44 (proj1 ynz))) \0c ody) => oox.
have odx:=(OS_cnf_degree xnz).
case: (ozero_dichot oox)  => cz. 
  rewrite (CNF_prod_pr6 xnz ynz cz).
  rewrite (proj43 (cnf_and_val_pb (cnfp_prod_gen xnz ynz))).
  rewrite /cnf_prod_gen /cnf_ns.
  have ->: (domain y -c \1c) = cnf_size y.
    by rewrite syv - cpred_pr4; fprops; rewrite cpred_pr2.
  set d1 := (domain x +c (cnf_size y)).
  have eq1: d1 = csucc ((cnf_size x) +c (cnf_size y)). 
     by rewrite - (csum_Sn _  sxN) - sxv.
  have d1N: natp d1 by apply:(NS_sum dxN syN).
  have eq2: cpred d1 = (cnf_size x +c cnf_size y).
     rewrite eq1 cpred_pr2; fprops.
  have idd: inc (cpred d1) d1 by rewrite eq2 eq1; apply:Nsucc_i; fprops.
  rewrite/ cnf_prod_gen {1}/ocoef /cnf_size /cnf_nm Lgd.
  rewrite /cnf_nck /cnf_shift_expo /cnf_ns !Lgd -/d1.
  rewrite !LgV //eq2 /cnf_m; Ytac lt1.
  move/proj2; case. 
    move/(NltP dxN):(lt1)=> lt2.
    move: lt1; rewrite sxv => /(cltSleP sxN).
    move: (Nsucc_i sxN)=> i3.
    rewrite -{2}(csum0r (CS_nat sxN)) => /(csum_le2l sxN syN NS0) /cle0 sy0.
    by rewrite /cnf_degree sy0 cz.
  case:(NleT_el dxN (NS_sum sxN syN)) => //; rewrite sxv.
  rewrite {1} (csucc_pr4 (CS_nat sxN)) => /(csum_le2l sxN NS1 syN) /cge1P.
  move => /proj2/nesym snz.
  move:(cpred_pr syN snz); set c := cpred _; move => [cN cv].
  rewrite cv (csum_nS _ cN) -(csum_Sn _ sxN) csumC (cdiff_pr1 cN (NS_succ sxN)).
  rewrite syv (cpred_pr2 syN) /oexp/ocoef/cnf_s.
  have i3: inc c (cnf_size y) by rewrite cv; apply: Nsucc_i.
  by rewrite !LgV//;aw; rewrite - (csucc_pr4 (CS_nat cN)) - cv.
move => _.
rewrite (CNF_prod_pr5 xnz ynz cz).
rewrite (proj43 (cnf_and_val_pb (cnfp_shift_expo (proj1 ynz) odx))).
rewrite /ocoef/oexp/cnf_shift_expo /cnf_size Lgd LgV//; aw; trivial;
by rewrite syv (cpred_pr2 syN); apply: Nsucc_i.
Qed.
  

Lemma ovaluation_prod a b: \0o <o a -> \0o <o b ->
  ovaluation (a *o b) =
  Yo (ovaluation b = \0o) (ovaluation a) (odegree a +o ovaluation b).
Proof.
move => ap bp.
rewrite /ovaluation.
rewrite (odegree_of_nz (nesym(proj2 ap))).
move:(the_cnf_p0_nz ap) (the_cnf_p0_nz bp).
set x := the_cnf a; set y := the_cnf b.
move=> [xnz <-][ynz <-] . 
rewrite -/(cnf_degree x) -/(cnf_degree y).
have dxN := (proj42 (proj1 xnz)).
move: (cnf_size_nz xnz)(cnf_size_nz ynz) => [sxN sxv] [syN syv].
have [oody2 ody] := cnf_size_nz_ter ynz. 
move: (proj42(proj1 (proj44 (proj1 ynz))) \0c ody) => oox.
have odx:=(OS_cnf_degree xnz).
case: (ozero_dichot oox)  => cz. 
  rewrite (CNF_prod_pr6 xnz ynz cz).
  rewrite (proj43 (cnf_and_val_pb (cnfp_prod_gen xnz ynz))).
  rewrite/cnf_prod_gen/oexp/cnf_nm/cnf_shift_expo !Lgd.
  have ->: (domain y -c \1c) = cnf_size y.
    by rewrite syv - cpred_pr4; fprops; rewrite cpred_pr2.
  have [oodx2 oodx]:= cnf_size_nz_ter xnz.
  have aux: inc \0c (domain x +c cnf_size y).
    apply/(NltP (NS_sum dxN syN)).
    rewrite sxv(csum_Sn _ sxN); apply: succ_positive.
  rewrite LgV// /cnf_m; Ytac0; Ytac0; rewrite/cnf_nck /cnf_c.
  rewrite LgV//; Ytac foo => //; aw; ue.
rewrite (CNF_prod_pr5 xnz ynz cz).
rewrite (proj43 (cnf_and_val_pb (cnfp_shift_expo (proj1 ynz) odx))).
by rewrite (Y_false (nesym (proj2 cz))) /oexp/cnf_shift_expo LgV//; aw.
Qed.
  

Lemma opow_int_omega n:
  \2o <=o n -> n <o omega0 -> n ^o omega0 = omega0.
Proof.
move=> n2 no.
have oo:= OS_omega.
have on:= proj32 n2.
have nz:=(olt_leT olt_02 n2). 
apply:oleA.
  rewrite (proj2 (opow_normal n2) _ omega_limit).
  apply: ord_ub_sup => //.    
  by move => x /funI_P [z /(oltP oo) /(opow_2int1 no) [zo _] ->].
by move: (opow_Mspec2 oo n2); rewrite oprod_int_omega.
Qed.

Lemma CNF_pow_pr1 x k: cnfp_nz x -> \0o <o (oexp x \0c) -> natp k ->
  (cnf_val x) ^o (osucc k) =  (oopow ((cnf_degree x) *o k)) *o (cnf_val x).
Proof.
move=> xp vxp.
move:(OS_cnf_valp xp) => xnz;move:(proj32_1 xnz) => ox.
move: (OS_cnf_degree xp) => olcx.
move: k; apply: Nat_induction.
  by rewrite (oprod0r) oopow0 (oprod1l ox) osucc_zero opowx1.
move=> k kN hrec.
move:(OS_nat kN) => ok.
have osk := OS_succ ok.
have odf:=(OS_prod2 olcx ok).
move: (OS_pow OS_omega odf)(OS_pow OS_omega olcx) =>  of1 ood.
rewrite (succ_of_nat kN)(opow_succ ox osk) hrec -(oprodA of1 ox ox).
rewrite (CNF_prod_pr4 xp xp vxp) (oprodA of1 ood ox)(oprod2_succ olcx ok).
by rewrite - (opow_sum OS_omega odf olcx). 
Qed.


Lemma CNF_pow_pr1_bis x k: limit_ordinal x -> natp k ->
  x ^o (osucc k) =  (oopow ((odegree x) *o k)) *o x.
Proof.
move/ovaluation3_rev => [xp vxp]  kN.
move:(the_cnf_p0_nz xp) => [qa qb].
by move:(CNF_pow_pr1 qa vxp kN); rewrite (odegree_of_pos xp) qb.
Qed.

Lemma CNF_pow_pr2 x k: omega0 <=o x ->  posnatp k ->
  odegree (x ^o k) = (odegree x) *o k  /\ 
  oleading_coef(x ^o k) = oleading_coef x.
Proof.
move => xinf [ka /proj2/nesym kb].
move:(olt_leT olt_0omega xinf) => xnz.
move:(proj32_1 xnz) => ox.
move:(OS_degree ox) => od.
move:(cpred_pr ka kb) =>[nN ->].
move: (cpred k)nN; clear k ka kb.
apply: Nat_induction.
  by rewrite succ_zero (opowx1 ox) (oprod1r od).
move => n nN [ha hb].
move:(OS_nat (NS_succ nN)) => osn.
rewrite(succ_of_nat (NS_succ nN)) (opow_succ  ox osn).
move: (opow_pos xnz osn) => xpnz.
rewrite (odegree_prod xpnz xnz)  (oleading_coef_prod2 xpnz xinf).
by rewrite ha  - oprod2_succ.
Qed.

Lemma CNF_pow_pr3 x: omega0 <=o x ->
  x ^o omega0  = oopow ((odegree x) *o omega0).
Proof.
move => xinf.
have oo:= OS_omega.
move:(olt_leT olt_0omega xinf) => xp.
move:(odegree_infinite xinf) => enz; move: (proj32_1 enz) => oe.
move:(the_cnf_p4 xp) => [le1 le2]. 
have od := proj32_1 xp; have pa:= (oopow_pos od).
move:(opow_Mleeq (oopow_nz oe) le1 OS_omega).
move:(opow_Mleeq (nesym (proj2 xp)) (proj1 le2) OS_omega).
rewrite - (opow_prod oo (OS_succ oe) oo) - (opow_prod oo oe oo).
rewrite(indecomp_prod3 enz); apply: oleA.
Qed.

Lemma CNF_pow_pr4 x y: omega0 <=o x ->  limit_ordinal y ->
  x ^o y  = oopow ((odegree x) *o y).
Proof.
move: OS_omega => oo infx limy.
have ox:= proj32 infx.
have op := (OS_degree (proj32 infx)).
move/ (limit_ordinal_P4 (proj31 limy)): limy  => [z /proj32_1 oz ->].
rewrite (opow_prod ox oo oz) (CNF_pow_pr3 infx).
by rewrite - (opow_prod oo (OS_prod2 op oo) oz) (oprodA op oo oz).
Qed.


Lemma CNF_pow_pr5 x y: 
  \2o <=o x -> x <o omega0 -> limit_ordinal y ->
  exists z,
   [/\ ordinalp z, y = omega0 *o z & x ^o y = oopow z].
Proof.
move=> x2 xo limy.
move/ (limit_ordinal_P4 (proj31 limy)): limy  => [z /proj32_1 oz ->].
by rewrite (opow_prod (proj32 x2) OS_omega oz) (opow_int_omega x2 xo); exists z.
Qed.

Lemma CNF_pow_pr5_deg x y: \2o <=o x -> x <o omega0 -> ordinalp y ->
   odegree (x ^o y) = oquo y omega0.
Proof.
move => lx2 lxo oy.
move: (oquoremP oy olt_0omega); set q := oquo _ _; set r := orem _ _.
move =>[oq or -> rs].
move: (proj32 lx2)  (olt_leT olt_02 lx2) (OS_prod2 OS_omega oq) => ox xp op.
rewrite (opow_sum ox op or).
rewrite (opow_prod ox OS_omega oq) (opow_int_omega lx2 lxo).
rewrite (odegree_prod (oopow_pos oq) (opow_pos xp or)).
rewrite (odegree_opow oq).
by rewrite (odegree_finite (opow_2int1 lxo rs)) (osum0r oq).
Qed.

Lemma CNF_pow_pr4_deg x y: omega0 <=o x -> ordinalp y ->
    odegree (x ^o y) = odegree x *o y.
Proof.
move => xgo oy.
move: (oquoremP oy olt_0omega); set q := oquo _ _; set r := orem _ _.
move =>[oq or -> rs].
move: (proj32 xgo)  (olt_leT olt_0omega xgo) (OS_prod2 OS_omega oq) => ox xp op.
have od := (OS_degree ox). 
have op1:= (OS_prod2 od OS_omega).
rewrite (opow_sum ox op or) (odegree_prod (opow_pos xp op)(opow_pos xp or)).
rewrite  (opow_prod ox OS_omega oq)  (CNF_pow_pr3 xgo).
rewrite - (opow_prod OS_omega op1 oq) (odegree_opow (OS_prod2 op1 oq)).
suff:  odegree (x ^o r) = (odegree x) *o r.
  by move ->; rewrite - (oprodA od OS_omega oq) (oprodD op or od).
move/olt_omegaP: rs; clear or;move: r; apply: Nat_induction.
  by rewrite opowx0 oprod0r odegree_one.
move => n nN; move:(OS_nat nN) => on.
rewrite (succ_of_nat nN) (opow_succ ox on) (oprod2_succ od on).
by rewrite (odegree_prod (opow_pos xp on) xp) => ->.
Qed.

(* ------- couper ici --------  *)


(** Cantor product form *)

Definition CNFp_value1 e c := osucc ((oopow e) *o c).
Definition CNFp_value2 e c := (osucc (oopow e)) *o c.

Lemma CNF_succ_pow1 n c (x := (osucc ((oopow n) *o c)))
      (X := variantLc (J \0o \1o) (J n c)):
  \0o <o n -> posnatp c-> cnf_and_val X x.
Proof.
move => ha hb. 
move/posnat_ordinalp: (hb) => /proj1 /proj32_1 on.
move:(cnf_two_terms ha hb PN1); rewrite /oopow opowx0 (oprod1r OS1).
rewrite osucc_pr //; apply: (OS_prod2 (OS_oopow (proj32_1 ha)) on).
Qed.


Lemma CNF_succ_pow n (x:= osucc (oopow n))
      (X := variantLc (J \0o \1o) (J n \1c)):
  \0o <o n ->  cnf_and_val X x.
Proof.
move => ha; move:(CNF_succ_pow1 ha PN1).
by rewrite (oprod1r (OS_oopow (proj32_1 ha))).
Qed.


Lemma odegree_succ_pow n : \0o <o n -> odegree (osucc (oopow n)) = n.
Proof.
move => h.
rewrite (odegree_of_nz (@osucc_nz _)).
move:  (CNF_succ_pow h) => [_ _ -> _].
by rewrite /cnf_size /oexp; aw; rewrite cpred2; aw.
Qed.

Lemma CNFp_pr1 e c:
  \0o <o e -> posnatp c ->
  CNFp_value1 e c = CNFp_value2 e c.
Proof.
move=> ep cp.
move: (CS_nat (proj1 cp)) => cz.
rewrite /CNFp_value1 /CNFp_value2.
move:(CNF_succ_pow ep); set v := variantLc _ _; set x := osucc _.
move => [qa qb qc qd].
have vnz: cnfp_nz v by split=> //; move/domain_set0_P;rewrite /v;aww.
rewrite - qd (CNF_prod_pr1 vnz cp) - (proj44 (CNF_succ_pow1 ep cp)).
congr cnf_val;rewrite /cnf_nck/v /cnf_size/cnf_c; aw; rewrite cpred2.
have foo: ~(C0 = \1c) by fprops.
apply: Lg_exten => y yd; try_lvariant yd; first by Ytac0.
rewrite/cnf_degree/cnf_lc/ocoef/cnf_size/oexp (Y_true  (erefl C1)); aw.
by rewrite cpred2  LgV//; aww; rewrite cprod1l.
Qed.

Definition pmonomp m := [/\ pairp m, \0o <o P m &  posnatp (Q m)].

Definition CNFp_ax (p: fterm) n:=
   (forall i, i <c n -> pmonomp (p i)) /\ omonomp (p n).

Definition CNFp_ax1 (p: fterm) n:=
  forall i, i <c n -> pmonomp (p i).

Definition cantor_pmon (p: fterm) i :=  CNFp_value1 (P (p i)) (Q (p i)).

Definition CNFpv1 (p: fterm) n :=  oprodf (cantor_pmon p) n.

Definition CNFpv (p:fterm) n :=
  ((oopow (P (p n))) *o (Q (p n))) *o (CNFpv1 p n).

Lemma OS_CNFp0 p n: CNFp_ax1 p n ->
   ord_below (cantor_pmon p) n.
Proof.
move => ax i lin; move:(ax  i lin) => [_ /proj32_1 oa /proj1/OS_nat ob].
exact: (OS_succ ( OS_prod2 (OS_oopow oa) ob)).
Qed.

Lemma OS_CNFp1 p n: CNFp_ax1 p n -> natp n -> ordinalp (CNFpv1 p n).
Proof.
move => ax nN; apply: (OS_oprodf nN) => // i lin.
apply:(OS_CNFp0 ax lin).
Qed.

Lemma OS_CNFp1r p n m: CNFp_ax1 p n -> natp n -> m <=c n ->
   ordinalp (CNFpv1 p m).
Proof.
move => ax nN nm; apply: (OS_oprodf (NS_le_nat nm nN)) => // i lin.
apply:(OS_CNFp0 ax (clt_leT lin nm)).
Qed.

Lemma OS_CNFp p n:  CNFp_ax p n -> natp n -> ordinalp (CNFpv p n).
Proof.
move => ax nN.
move: (OS_CNFp1 (proj1 ax) nN) => o1.
move: (proj2 ax) => [ _ oa  /proj1/OS_nat ob].
exact (OS_prod2 (OS_prod2 (OS_oopow oa) ob) o1).
Qed.

Lemma CNFp_0 p: CNFpv1 p \0c = \1o.
Proof. by apply: oprod_f0. Qed.

Lemma CNFp_1 p n: CNFp_ax1 p n -> \0c <c n ->
  CNFpv1 p \1c = cantor_pmon p \0c.
Proof.
move => ax1 n1; rewrite /CNFpv1 oprod_f1 //. 
apply: (OS_CNFp0 ax1 n1).
Qed.

Lemma CNFp_A p n m :
  natp n -> natp m -> CNFp_ax1 p (n +c m) ->
  CNFpv1 p (n +c m) = (CNFpv1 p n) *o 
    CNFpv1 (fun z => p (z +c n)) m.
Proof. move => nN mN /OS_CNFp0; exact(oprod_fA nN mN). Qed.

Lemma CNFp_r p n: natp n -> 
  CNFpv1 p (csucc n) = CNFpv1 p n  *o (cantor_pmon p n).
Proof. move => nN; exact:(oprod_fS _ nN). Qed. 


Lemma CNFp_p2 e c n (a:= e n -o (e (cpred n))) (b := c n):
   CNFb_axo e c (csucc n) -> natp n -> n <> \0c ->
   [/\ \0o <o a, posnatp b &
    CNFbvo e c (csucc n) = (CNFbvo e c n) *o (CNFp_value1 a b)].
Proof.
move => ax nN nz.
move: (cpred_pr nN nz) => [pnN pn]. 
move: (ax) => [[_ _ pe pf] pg].
have nn:= (cltS nN).
have lt1: e (cpred n) <o e n.
  move: nn; rewrite {1 4} pn => h; exact:(pf _ pnN h).
move: (odiff_pos lt1);move: lt1 => [le1 _]; move: (odiff_pr le1) => [oa pi] pj.
move:(pg _ nn) (pe _ nn) => pa pb.
rewrite -/a in oa.
have pnb: posnatp b by apply/posnat_ordinalp.
split => //.
have ax2:= (CNFb_p5 nN ax).
have od1 := OS_pow OS_omega oa.
have ocn := (proj32_1 pa).
have oc1 := (proj31 le1).
have pc:= (OS_CNFb nN ax2); rewrite pn in ax2.
move: (ord_rev_pred pj) =>[]; rewrite -/a => osa av.
have od2 := OS_pow OS_omega osa.
rewrite /CNFbvo (CNFq_p1 _ _ _ nN) /CNFp_value1.
rewrite (oprod2_succ pc (OS_prod2 od1 ocn)); apply: f_equal2; last exact.
rewrite (oprodA pc od1 ocn)/cantor_mon; apply: f_equal2; last exact.
rewrite   pi (opow_sum OS_omega oc1 oa) av (opow_sum OS_omega OS1 osa).
rewrite  (opowx1 OS_omega)(oprodA (OS_pow OS_omega oc1) OS_omega od2).
rewrite   (oprodA pc OS_omega od2); apply: f_equal2; last exact.
move: (the_cnf_p5 pnN ax2); rewrite - pn;set v := CNFbvo _ _ _; move => [vp dv].
by rewrite - dv (CNF_prod_pr2bis vp). 
Qed.


Lemma CNFp_p3 e c n:  CNFb_axo e c (csucc n) -> natp n ->
  exists p,
   [/\ CNFp_ax p n, CNFbvo e c (csucc n) = CNFpv p n,
     (forall i, i <c n -> (p  i) = J (e (csucc i) -o (e i) )  (c (csucc i))) &
       p n = J (e \0c) (c \0c) ].
Proof.
move => ax nN; move: n nN ax; apply: Nat_induction.
  move => h0; exists (fun z => J (e \0c) (c \0c)).
  move: (h0) => [[ha hb hc hd] he].
  move: (@succ_positive \0c) => qa.
  move: (hb _ qa) (hc _ qa)  (he _ qa) => a1 a2  a4.
  have qb: posnatp (c \0c) by apply/posnat_ordinalp. 
  have oc:= OS_prod2 (OS_pow OS_omega a1) (proj31_1 a2).
  split => //.
  - split; [ by move => i /clt0 | split; aww].
  - rewrite /CNFpv CNFp_0 succ_zero /CNFbvo; aw.
    by rewrite (CNFq_p3 (proj1 h0) (cltS NS0)) (oprod1r oc). 
  - by move => o /clt0.
move => n nN Hrec ax.
move: (CNFp_p2 ax (NS_succ nN) (@succ_nz n)) => [pa1 pa2 ->].
move: (Hrec (CNFb_p5 (NS_succ nN) ax)) => [p [ax3 -> h1  h3]] {Hrec}.
set sa := _ -o _; set sb := c (csucc n).
move: (proj32_1 pa1)=> osa.
move/posnat_ordinalp :(pa2) => /proj1/proj32_1 osb.
have of3:=(OS_succ (OS_prod2 (OS_pow OS_omega osa) osb)). 
pose p1 i :=  Yo (i = (csucc n)) (p n)  (Yo (i = n) (J sa sb) (p i)).
have aux: forall i, i <c csucc n -> 
      (i <> csucc n /\ (i = n \/ (i <> n /\ i <c n))).
  move => i h ; split; first by exact (proj2 h).
  move /(cltSleP nN): h => lt1.
  by case: (equal_or_not i n) => hc; [left | right].
exists p1;  split.
+ move: ax3 => [pa pb]; rewrite /p1; split; last by Ytac0.
  move => i /aux [ra rb]; Ytac0.
  case: rb=> rc; [ Ytac0; aw |case: rc=> [rc1 rc2]; Ytac0; fprops].
  split; aw; fprops. 
+ rewrite /CNFpv (CNFp_r  _ nN).
  have ->: CNFpv1 p1 n  = CNFpv1 p n.
    apply:(oprodf_exten nN) => i lin.
    move: (proj2(clt_leT lin (cleS nN))) (proj2 lin) => ha hb.
    by rewrite /p1 /cantor_pmon; Ytac0; Ytac0. 
  have of1: ordinalp (oopow (P (p n)) *o Q (p n)).
    rewrite h3; aw.
    exact:(CNFq_p0 (proj1 ax) (succ_positive  (csucc n))).
  rewrite /p1/cantor_pmon (Y_false (proj2(cltS nN))); Ytac0; Ytac0.
  by rewrite  (oprodA of1 (OS_CNFp1 (proj1 ax3) nN)); aw.
+ rewrite /p1;move => i /aux [ra rb]; Ytac0; case:rb=> rb.
    by Ytac0; rewrite rb/sa (cpred_pr1 (CS_nat nN)). 
   move: rb =>[rb1 rb2];Ytac0; fprops.
+ by rewrite /p1; Ytac0.
Qed.

Lemma CNFp_exists x: \0o <o x ->
  exists p n, [/\ CNFp_ax p n, natp n & x = CNFpv p n].
Proof.
move=> xp.
move: (the_cnf_p0_nz xp) => [cp cv].
move:(proj44 (proj1 cp)).
move: (cnf_size_nz cp); set n :=cnf_size _; move => [nN nv]; rewrite nv.
move => ax.
move: (CNFp_p3 ax nN) => [p [pa pb pc pd]]; exists p, n => //.
by rewrite - cv - pb /cnf_val nv. 
Qed.

Lemma CNFp_p4 p n:
   CNFp_ax p n -> natp n ->
   exists e c,
   [/\ CNFb_axo e c (csucc n), 
       CNFbvo e c (csucc n) = CNFpv p n,
       forall i, i <c n -> p i = J (e (csucc i) -o (e i)) (c (csucc i)) &
       p n = J (e \0c)(c \0c)].
Proof.
move=> [ax1 ax2] nN.
pose e :=  induction_term (fun i z => z +o (P (p i))) (P (p n)).
pose c i := Yo (i = \0c) (Q (p n)) (Q (p (cpred i))).
have pe1: P (p n) = (e \0c)  by rewrite /e induction_term0.
have pe2:  Q (p n) =  (c \0c) by rewrite/c ; Ytac0.
have pe: p n = J (e \0c) (c \0c) by rewrite - pe1 - pe2 (proj31 ax2).  
have hc i: natp i ->  e (csucc i) = e i +o (P (p i)).
   by move=> iN; rewrite /e induction_terms.
have ose i:  i<c n -> ordinalp (P (p i)).
  move => lin; move:(NS_lt_nat lin nN) => iN.
  exact:(proj32_1(proj32(ax1 i lin))).
have ose1 i:  i <=c n -> ordinalp (e i).
  move => lin; move:(NS_le_nat lin nN) => iN.
  move: i iN lin; apply: Nat_induction.
    by rewrite - pe1;case: ax2.
  move => i iN hr sin; rewrite (hc _ iN). 
  have lin:= (clt_leT (cltS iN) sin).
  exact: (OS_sum2 (hr (proj1 lin)) (ose _ lin)).
have pc i: i <c n -> p i = J(e (csucc i) -o e i)(c (csucc i)).
  move => lin; have iN:=(NS_lt_nat lin nN); rewrite /c (Y_false (@succ_nz i)).
  rewrite (cpred_pr2 iN) (hc _ iN) - {1} (proj31 (ax1 _ lin)).
  by rewrite  (odiff_pr1 (ose1 _ (proj1 lin)) (ose _ lin)). 
have pc2 i:i <c csucc n -> i <> \0c ->
     [/\ (cpred i <c n), e i = e (cpred i) +o (P (p (cpred i)))
         & c i = Q (p(cpred i))].
  move => lin inz.
  move: (cpred_pr (NS_lt_nat lin (NS_succ nN)) inz) => [pa pb].
  rewrite pb in lin; move /(cltSSP (CS_nat pa) (CS_nat nN)): lin => sin.
  by rewrite {2} pb - (hc _ pa) /c (Y_false inz).
have cv i: i <c csucc n -> exists2 j, j <=c n & c i = Q (p j).
  move => /(cltSleP nN) lin; rewrite /c; Ytac ei0.
    exists n; fprops.
  exists (cpred i)=> //; exact: (cleT (cpred_le (proj31 lin)) lin).
have axx: CNFb_axo e c (csucc n).
  have aux i: i <=c n -> posnatp (Q (p i)).
   by case/cle_eqVlt; [  move ->; case: ax2 | case/ax1].
  split; first split.
  - apply: ole_2omega.
  - by move => i /(cltSleP nN); apply: ose1.
  - by move => i /cv [j /aux/posnat_ordinalp/proj2 ok ->].
  - move => i iN ssin. 
    move: (pc2 _ ssin (@succ_nz i)); rewrite (cpred_pr2 iN); move => [sc sd _].
    have oe:=(ose1 _ (proj1 sc)).
    by move: (osum_Meqlt (proj32(ax1 _ sc)) oe); rewrite (osum0r oe) sd.
  - by move => i /cv [j /aux/posnat_ordinalp/proj1 ok ->].
move: (CNFp_p3 axx nN) => [p' [ ax' sv qa qc]].
have sv2: CNFbvo e c (csucc n) = CNFpv p n.
  rewrite sv /CNFpv qc pe; apply: f_equal.
  apply:(oprodf_exten nN) => i lin.
  by rewrite /cantor_pmon (qa _ lin) (pc _ lin).
by exists e, c.
Qed.

Lemma CNFp_unique p n p' n' :
   CNFp_ax p n  ->  CNFp_ax p' n' -> natp n -> natp n' ->
   CNFpv p n = CNFpv p' n' -> 
   n = n' /\  same_below p p' (csucc n).
Proof.
move=> ax1 ax2 nN n'N eq.
move: (CNFp_p4 ax1 nN) => [e1 [c1 [pa pb pc pe]]].
move: (CNFp_p4 ax2 n'N) => [e1' [c1' [pa' pb' pc' pe']]].
rewrite -pb -pb' in eq.
move: (CNFb_unique (NS_succ nN) (NS_succ n'N) pa pa' eq) => [sa sb].
have nn:= (csucc_inj (CS_nat nN) (CS_nat n'N) sa).
split; first exact.
rewrite - nn in pc' pe'.
move => i /(cltSleP nN); case/(cle_eqVlt)=> la.
  by rewrite la pe  pe'; move:(sb _ (succ_positive n)) => [-> ->].
rewrite (pc _ la) (pc' _ la).
move: (sb _ (clt_leT la (cleS nN))) => [-> _].
by move: (sb _ (cltSS la)) => [-> ->].
Qed.

Lemma osum2_commutes a b: ordinalp a -> ordinalp b ->
 ((a +o b = b +o a) <-> (exists c n m, 
  [/\ ordinalp c, natp n, natp m, a = c *o n & b = c *o m])).
Proof.
move=> oa ob; split; last first.
  move=> [c [n [m [oc nN mN av bv]]]].
  have on: ordinalp n by apply: OS_cardinal; fprops.
  have om: ordinalp m by apply: OS_cardinal; fprops.
  rewrite av bv - (oprodD on om oc) - (oprodD om on oc).
  by rewrite (osum2_2int nN mN)(osum2_2int mN nN) csumC.
move=> hc.
case: (ozero_dichot oa) => az.
  exists b, \0c, \1c;split;fprops.
    by rewrite az (oprod0r).
  by rewrite (oprod1r ob).
case: (ozero_dichot ob) => bz.
  exists a, \1c, \0c;split;fprops.
    by rewrite (oprod1r oa).
  by rewrite bz (oprod0r).
case: (oleT_ell (OS_degree oa) (OS_degree ob)); last first => cab.
    case: (nesym (proj2 bz)); apply:(osum2_a_ab oa ob).
    rewrite hc;apply: (ord_negl_p7 bz az cab).
  case: (nesym (proj2 az)); apply:(osum2_a_ab ob oa).
  rewrite - hc;apply: (ord_negl_p7 az bz cab).
move: (the_cnf_p0_nz az) => [axa av]. 
move: (the_cnf_p0_nz bz) => [axb bv].
move:(cnf_size_nz axa) (cnf_size_nz axb) cab.
rewrite (odegree_of_nz (nesym (proj2 az))) (odegree_of_nz (nesym (proj2 bz))).
set x := the_cnf a; set y := the_cnf b.
set sa := (cnf_size x); set sb := cnf_size y.
move=> [ua ub][uc ud] sd.
rewrite -/x in axa; rewrite -/y in axb.
set s1:= cnf_nc y (cnf_lc x).
set s2 := cnf_nc x (cnf_lc y).
move: (posnat_lc axa) (posnat_lc axb) => p1 p2.
move: (cnf_nc_prop axa (proj1 p2)) (cnf_nc_prop axb (proj1 p1)).
rewrite -/s1 -/s2; move => [ra2 rb2 rc2 rd2 re2] [ra1 rb1 rc1 rd1 re1].
have s1s2: s1 = s2.
  apply:(cnf_val_inj ra1 ra2).
  rewrite - (CNF_sum_pr3 axa axb sd) - (CNF_sum_pr3 axb axa (esym sd)).
  by rewrite /x/y av bv hc.
have dxdy: domain x = domain y by rewrite -rb1 - rb2 s1s2.
set s3 :=  Lg (domain x) (cnf_c (Vg x) (cnf_size x) (J (cnf_degree x) \1c)).
move: (nesym(proj2(succ_positive sa))); rewrite - ub => dxz.
have oexp3  i: inc i (domain x) -> oexp s3 i = oexp x i.
  by move => h;rewrite/s3/oexp/cnf_c LgV//; Ytac lt1; aw;trivial; rewrite lt1.
have aux: cnfp_nz s3.
  rewrite/s3;split; last by move/domain_set0_P;aw.
  move/cnfpP:(proj1 axa) => [qa qb qc qd].
  apply/cnfpP; split ; aww.
    move => i idx;rewrite LgV// /cnf_c; Ytac w;fprops.
    split;aww;[exact:(OS_cnf_degree axa) | exact PN1].
  move => i iN lin;move:(qd i iN lin) => r.
  move/(NltP qb):(clt_ltT (cltS iN) lin)=> idx.
  move/(NltP qb): lin=> lin.
  by rewrite -/s3 (oexp3 _ idx)(oexp3 _ lin).
have ds3: domain s3 = domain x by rewrite /s3 Lgd.
have ss3: cnf_size s3 = cnf_size x by rewrite /cnf_size ds3.
move:(cnf_size_nz_bis axa) => qq.
have lcs3: cnf_lc s3 = \1c.
  by rewrite/s3/cnf_lc/ocoef ss3/cnf_c LgV//; Ytac0; aw.
have dgcs3: cnf_degree s3 = cnf_degree x.
  by  rewrite /cnf_degree ss3; apply: oexp3.
have vs3 i: inc i (domain x) -> i <> cnf_size x ->  Vg x i = Vg s3 i.
  by move => ha hb; rewrite/s3 LgV// /cnf_c; Ytac0.
have  eqx: x =  (cnf_nck s3 (cnf_lc x)).
  move/cnfpP:(proj1 axa) => [qa _ qc _].
  rewrite /cnf_nck dgcs3 lcs3 ds3  ss3(cprod1l (CS_nat(proj1 p1))).
  apply: fgraph_exten; aww => i idx;rewrite LgV//.
  rewrite /cnf_c; Ytac lt1; last by apply:vs3.
  by rewrite - (proj31 (qc  i idx)) lt1.
have  eqy: y =  (cnf_nck s3 (cnf_lc y)).
  rewrite /cnf_nck dgcs3 lcs3 ds3 ss3 (cprod1l (CS_nat(proj1 p2))).
  move/cnfpP:(proj1 axb) => [qa _ qc _].
  apply: fgraph_exten; aww. 
  rewrite dxdy => i idy;rewrite LgV // /cnf_c; Ytac lt1.
  have ->: cnf_degree x = cnf_degree y by  rewrite/cnf_degree sd. 
    by rewrite - (proj31 (qc  i idy)) lt1 /cnf_size dxdy.
  move: (idy); rewrite - dxdy => idx.
  rewrite -(vs3 _ idx lt1).
  move: (f_equal (Vg ^~ i) s1s2); rewrite/s1/s2/cnf_nc/cnf_c !LgV//.
  by rewrite{1}/cnf_size -dxdy -/(cnf_size x); Ytac0; Ytac0.
exists (cnf_val s3), (cnf_lc x),(cnf_lc y).
split.
- exact: (OS_cnf_val (proj1 aux)).
- exact: (proj1 p1).
- exact: (proj1 p2).
- by rewrite (CNF_prod_pr1 aux p1) - av - eqx.
- by rewrite (CNF_prod_pr1 aux p2) -bv - eqy.
Qed.



Definition oprod_comm x y :=  (x *o y = y *o x).

Lemma cnf_nat_prop a: cnfp_nz a ->  cnf_size a = \0c -> oexp a \0c = \0c ->
   (cnf_val a) <o omega0 /\ cnf_val a = ocoef a \0c.
Proof.
move => cnz ha hb.
move:(cnf_size_nz cnz) => [qa qb].
have oda:= proj2(cnf_size_nz_ter cnz).
move: (proj2 (proj44 (proj1 cnz)) _ oda)=> lp.
move: (proj43 (proj1 (proj44 (proj1 cnz)))  _ oda)  => xf.
move:(proj32_1 lp) => od.
have eq0: cantor_mon omega0 (oexp a) (ocoef a) \0c = ocoef a \0c.
  by rewrite/cantor_mon hb  opowx0 (oprod1l od).
by rewrite /cnf_val/CNFbvo/CNFbv qb ha succ_zero osum_f1 eq0//.
Qed.
  

Lemma oprod2_comm1  a b (x := cnf_val a) (y:= cnf_val b):
  cnfp_nz a -> cnfp_nz b ->
  oexp b \0c = \0o -> \0o <o oexp a \0c -> 
  oprod_comm x y -> y = \1o.
Proof. 
move => anz bnz ha hb eq1.
move: (cnfp_prod_gen anz bnz).
move: (cnfp_shift_expo (proj1 anz)  (OS_cnf_degree bnz)).
set u := cnf_shift_expo a (cnf_degree b).
set v := cnf_prod_gen a b.
move => ou ov.
have eq2: cnf_val v = cnf_val u.
  by rewrite -(CNF_prod_pr5 bnz anz hb)  - (CNF_prod_pr6 anz bnz ha).
move:(cnf_val_inj ov ou eq2) => eq3.
move: (proj42 (proj1 anz)) (proj42 (proj1 bnz)) => aN bN.
move: (cnf_size_nz bnz) => [qa qb].
have pdy: (domain b -c \1c) = cnf_size b.
  by rewrite - (cpred_pr4 (CS_nat bN)) qb (cpred_pr1 (CS_nat qa)).
move: (f_equal domain eq3).
rewrite/u/v/cnf_prod_gen/cnf_shift_expo /cnf_nm Lgd.
rewrite /cnf_nck /cnf_ns ! Lgd => eq4.
move: (eq4); rewrite pdy - {2}(csum0r (CS_nat aN)).
move/(csum_eq2l aN qa NS0) => eq5.
rewrite /y (proj2 (cnf_nat_prop bnz eq5 ha)).
move:(cnf_size_nz_bis anz) => qe.
have qf: cnf_size a <c domain a  by apply/NltP.
move:(f_equal (Vg^~ (cnf_size a)) eq3).
rewrite/u/v /cnf_prod_gen /cnf_nm /cnf_shift_expo !Lgd eq4.
rewrite (LgV qe) (LgV qe) /cnf_m /cnf_nck /cnf_c; Ytac0.
rewrite  (LgV qe); Ytac0 => /pr2_def.
move:(posnat_lc anz) => [q1 /proj2/nesym q2].
move:(proj1 (posnat_lc bnz)); rewrite/(cnf_lc) eq5=> aux.
rewrite -/(cnf_lc a)  - {2} (cprod1r  (CS_nat q1)).
by move/(cprod_eq2l q1 aux NS1  q2). 
Qed.

Lemma oprod2_comm2 a mu 
  (x:= cnf_val a) (y := (oopow mu) *o x):
  cnfp_nz a -> \0o <o oexp a \0c -> ordinalp mu ->
  (cnf_degree a) +o mu = mu +o (cnf_degree a) -> oprod_comm x y.
Proof.
move=> anz vp om c1.
have xp:= OS_cnf_valp anz.
have ox := proj32_1 xp.
have oe := (OS_cnf_degree anz).
have oomu:= OS_oopow om.
case: (ozero_dichot om) => muz.
  by rewrite /y muz oopow0 (oprod1l ox).
move: (ord_rev_pred muz); set t:= _ -o _; move=> [ot tv].
have oot:= OS_oopow ot.
have oot1:= OS_prod2 OS_omega oot.
have ooe := OS_oopow oe.
have oo := OS_omega.
rewrite /oprod_comm - (oprodA oomu ox ox) (CNF_prod_pr4 anz anz vp).
rewrite (oprodA oomu ooe ox) - (opow_sum oo om oe) - c1 (opow_sum oo oe om).
rewrite /y /oopow tv (opow_sum oo OS1 ot) (opowx1 OS_omega).
rewrite (oprodA ox oot1 ox) (oprodA ox oo oot) (CNF_prod_pr2 anz).
by rewrite - (oprodA ooe oo oot).
Qed.


Definition oprod2_comm_P4 x y :=
  exists z gamma c1 c2,
  [/\ cnfp_nz z, \0o <ooexp z \0c, ordinalp gamma & 
  [/\ natp c1, natp c2,
  x = cnf_val z,
  cnf_degree z = gamma *o c1 &
  y = oopow (gamma *o c2) *o x]].

Lemma oprod2_comm3 x y:  oprod2_comm_P4 x y ->  oprod_comm x y.
Proof.
move=>  [a [g [c1 [c2 [ ]anz vp og[c1N c2N xv dx yv]]]]].  
rewrite yv xv.
have oc1:= OS_nat c1N.
have oc2:= OS_nat c2N.
apply:(oprod2_comm2 anz vp (OS_prod2 og oc2)).
rewrite dx - (oprodD oc1 oc2 og) - (oprodD oc2 oc1 og).
by rewrite (osum2_2int c1N c2N) (osum2_2int c2N c1N) csumC.
Qed.

Lemma oprod2_comm4  a b 
  (x := cnf_val a) (y:= cnf_val b):
  cnfp_nz a -> cnfp_nz b -> 
  \0o <o (oexp a \0c) -> \0o <o oexp b \0c -> 
  oprod_comm x y ->
  (oprod2_comm_P4 x y \/ oprod2_comm_P4 y x).
Proof.
move=> anz bnz tcX tcY cr.
move: (cnfp_shift_expo (proj1 anz)  (OS_cnf_degree bnz)).
move: (cnfp_shift_expo (proj1 bnz)  (OS_cnf_degree anz)).
set u := cnf_shift_expo _ _.
set v := cnf_shift_expo _ _.
move => ou ov.
have eq2: cnf_val u = cnf_val v.
  by rewrite -(CNF_prod_pr5 bnz anz tcX)  - (CNF_prod_pr5 anz bnz tcY).
move:(cnf_val_inj ou ov eq2) => eq3.
move: (f_equal domain eq3). 
    rewrite/u/v /cnf_shift_expo !Lgd=> dadb.
move:(f_equal (Vg ^~ (cnf_size a)) eq3).
move:(cnf_size_nz_bis anz) => pa.
have pb: inc (cnf_size a) (domain b) by ue.
rewrite/u/v/cnf_shift_expo (LgV pb) (LgV pa) -/(cnf_degree a).
rewrite /cnf_size- dadb -/(cnf_size b) -/(cnf_degree b) => /pr1_def csd.
move/(osum2_commutes (OS_cnf_degree anz) (OS_cnf_degree bnz)): csd.
move => [c [c1 [c2 [oc c1N c2N p1v p2v]]]].
move:(NS_diff c1 c2N) (NS_diff c2 c1N).
set c3:= c2 -c c1; set c4:= c1 -c c2 => c3N c4N.
move:(OS_nat c1N)(OS_nat c2N) => oc1 oc2.
move:(OS_nat c3N)(OS_nat c4N) => oc3 oc4.
have disj: ((c1 +c c3 = c2 /\ c4 = \0c) \/ (c2 +c c4 = c1 /\ c3 = \0c)).
  case: (NleT_ee c1N c2N) => le1.
   by  left; split; [ apply: (cdiff_pr le1) | apply: (cdiff_wrong le1) ].
   by right; split; [ apply: (cdiff_pr le1) | apply: (cdiff_wrong le1) ].
have [t [ot tp1 tp2]]: exists t, [/\ ordinalp t, c1 = t +o c4 & c2 = t +o c3].
   move:(esym (osum0r oc1))(esym (osum0r oc2)) => sa sb.
   move:(esym (osum2_2int c1N c3N))(esym (osum2_2int c2N c4N)) => sc sd.
   by case: disj;move => [<- ->]; [exists c1 | exists c2]; split.
move: (p1v); rewrite tp1 (oprodD ot oc4 oc) => p1.
move: (p2v); rewrite tp2 (oprodD ot oc3 oc) => p2.
have occ3: ordinalp (c *o c3) by fprops.
have occ4: ordinalp (c *o c4) by fprops.
have sYv: (oopow (c *o c3)) *o x = (oopow (c *o c4)) *o y.
  rewrite - {1} (CNF_prod_pr0 (proj1 anz) occ3).
  rewrite - (CNF_prod_pr0 (proj1 bnz) occ4).
  congr cnf_val. 
  move:eq3; rewrite /u/v/cnf_shift_expo dadb => aux.
  apply:Lg_exten => i ida.
  move:(f_equal (Vg ^~ i) aux); rewrite (LgV ida)(LgV ida) => eq4.
  apply: f_equal2; [symmetry |  by rewrite(pr2_def eq4)].
  move:(OS_prod2 oc ot) (OS_prod2 oc oc4) (OS_prod2 oc oc3) => o1 o2 o3. 
  move: (proj42 (proj1 anz)) => daN.
  have lia: i <c domain a by  apply/NltP. 
  move:(proj42(proj1(proj44(proj1 anz))) _ lia)=> oa.
  rewrite - dadb in lia.
  move:(proj42(proj1(proj44(proj1 bnz))) _ lia)=> ob.
  move:(pr1_def eq4); rewrite p1 p2.
  rewrite - {1} (osumA o1 o2 ob) - (osumA o1 o3 oa).
  by move/(osum2_simpl (OS_sum2 o2 ob) (OS_sum2 o3 oa) o1).
case: disj; move=> [pr1 pr2].
  left; exists a, c,c1, c3.
  rewrite sYv pr2 oprod0r  oopow0 (oprod1l (OS_cnf_val (proj1 bnz))).
  by split;last split ;try reflexivity.
right; exists b ,c, c2, c4.
rewrite - sYv pr2 oprod0r oopow0 (oprod1l (OS_cnf_val (proj1 anz))). 
by split; last split; try reflexivity.
Qed.

Lemma oprod2_comm5 a b 
  (x := cnf_val a) (y := cnf_val b):
  cnfp_nz a -> cnfp_nz b ->
  oexp a \0c = \0o -> oexp b \0c = \0o -> cnf_size a = \0c -> oprod_comm x y ->
  (x = \1o \/ (x <o omega0 /\ y <o omega0)).
Proof.
move=> anz bnz limX limY sz cxy.
move:(cnf_nat_prop anz sz limX)=> [fx xv].
have bN:= (proj42 (proj1 bnz)).
case: (equal_or_not (cnf_size b) \0c) => sbz.
   right; split; [ exact | exact: (proj1 (cnf_nat_prop  bnz sbz limY))].
move: (cnfp_prod_gen anz bnz).
move: (cnfp_prod_gen bnz anz).
move:(CNF_prod_pr6 anz bnz limY).
move:(CNF_prod_pr6 bnz anz limX).
set u := cnf_prod_gen a b.
set v := cnf_prod_gen b a.
move => eq1 eq2 ov ou.
have eq3: cnf_val u = cnf_val v by rewrite - eq1 - eq2. 
move:(cnf_val_inj ou ov eq3) => eq4.
left; rewrite /x xv; clear eq1 eq2 eq3 cxy.
move:(cnf_size_nz bnz) => [qa qb].
have pdy: (domain b -c \1c) = cnf_size b.
  by rewrite - (cpred_pr4 (CS_nat bN)) qb (cpred_pr1 (CS_nat qa)).
have db0: domain b +c \0c = domain b. rewrite csum0r // qb; fprops.
move: (proj2(cnf_size_nz anz)); rewrite sz succ_zero => da.
have da1: domain a -c \1c = \0c by rewrite da cdiff_nn.
have [zdb lzdb]  := cnf_size_nz_ter bnz.
have [zda lzda]  := cnf_size_nz_ter anz.
have eq1: (domain a +c (domain b -c \1c)) = domain b.
  by rewrite pdy da csumC qb - (csucc_pr4 (CS_nat qa)).
move:(f_equal (Vg ^~ \0c) eq4).
rewrite/u/v/cnf_prod_gen/cnf_nm !Lgd.
rewrite/cnf_ns /cnf_nck/cnf_m  eq1 da1  db0 (LgV zdb) (LgV zdb)  (LgV zda).
rewrite (LgV zdb);Ytac0; Ytac0.
rewrite /cnf_c sz;Ytac0; Ytac0 => /(f_equal Q); aw.
move/cnfpP: (proj1 bnz) => /proj43 h.
move: (proj33 (h _ zdb))=>[cN /proj2/nesym cp].
rewrite -(cprod1l (CS_nat cN)).
move/ (cprod_eq2r cN (proj1 (posnat_lc anz)) NS1 cp).
by rewrite/cnf_lc sz.
Qed.

Definition CNF_npec (px py: fterm) n m :=
  fun i => Yo (i = (csucc n +c m)) (px (csucc n)) 
              (Yo (i = n) (J (P (px n)) ((Q (px n) *o (Q (py m)))))
                  (Yo (i <c n) (px i) (py (i -c (csucc n))))).

Lemma CNFp_pg  px n py m 
  (pz := CNF_npec px py n m)
  (lx := Q (px (csucc n))) (ly := Q (py m)):
  CNFp_ax px (csucc n) -> CNFp_ax py m -> natp n -> natp m ->
  (CNFp_ax pz (csucc n +c m) /\ 
  (lx *o (CNFpv1 px (csucc n))) *o (ly *o (CNFpv1 py m)) 
   = lx *o CNFpv1 pz (csucc n +c m)).
Proof.
move=> ax ay nN mN.
move:(ax) (ay) => [p1 p2] [p1' p2']. 
have snN:= NS_succ nN.
have ltnsn:=(cltS nN).
have lenn:= cleR (proj32_1 ltnsn).
have cnn:=(CS_nat nN). 
have axz: CNFp_ax pz (csucc n +c m).
  have aux: forall i,  i <c csucc n +c m -> i <> n ->  ~ i <c n ->
    (i -c (csucc n) <c m).
    move => i pa.
    case: (cleT_ell cnn (proj31_1 pa)) => //; first by move => ->.
    move => /(cleSltP nN) => ha _ _.
    rewrite csumC in pa; have hh:= (NS_sum mN snN). 
    exact: (cdiff_Mlt mN (NS_lt_nat pa hh) ha pa).
  split; last by rewrite /pz /CNF_npec; Ytac0. 
  move => i isn; rewrite /pz /CNF_npec.  
  move: (proj2 isn) => ha; Ytac0; clear ha.
  Ytac h0.
    move:(p1 _ ltnsn)=> [qa qb qc]; split; aww. 
    move:(proj33 p2') => qd.
    by rewrite (oprod2_2int (proj1 qc) (proj1 qd)); apply:PN_prod.
  Ytac h3; first  exact: (p1 _ (clt_leT h3 (proj1 ltnsn))).
  exact: (p1' _ (aux _ isn h0 h3)).
split; first by exact.
have ax':= (proj1 ax).
have ox:=(OS_CNFp1 ax' snN).
have oy:=(OS_CNFp1 (proj1 ay) mN).
move:(OS_nat (proj1(proj33 p2))) (OS_nat (proj1(proj33 p2'))) => ocx ocy.
rewrite - (oprodA ocx ox (OS_prod2 ocy oy)) (oprodA ox ocy oy); apply: f_equal.
rewrite (CNFp_A snN mN (proj1 axz)).
apply: f_equal2; last first.
  apply: (oprodf_exten mN) => i im.
  rewrite /CNFp_value1/pz/cantor_pmon/CNF_npec.
  have iN:= (NS_lt_nat im mN).
  move: (proj2 (csum_Mlteq snN im));rewrite (csumC m).
  move:(csum_Mlteq nN (succ_positive i)).
  rewrite (csum0l cnn) (cdiff_pr1 iN snN) (csum_nS _ nN).    
  rewrite - (csum_Sn _ iN); move => [sa sb] sc. 
  by move:(cleNgt sa) => sa'; repeat Ytac0. 
have nn1: n <c (csucc n) +c m.
  rewrite (csum_Sn _ nN); apply /(cltSleP (NS_sum nN mN)).
  apply: (csum_M0le _ cnn).
have nn2: ~(n = csucc n +c m) by move: (proj2 nn1).
move: (axz) => [p7 p8]. 
move:(p7 _  nn1) => [ha hb hc].
move: (p1 _ ( ltnsn)) => [ha' hb' hc'].
move: (OS_CNFp0 (proj1 ax) (cltS nN)). 
rewrite (CNFp_r _ nN)(CNFp_r  _ nN).
rewrite /cantor_pmon (CNFp_pr1 hb hc)(CNFp_pr1 hb' hc') => o2.
rewrite -(oprodA (OS_CNFp1r ax' snN (proj1 ltnsn)) o2 ocy); apply: f_equal2.
  apply: (oprodf_exten nN) => i lin.
  rewrite / CNFp_value1 /pz/CNF_npec /cantor_pmon.
  move:(proj2 (clt_leT lin (proj1 nn1))) (proj2 lin) => lt1 ne1.
  by repeat  Ytac0.
move: (OS_nat (proj1 (proj33 p2'))) (OS_nat (proj1 hc')) => ory orx.
rewrite /CNFp_value2/pz/CNF_npec;repeat Ytac0; aw.
by rewrite (oprodA (OS_succ (OS_oopow (proj32_1 hb'))) orx ory).
Qed.


Definition CNFp_ax4 (p:fterm) n x :=
  [/\ CNFp_ax p (csucc n), natp n, (P (p (csucc n))) = \0c &
    x = (Q (p (csucc n))) *o CNFpv1 p (csucc n)].


Lemma CNFp_ph px n py m  x y
  (pz1 := CNF_npec px py n (csucc m)) (pz2 := CNF_npec py px m (csucc n)):
  CNFp_ax4  px n x  -> CNFp_ax4 py m y ->
  oprod_comm x y -> 
   [/\ (same_below pz1 pz2 (csucc n +c csucc m)),
    ( n = m -> x = y) &
    ( m <c n -> exists pz p z,
       [/\ CNFp_ax4 pz p z, x = z *o y, z *o y = y *o z & p <c n])].
Proof.
move=> [ ax nN exn xv] [ ay mN eym yv].
move:(NS_succ mN)(NS_succ nN) => smN snN.
have sc1:= (csumC (csucc m)(csucc n)).
have eq0:= (erefl(csucc n +c csucc m)).
move: (CNFp_pg ax ay nN smN) (CNFp_pg ay ax mN snN). 
rewrite -{1} xv -{1} yv; move => [at1 eq1].
rewrite -{1} xv -{1} yv; move => [at2 eq2].
rewrite /oprod_comm eq1 eq2; clear eq1 eq2.
move: (CNFp_unique at1 at2 (NS_sum snN smN) (NS_sum smN snN)); rewrite /CNFpv.
set z1 := CNFpv1 _ _; set z2 := CNFpv1 _ _.
rewrite /CNF_npec sc1 (Y_true eq0) (Y_true eq0) exn eym oopow0.
move:(proj33(proj2 ax)) (proj33 (proj2 ay)) => pnu pnv.
move: (OS_nat (proj1 pnu))(OS_nat (proj1 pnv)) => oq1 oq2.
rewrite (oprod1l oq1) (oprod1l oq2).
rewrite -/(CNF_npec px py _ _) - {2 3}sc1 -/(CNF_npec py px _ _) -/pz1 -/pz2.
move => eq1 eq3; move: (proj2 (eq1 eq3)) => me; clear eq1 eq3.
move:(true_below_rec (NS_sum snN smN) me) => [me1 me2].
split; first exact.
  move => enm; rewrite - enm in   oq2 me1 me2.
  rewrite xv yv - enm.
  apply: f_equal2.
    by move: me2; rewrite /pz1/pz2 /CNF_npec - enm;Ytac0;Ytac0; move ->.
  apply: (oprodf_exten snN) => i lt1; rewrite /cantor_pmon.
  suff: px i = py i  by move ->.
  have ha:= (csum_Mlteq snN lt1).
  have iN:= (NS_lt_nat lt1 snN).
  have eq2:= (cdiff_pr1 iN snN).
  have l1 :=  (Nsum_Mle0 i nN).
  have [hb1 hb2]: n <c i +c (csucc n).
    by rewrite (csum_nS _ nN);apply/(cltSleP((NS_sum iN nN))).
  move: (cleNgt hb1) => hb3.
  move: (me1 _ ha); move:(proj2 ha)=> hb.
  by rewrite/pz1/pz2/CNF_npec -enm; repeat Ytac0; rewrite eq2.
move=> ltnm. 
move: me2; rewrite /pz1/pz2 /CNF_npec - sc1; Ytac0; Ytac0 => eqd.
have snmnz: n -c m <> \0c by apply: (cdiff_nz ltnm).
move: ltnm => [lenm nenm].
move: (cdiff_pr lenm) (NS_diff m nN) =>  snmp snmN.
move: (cpred_pr snmN snmnz); set p := cpred (n -c m); move=> [pN pv1].
have spN: natp (csucc p) by fprops.
set nm := (csucc n) +c (csucc m).
have nmN:= NS_sum snN smN.
have spm:csucc p +c csucc m = csucc n.
  by rewrite (csum_nS _ mN) csumC -pv1 snmp.
have spm1: p +c csucc m = n. 
  by rewrite (csum_nS _ mN) csumC - (csum_nS _ pN) -pv1.
have nsm: (n -c csucc m) = p by apply: cdiff_pr2 => //.
have pltn: p <c n by rewrite - spm1; apply: (csum_M0lt pN (@succ_nz m)).
pose pz i:= Yo (i = csucc p) (px (csucc n)) (px (i +c (csucc m))).
set z:= Q (px (csucc n)) *o CNFpv1 pz (csucc p).
have axz: (CNFp_ax4 pz p z).
  move:(ax) =>[ a1 a2].
  have aux: forall i, i<c csucc p -> i +c (csucc m) <c (csucc n).
    move => i isp.
     by move: (csum_Mlteq smN isp); rewrite spm.
  hnf; rewrite /z  /pz; Ytac0.  
  split; [ split; last by Ytac0 | exact  | exact | reflexivity ].
  move => i lip;move:(lip) => [_ h]; Ytac0; exact:(a1 _ (aux _ lip)).
set eca:= CNF_npec pz py p (csucc m).
have eqa: forall i, i <c (csucc n) -> eca i = px i.
  move => i ism; rewrite /eca. 
  have ha:=(csum_Mlteq smN ism).
  move: (me1  _ ha); rewrite /pz /pz1/pz2 /CNF_npec spm sc1.
  rewrite 2!(Y_false (proj2 ha))  (Y_false (proj2 ism)).
  have iN:= (NS_lt_nat ism snN).
  have li1:= (Nsum_Mle0 i mN).
  move/(cltSleP (NS_sum iN mN)):li1.
  rewrite - (csum_nS _ mN) => - [ha4 ha5].
  have ha7 := cleNgt ha4.
  have h3:= (proj2 (cltS pN)).
  repeat Ytac0.
  rewrite (cdiff_pr1 iN smN).
  case: (cleT_ell (proj31_1 ism) (CS_nat pN)) => cip.
  + by have ht:= (cleNgt lenm); rewrite cip spm1; repeat Ytac0. 
  + move:(csum_Mlteq smN cip); rewrite spm1 => ha1.
    have ha6:= (proj2 (clt_leT cip (cleS pN))).
    by move:(proj2 cip)(proj2 ha1) => ha2 ha3; repeat Ytac0.
  + move:(csum_Mlteq smN cip); rewrite spm1; move => [/cleNgt hb1 hb2].
    have ->: (i +c csucc m) -c csucc n = i -c csucc p.
      move/(cleSltP pN): cip => lt2.
      rewrite - {1} (cdiff_pr lt2) (csumC (csucc p)) - csumA spm.
      apply: (cdiff_pr1 (NS_diff (csucc p) iN) snN).
    move: cip => [/cleNgt ha8 ha9].
    by repeat Ytac0.
set ecb:=(CNF_npec py pz m (csucc p)). 
have eqb i: i <c (csucc n) -> px i = ecb i.
  move =>  iln; rewrite /ecb.
  have ha:=(clt_leT iln (csum_M0le (csucc m) (CS_succ n))).
  move: (me1 _ ha).
  rewrite /pz1/pz2/pz /CNF_npec  sc1.
  move: (proj2 iln)  (proj2 ha) => nin nin2.
  rewrite (csumC (csucc m)(csucc p)) spm; repeat Ytac0.
  case (equal_or_not i n) => ein.
    have h3:= (proj2 (cltS pN)); have h:= (cleNgt lenm).
    by move => _ ;rewrite ein nsm spm1;  repeat Ytac0.
  have lin1: i <c n by split; [  apply/(cltSleP nN) | exact ].
  repeat Ytac0.
  case : (cleT_ell (proj31_1 lin1) (CS_nat mN)) => cim.
  + by rewrite cim; repeat Ytac0. 
  + by move: (proj2 cim) => hb; repeat Ytac0.
  +  have smi: csucc m <=c i by move/(cleSltP mN): cim.
     move => _.
     rewrite (csumC (i -c csucc m)) (cdiff_pr smi). 
     case: (equal_or_not (i -c csucc m) (csucc p)) => hu.
       by move: (cdiff_pr smi) nin; rewrite hu csumC spm => ->; case.
     move: cim => [/cleNgt hb hc].
     by repeat Ytac0.
move: (axz)=> [az1 az2 az3 cs4].
move: (proj2(CNFp_pg az1 ay pN smN)).
have ->: CNFpv1 eca (csucc p +c csucc m) = CNFpv1 px (csucc n).
  rewrite spm; apply:(oprodf_exten snN) => i /eqa. 
  by rewrite /cantor_pmon; move ->.
  rewrite - yv  {1 3} /pz (Y_true (erefl _)) - [RHS] xv -/z => eqc.
move:(proj2(CNFp_pg ay az1 mN spN)).
have ->: CNFpv1 ecb (csucc m +c csucc p)  = CNFpv1 px (csucc n).
  rewrite csumC spm; apply:(oprodf_exten snN) => i /eqb.
  by rewrite/cantor_pmon => ->.
rewrite - cs4- {1} yv - eqd - xv => sc.
by exists  pz, p, z; rewrite eqc sc. 
Qed.

                                                      
Definition oprod2_comm_P1 x y :=
  exists c n m,
    [/\ ordinalp c, natp n, natp m, x = c ^o n & y = c ^o m].

Lemma oprod2_comm6 px n x py m y:
  CNFp_ax4 px n x -> CNFp_ax4 py  m y ->
  oprod_comm x y -> oprod2_comm_P1 x y.
Proof.
move => h1 h2 h3.
move:(h1)(h2) => [_ nN _ _] [_ mN _ _].
move:(NS_sum nN mN);set p := n +c m => pN.
have aux: n +c m <=c p by rewrite /p; fprops.
move: p pN aux => p pN aux.
move: p pN px n x py m y h1 h2 h3 aux nN mN.
have ores: forall px n x, CNFp_ax4 px n x -> ordinalp x.
  move=> px n x [[ax1 /proj33/proj1/OS_nat o1] nN _ ->].
  exact: (OS_prod2 o1 (OS_CNFp1 ax1 (NS_succ nN))).
have special: forall px n x, CNFp_ax4 px n x -> oprod2_comm_P1 x x.
  move=> px n x /ores h; move: (opowx1 h) => p1.
  exists x; exists \1c; exists \1c; split;fprops.
apply: Nat_induction.
  move=> px n x py m y pa pb h1 h2 nN mN.
  move: (cle0 h2); rewrite -(osum2_2int nN mN) => nmz.
  move: (osum2_zero (OS_nat nN) (OS_nat mN) nmz) => [nz mz].
  rewrite - mz in nz;move: (CNFp_ph pa pb h1) => [_  ok _].
  move: (ok nz) => ok0; rewrite - ok0; apply: special pa.
move=> sm smN hrec px n x py m y pa pb h1 h2 nN mN.
wlog:px py n m x y pa pb h1 h2 nN mN / (m <=c n).
  move=> aux.
  case: (cleT_el (CS_nat mN) (CS_nat nN)). 
    apply: aux  pa pb h1 h2 nN mN.
  symmetry in h1; rewrite csumC in h2.
  move=> [lemn _]; move: (aux _ _ _ _ _ _  pb pa h1 h2 mN nN lemn).
  move => [z [xe [ye [oz xeN yeN eq1 e2]]]].
  exists z; exists ye; exists xe; split => //.
move: (CNFp_ph pa pb h1) => [_ pc pd].
move=> lenm; case: (equal_or_not m n) => dnm. 
 symmetry in dnm;rewrite -(pc dnm); apply: (special _ _ _  pa).
have ltnm: m <c n by split.
move: (pd ltnm) => [pZ [p [z [pe xv h3 ltpn]]]].
have pN: natp p by move: ltpn => [lepn _];apply:  (NS_le_nat lepn nN).
move: (csum_Mlteq  mN ltpn) => r1.
move /(cltSleP smN): (clt_leT r1 h2) => le1.
move: (hrec _ _ _ _ _ _  pe pb h3 le1 pN mN)=> xx.
move: xx =>[t [xe [ye [oz xeN yeN eq1 e2]]]].
exists t; exists (xe +c ye); exists ye; split;fprops.
have oxe: ordinalp xe by apply: OS_cardinal; fprops.
have oye: ordinalp ye by apply: OS_cardinal; fprops.
by rewrite xv eq1 e2 - (opow_sum oz oxe oye) (osum2_2int xeN yeN).
Qed.

Theorem oprod2_comm x y: ordinalp x -> ordinalp y ->
   ((oprod_comm x y) <->
   (x = \0o \/ y = \0o \/ (oprod2_comm_P4 x y \/  oprod2_comm_P4 y x) \/
   (x <o omega0 /\ y <o omega0) \/ oprod2_comm_P1 x y)).
Proof.
move=> ox oy.
split; last first.
  rewrite /oprod_comm.
  move => h; case: h; first by move=> ->; rewrite (oprod0r) (oprod0l).
  case; first by move=> ->; rewrite (oprod0r) (oprod0l).
  case; first by case ;[ apply: oprod2_comm3 |  symmetry; apply: oprod2_comm3 ].
  case.
    move => [/olt_omegaP xN /olt_omegaP yN].
    by rewrite (oprod2_2int xN yN)(oprod2_2int yN xN) cprodC.
  move=> [c [n [m [oc nN mN -> ->]]]].
  move:(OS_nat nN) (OS_nat mN) => on om.
  rewrite - (opow_sum oc on om) - (opow_sum oc om on).
  by rewrite (osum2_2int nN mN)(osum2_2int mN nN) csumC.
move=> h.
case: (ozero_dichot ox) =>  xnz; first by left.
case: (ozero_dichot oy) =>  ynz; [by right;left | right; right].
case: (equal_or_not y \1c) => y1.
  by right;right;exists x, \1o, \0c;split;fprops; rewrite ?opowx1 // y1 opowx0.
case: (equal_or_not x \1c) => x1.
 by right;right;exists y,\0c,\1c;split;fprops; rewrite ? opowx1 // x1 opowx0.
move: (the_cnf_p0_nz xnz) (the_cnf_p0_nz ynz).
set a := the_cnf x; set b := the_cnf y.
move =>[anz av] [bnz bv].
have h1:oprod_comm (cnf_val a) (cnf_val b) by rewrite av bv.
move:(cnf_size_nz anz) (cnf_size_nz bnz).
set m := cnf_size a; set m' := cnf_size b; move => [mN mv][m'N m'v].
move: (proj42 (proj1(proj44 (proj1 anz)))) => ax0.
move: (proj42 (proj1(proj44 (proj1 bnz)))) => ay0.
have l0x:=(proj2 (cnf_size_nz_ter anz)). 
have l0y:=(proj2 (cnf_size_nz_ter bnz)). 
move: (ax0 _ l0x) (ay0 _ l0y) => oex0 oey0.
case: (ozero_dichot oex0) => limX; last first.
  case: (ozero_dichot oey0) => limY; last first.
    by move: (oprod2_comm4 anz bnz limX limY h1); rewrite av bv; left.
  move:(oprod2_comm1 anz bnz limY limX h1);rewrite bv => h2; contradiction.
case: (ozero_dichot oey0) => limY; last first.
  symmetry in h1.
  move: (oprod2_comm1 bnz anz limX limY h1); rewrite av => h2;contradiction.
case: (equal_or_not (cnf_size a) \0c) => n1.
  move: (oprod2_comm5 anz bnz limX limY n1 h1); rewrite av bv.
   case => h2; [ by case: x1 | by right;left].
case: (equal_or_not (cnf_size b) \0c) => m1.
  symmetry in h1.
  move: (oprod2_comm5 bnz anz limY limX m1 h1); rewrite av bv.
  case => h2; [ by case: y1 |move: h2 => [q1 q2];by right;left; split].
right; right.
move: (CNFp_exists xnz) => [px [n [ax2 nN xv2]]].
move: (CNFp_p4 ax2 nN)  => [e''x [c''x [ax3 xv3 ex1 eqx2]]].
move: (proj44 (proj1 anz)); rewrite mv  => ax1.
move: xv3; rewrite - xv2 - {1}  av /cnf_val mv => xv3.
move: (CNFb_unique (NS_succ nN)  (NS_succ mN) ax3  ax1 xv3)  => [sa scx].
have mn:=(csucc_inj (CS_nat nN) (CS_nat mN) sa).
rewrite mn  in eqx2  scx xv2 ax2; clear sa mn xv3.
move: (CNFp_exists ynz) =>  [py [n' [ay2 n'N yv2]]].
move: (CNFp_p4 ay2 n'N) => [e''y [c''y [ay3 yv3 ey1 eqy2]]].
move: yv3;  rewrite - yv2 - {1} bv /cnf_val m'v => yv3.
move: (proj44 (proj1 bnz)); rewrite m'v =>  ay1.
move: (CNFb_unique (NS_succ n'N)  (NS_succ m'N) ay3 ay1 yv3) => [sa scy].
have mn:=(csucc_inj (CS_nat n'N) (CS_nat m'N) sa).
rewrite mn  in eqy2 scy yv2 ay2; clear sa mn yv3.
move: (proj2 (proj44 (proj1  anz)) _ l0x) => c1a.
move: (proj2 (proj44 (proj1  bnz)) _ l0y) => c2a.
move:(proj32_1 c1a) (proj32_1 c2a) => oc1 oc2.
move: xv2 yv2; rewrite /CNFpv eqy2 eqx2. 
move: (scy _ (succ_positive m')) (scx _ (succ_positive m)) => [e1 e2][e3 e4]. 
rewrite e1 e2 e3 e4 limX limY.
aw; rewrite oopow0 (oprod1l oc1) (oprod1l oc2) => xv4 yv4.
have ax5: (CNFp_ax4 px (cpred m) x).
  move: (cpred_pr mN n1) => [qa qb].
  by hnf; rewrite - qb eqx2 pr1_pair  pr2_pair e3 e4 limX - xv4; split.
have ay5: (CNFp_ax4 py (cpred m') y).
  move: (cpred_pr m'N m1) => [qa qb].
  by hnf; rewrite - qb eqy2   pr1_pair  pr2_pair e2 e1 limY - yv4; split.
exact: (oprod2_comm6 ax5 ay5 h).
Qed.




(** Factorisation *)


Lemma oprod_neg_p1 x y:  ordinalp x -> osuccp y ->
  x *o y =  y -> x = \1o.
Proof. 
move => ox yz eq1.
have yp: \0c <o y by case:yz => [z oz ->]; apply: olt0S.
have oy := proj32_1 yp.
case: (ozero_dichot ox) => xp.
  by case: (proj2 yp); rewrite -eq1 xp oprod0l.
move: (the_cnf_p0_nz yp); set b := the_cnf y; move=> [bnz yv].
move: (the_cnf_p0_nz xp); set a := the_cnf x; move=> [anz xv].
move:(ovaluation2_rev yz); rewrite /ovaluation -/b => vy0.
move:(CNF_prod_pr6 anz bnz vy0); rewrite xv yv eq1 -yv=> eq2.
move:(cnf_val_inj (proj1 bnz) (cnfp_prod_gen anz bnz) eq2) => eq3.
move:(cnf_size_nz anz) (cnf_size_nz bnz).
set n := cnf_size a; set m := cnf_size b; move => [nN nv][mN mv].
move:(f_equal domain eq3).
have db: (domain b -c \1c) = m.
  by rewrite mv - (cpred_pr4 (CS_succ m))  (cpred_pr1 (CS_nat mN)).
rewrite/cnf_prod_gen/cnf_nm /cnf_nck/cnf_shift_expo !Lgd.
move => eq4; move:(eq4).
rewrite mv nv - (cpred_pr4 (CS_succ m)) (cpred_pr1 (CS_nat mN)).
rewrite (csum_Sn _ nN) - (csum_nS _ mN) -{1}(csum0l (CS_succ m)).
move/(csum_eq2r (NS_succ mN) NS0 nN) => nz.
move:(f_equal (Vg ^~\0c) eq3).
have zdb:= proj1 (cnf_size_nz_ter bnz).
move:  (proj1 (cnf_size_nz_ter anz)).
rewrite/cnf_prod_gen/cnf_nm /cnf_nck/cnf_shift_expo !Lgd - eq4.
rewrite (LgV zdb) /cnf_m nv (Y_true (succ_positive _)) /cnf_c -/n - nz => i0z.
rewrite (LgV i0z); Ytac0; move => eq5.
move:(f_equal P eq5); aw; rewrite  -/(oexp _ _)vy0 /cnf_degree -/n - nz => dz.
move:(cnf_nat_prop anz (esym nz)(esym dz)) => [ /olt_omegaP eu ev].
rewrite ev in eu.
move:(f_equal Q eq5); aw; rewrite -/(ocoef _ _) /cnf_lc -/n - nz.
move/cnfpP: (proj1 bnz) => /proj43 hu.
move:(proj33 (hu _ zdb)) => [q1 /proj2 /nesym q2].
rewrite - xv ev {1} /ocoef - {1} (cprod1l  (CS_nat q1)).
by move/(cprod_eq2r q1 NS1 eu q2) . 
Qed.

Lemma oprod_neg_p2 x y : \0o <o x -> limit_ordinal y ->
   (x *o y = y  <-> odegree x <<o ovaluation y).
Proof.
move => xp ly.
move: (ovaluation6 (limit_pos ly)) => [z sz yv].
have od:=(OS_degree (proj32_1 xp)).
have ov:=(OS_valuation  (limit_pos ly)).
have oz: ordinalp z by case sz => [t /OS_succ ost ->].
move:(OS_pow OS_omega ov) (OS_pow OS_omega od) => oov ood.
rewrite (CNF_prod_pr3 xp ly) {1 2} yv (oprodA ood oov oz).
rewrite - (opow_sum OS_omega od ov); split => hyp; last by rewrite hyp.
exact: (proj1 (ovaluation7 (OS_sum2 od ov) ov sz sz hyp)).
Qed.


Definition ord_sprime a :=
  [/\ ordinalp a, \1o <o a &
     forall b c, ordinalp b -> ordinalp c -> a = b *o c -> b = \1o \/ c = \1o].


Definition ord_prime a :=
  [/\ ordinalp a, \1o <o a &
     forall b c, ordinalp b -> ordinalp c -> a = b *o c -> a = b \/ a = c].


Lemma ord_prime_prop1 a: ord_sprime a -> ord_prime a.
Proof.
move => [oa ag1 H]; split => // b c ob oc eq1; rewrite eq1.
case:(H b c ob oc eq1) => ->.
  by right;rewrite (oprod1l oc).
by left;rewrite (oprod1r ob).
Qed.

Lemma succ_pow_omega_irred p: ordinalp p -> ord_sprime (osucc (oopow p)).
Proof.
move => op; split.
    exact: (OS_succ (OS_pow OS_omega op)).
  by rewrite - (osucc_zero); apply/ oltSSP; apply:(oopow_pos op).
move => a b oa ob sab.
have oop:= OS_pow OS_omega op.
have: osuccp (a *o b) by rewrite - sab; exists (omega0 ^o p).
move/(oprod_succP oa ob) => [[a1 oa1 av] [b1 ob1 bv]].
have oab1 := (OS_prod2 oa ob1).
move: sab. rewrite bv (oprod2_succ oa ob1) {2} av - (osum2_succ oab1 oa1).
move/(osucc_inj oop (OS_sum2 oab1 oa1)) => /esym eq1.
case: (ozero_dichot ob1) => b1p; first by rewrite b1p osucc_zero; right.
case: (indecomp_pr oab1 oa1 (indecomp_prop4 op) eq1) => eq2.
  rewrite eq2 in eq1; move: (osum2_a_ab oop oa1 eq1) => a1z.
  by left; rewrite av a1z osucc_zero.
move:(oleT (oprod_Mle1 oa b1p) (osum_Mle0 oab1 oa1)).
rewrite eq1  -/(oopow _) - eq2 av; case/oleNgt; exact:(oltS oa1).
Qed.


Lemma succ_pow_omega_prime p: ordinalp p -> ord_prime (osucc (oopow p)).
Proof. by move =>/succ_pow_omega_irred /ord_prime_prop1. Qed.


Lemma ord_prime_prop2 a b c: \0o <o a -> \0o <o b -> osuccp b -> ordinalp c ->
  a *o b = oopow c -> a = oopow  c /\ b = \1o.
Proof.
move => ap bp bs oc eq.
have ob := proj32_1 bp; have ooc :=  (OS_pow OS_omega oc).
move:(ovaluation_prod ap bp); rewrite eq (ovaluation_opow oc).
case: (ozero_dichot (OS_valuation bp)) => vbz; last first.
  case (limit_nonsucc' (ovaluation3 bp vbz) bs).
Ytac0; move => cva.
move: (ovaluation6 ap) => [z sz av].
have oz: ordinalp z by case: sz => [t ot ->]; fprops.
move: eq; rewrite av - cva - (oprodA ooc oz ob) => eq.
move: (oprod2_simpl1 (OS_prod2 oz ob) (oopow_pos oc) eq) => eq1.
by move: (oprod2_one oz ob eq1) => [-> b1]; rewrite (oprod1r ooc).
Qed.
  
Lemma ord_prime_prop3 a b c (d := odegree a):
  \0o <o a -> limit_ordinal b -> ordinalp c ->
  a *o b = oopow c -> d <=o c /\ b = oopow (c -o d).
Proof.
move => ap limb oc eq.
move:(proj32_1 ap)(proj31 limb) => oa ob.
move:(OS_degree oa) (OS_degree ob) => oda odb.
move: (odegree_prod ap (limit_pos limb)).
rewrite eq -/d (odegree_opow oc) => eq1.
split; first by rewrite eq1; apply:(osum_Mle0 oda odb).
move: eq; rewrite /oopow (CNF_prod_pr3 ap limb) -/d eq1.
rewrite (opow_sum OS_omega oda odb) (odiff_pr1 oda odb).
by move/(oprod2_simpl ob (OS_pow OS_omega odb) (oopow_pos oda)).
Qed.

Lemma ord_prime_prop4 n: ordinalp n ->  ord_prime (oopow n) ->
  indecomposable n. 
Proof.
move => on [oon nnz opn]; split.
  by apply: (ord_ne0_pos on) => nz; case: (proj2 nnz); rewrite nz oopow0.
move => a b lan lbn abn.
move: (opow_Mo_lt lan) (opow_Mo_lt lbn).
move => [[op1 _ _] /nesym od1] [[op2 _ _] /nesym od2].
move:(opow_sum OS_omega (proj31_1 lan)  (proj31_1 lbn)); rewrite abn => H.
by case:(opn _ _ op1 op2 H).
Qed.

Lemma ord_prime_prop5 n: indecomposable n ->  ord_prime (oopow n).
Proof.
move => idn.
move:(proj1 idn) => np. 
move:(proj32_1 np) => on.
have oon:= (OS_pow OS_omega on).
move:(opow_Mo_lt np);  rewrite oopow0 => oogt1.
split => // b c ob oc fb.
case: (ozero_dichot ob) => bp.
  by move: (proj2 (olt_ltT olt_01 oogt1)); rewrite fb bp oprod0l.
case: (ozero_dichot oc) => cp.
  by move: (proj2 (olt_ltT olt_01 oogt1)); rewrite fb cp oprod0r.
case: (ordinal_limA oc)=> limc; first by case: (proj2 cp).
  by left; move: (proj1 (ord_prime_prop2 bp cp  limc on (esym fb))).
case: (ord_prime_prop3 bp  limc on (esym fb)).
set d := odegree b; move => ha ->.
move: (odiff_pr ha) => [oe ev].
case:(indecomp_pr (proj31 ha) oe idn (esym ev)); last by  move => ->; right.
move => dn; left.
apply: oleA; first by move: (proj1 (the_cnf_p4 bp)); ue. 
by rewrite fb; apply:(oprod_Mle1 ob cp).
Qed.

Lemma ord_prime_prop5' n: ordinalp n -> ord_prime (oopow (oopow n)).
Proof. by move => on; apply:(ord_prime_prop5 (indecomp_prop4 on)). Qed.
  
Definition nat_prime a :=
  [/\ natp a, \1c <c a &
     forall b c, natp  b -> natp c -> a = b *c c -> b = \1c \/ c = \1c].
      
Lemma nat_prime_p1 a : nat_prime a -> ord_prime a.
Proof.
move => [aN ag1 ap].
have oag1 :=  (oclt ag1).
apply:ord_prime_prop1;  split; [ by apply:OS_nat | exact: oag1 |].
move => b c ob oc av.
case: (ozero_dichot ob) => bp.  
  by move: (proj2 (olt_ltT olt_01 oag1)); rewrite av bp oprod0l.
case: (ozero_dichot oc) => cp.  
  by move: (proj2 (olt_ltT olt_01 oag1)); rewrite av cp oprod0r.
move: (oprod_Mle1 ob cp) (oprod_M1le bp oc); rewrite - av => le1 le2.
move/olt_omegaP: aN => asmall.
have bN: natp b by apply/olt_omegaP;exact:(ole_ltT le1 asmall).
have cN: natp c by apply/olt_omegaP;exact:(ole_ltT le2 asmall).
move:av; rewrite(oprod2_2int bN cN) => h; apply: (ap _ _ bN cN h).
Qed.


Lemma nat_prime_P a : nat_prime a <-> ord_prime a /\ a <o omega0.
Proof.
split.
  move => h; split; first exact:(nat_prime_p1 h).
  by move/olt_omegaP: (proj31 h).
move => [[ha hb hc] /olt_omegaP aN].
move:(oclt3 CS1 (CS_nat aN) hb) => lt1a.
split => // b c bN cN; rewrite - (oprod2_2int bN cN) => av.
have anz :=(proj2 (clt_ltT clt_01 lt1a)).
case: (equal_or_not b \0c) => bz; first by case: anz;rewrite av bz oprod0l.
case: (equal_or_not c \0c) => cz; first by case: anz; rewrite av cz oprod0r.
have H b' c': natp b' -> natp c' -> b' <> \0c -> b' = b' *c c' -> c' = \1c.
  move => b'N c'N b'nz;  rewrite cprodC -{1}(cprod1l (CS_nat b'N)) => h.
  by rewrite (cprod_eq2r b'N NS1 c'N b'nz h).
case: (hc _ _ (OS_nat bN) (OS_nat cN) av)=> eq1.
  move: av; rewrite  eq1 (oprod2_2int bN cN) => bb.
  right; exact:(H b c bN cN bz bb).
move: av; rewrite eq1 (oprod2_2int bN cN) cprodC => bb.
left; exact:(H _ _  cN bN cz bb).
Qed.

Lemma nat_prime_p2 a: natp a -> \1c <c a ->
   (nat_prime a <-> ~ composite a).
Proof.
move => aN ag1; split.
  move => [_ _ ap] [b [bN [le1b /nesym n1b] [_ lba] bda]].
  move: (cdivides_pr bda) => av.
  case(ap _ _ bN (NS_quo b aN) av) => // eq1.
  case: lba; rewrite av eq1 cprod1r; fprops.
move => nca; split => // b c bN cN eq1.
move: (proj1 ag1); rewrite eq1 => /(cprod_ge1 bN cN) [le1b le1c].
case:(cle_eqVlt le1b) => lt1b; first by left.
case:(cle_eqVlt le1c) => lt1c; first by right.
have lba: b <c a by rewrite eq1; apply:(cprod_M1lt' bN le1b lt1c).
move:(cdivides_pr1 cN bN); rewrite - eq1 => bdp.
by case:  nca; exists b.
Qed.

Lemma nat_prime_p3 a: natp a -> \1c <c a ->
  exists2 p, nat_prime p & p %|c a.
Proof.
move => aN;move: (cleR (CS_nat aN)); move: a aN {1 3 4}a; apply:Nat_induction.
  move => a /cle0 -> [/cleNgt[]]; exact:clt_01.
move => n nN Hrec a alesn lt1a.
have aN:=(NS_le_nat alesn (NS_succ nN)).
case: (p_or_not_p (composite a)); last  first.
  by move/(nat_prime_p2 aN lt1a);exists a => //; apply: cdivides_itself. 
move => [b [bN lt1b ltba bda]].
move/(cltSleP nN):(clt_leT ltba alesn) => lebn.
by move:(Hrec _ lebn lt1b) => [p pa /(cdivides_trans bda) pb]; exists p. 
Qed.

Definition nat_factor_list (p: fterm) n :=
  [/\ ord_below p n, forall i, i<c n -> nat_prime (p i) &
    forall i, natp i -> csucc i <c n -> (p (csucc i)) <=o p i]. 

Lemma nat_factor_list_rec p n: natp n -> 
  nat_factor_list p (csucc n) -> nat_factor_list p n.
Proof.
move => nN [ha hb hc].
have H i: i<c n -> i <c (csucc n) by  move => lin;apply: clt_ltT (cltS nN).
split => //.
- by move => i /H /ha.
- by move => i /H /hb.
- by move => i iN /H lsin; apply:(hc i iN lsin).
Qed.
  
Lemma NS_nat_prime_factor p n: natp n -> (nat_factor_list p n) ->
  natp (oprodf p n).
Proof.
move => nN [_ H _].
have: forall i, i<c n -> natp (p i) by move => i /H [].
clear H; move: n nN; apply: Nat_induction.
  by move => _;rewrite oprod_f0; apply: NS1.
move => n nN Hr fn1; rewrite (oprod_fS _ nN).
move: (true_below_rec nN fn1) => [ha hb].
have hc:=(Hr ha); rewrite (oprod2_2int (Hr ha) hb); fprops.
Qed.

Lemma nat_prime_factor_vS p n: natp n -> nat_factor_list p (csucc n) ->
  [/\ natp  (oprodf p n), natp (p n) &
  oprodf p (csucc n) = (oprodf p n) *c (p n)]. 
Proof.
move => nN H.
move: (NS_nat_prime_factor nN (nat_factor_list_rec nN H)) => fN.
move:(proj31 (proj32 H _ (cltS nN)))=> pN.
by rewrite (oprod_fS _ nN) (oprod2_2int fN pN).
Qed.


Lemma nat_prime_p4 p n i: natp n -> (nat_factor_list p n) -> i <c n->
  p i %|c (oprodf p n).
Proof.
move => nN; move: n nN i; apply:Nat_induction;first by move => i _ /clt0.
move => n nN Hrec i hr/(cltSleP nN) lin.
move:(nat_prime_factor_vS nN hr) => [fN pnN ->].
case:(cle_eqVlt lin) => ltin. 
  by rewrite ltin cprodC; apply: (cdivides_pr1 fN pnN).
exact:(cdivides_trans2 pnN (Hrec i (nat_factor_list_rec nN hr) ltin)).
Qed.

Lemma nat_prime_coprime a b: nat_prime a -> nat_prime b ->
   a = b \/ coprime a b.
Proof.
move => [aN ag1 ap] [bN bg1 bp].
case: (equal_or_not a b) => eab; [by left | right; split => //].
move => x xda xdb.
move:(cdivides_pr xda) (cdivides_pr xdb)  => ea eb.
case:(ap _ _ (proj32 xda) (NS_quo x aN) ea) => // => ec.
case:(bp _ _  (proj32 xdb) (NS_quo x bN) eb) => // => ed.
by case: eab; rewrite ea eb ec ed.
Qed.


Lemma nat_prime_p5 p n q: natp n -> (nat_factor_list p n) ->
   nat_prime q -> q %|c (oprodf p n) ->
   exists2 i, i <c n & q = p i.
Proof.
move => nN h qp; move: n nN h; apply: Nat_induction.
  rewrite oprod_f0; move: qp => [_ [_ q1] _] _  /cdivides_oner nq1.
  by case:q1.
move => n nN Hrec hsn.
move:(nat_prime_factor_vS nN hsn) => [fN pnN ->] qdv.
case: (nat_prime_coprime qp (proj32 hsn _ (cltS nN)))=> cpd.
  exists n => //; exact: (cltS nN).
move:(Hrec(nat_factor_list_rec nN hsn)  (coprime3  cpd fN qdv)).
move => [i lin ->];exists i => //; exact: (clt_ltT lin (cltS nN)).
Qed.

Lemma nat_prime_p6 p p' n n': natp n -> natp n' ->
   nat_factor_list p n  ->  nat_factor_list p' n' ->
   oprodf p n = oprodf p' n' ->
   n = n' /\ same_below p p' n.
Proof.
move => nN n'N hn; move:n nN hn n' n'N; apply: Nat_induction.
  move => ha m mN hb eq1; case: (equal_or_not m \0c) => m0.
    by split => // i /clt0.
  move: (cpred_lt mN m0) => lt1.
  move:(nat_prime_p4 mN hb lt1); rewrite - eq1 oprod_f0 =>/(cdivides_oner).
  by move: (proj2 (proj32 (proj32 hb _ lt1)))=> bad eq2; case:bad.
have aux : forall n, natp n -> forall q i, nat_factor_list q (csucc n) -> 
   i <c csucc n -> q n <=o q i.
   move => n nN q i hyp /(cltSleP nN) /cle_eqVlt;case.
     by move ->; exact: (oleR (proj31 hyp _ (cltS nN))).
   move: n nN q i hyp; apply: Nat_induction; first by  move => q i _ /clt0.
   move=> n nN Hrec q i hr /(cltSleP nN) /cle_eqVlt.   
   have lt0 := (proj33 hr _ nN (cltS (NS_succ nN))).
   case => lin; first by rewrite lin.
   exact:(oleT lt0 (Hrec q i (nat_factor_list_rec (NS_succ nN) hr) lin)).
move=> n nN Hrec nf1 m mN nf2 eq1.
move:(nat_prime_p4 (NS_succ nN) nf1 (cltS nN)); rewrite eq1=> dvd1.
have ppn:= (proj32 nf1 _ (cltS nN)).
move:(nat_prime_p5 mN nf2 ppn dvd1) => [i lim ppni].
case: (equal_or_not m\0c) => mz; first by  move:lim; rewrite mz => /clt0.
move:(cpred_pr mN mz) => [m'N m'v].
move: (cpred_lt mN mz) => lt1.
move:(nat_prime_p4 mN nf2 lt1); rewrite - eq1 => dvd2.
have ppm:= (proj32 nf2 _ lt1).
case: (equal_or_not (p' i) (p' (cpred m))) => he1.
  move: eq1.
  rewrite m'v in nf2 *.
  move: (nat_prime_factor_vS nN  nf1) => [p1N f1N ->].
  move: (nat_prime_factor_vS m'N  nf2) => [p2N f2N ->].
  rewrite - he1 - ppni => eq2.
  move: (nesym (proj2 (clt_ltT clt_01 (proj32 ppn)))) => pnz.
  move: (cprod_eq2r f1N p1N p2N pnz eq2)=> eq3.
  move: (nat_factor_list_rec nN nf1) (nat_factor_list_rec m'N nf2)=> nf1' nf2'.
  move: (Hrec nf1' _ m'N nf2' eq3) => [eq4 eq5].
  split; [by  rewrite eq4 | move => k /(cltSleP nN) lkn].
  case:(cle_eqVlt lkn) => ltin; first by rewrite ltin ppni he1 eq4.
  by apply: eq5.
move:(nat_prime_p5 (NS_succ nN) nf1 ppm dvd2) => [j ljn ppnj].
rewrite m'v in nf2 lim.
have : p' (cpred m) <o p' i.
   split;[ exact: (aux _  m'N p' i nf2 lim) | exact: (nesym he1)].
rewrite ppnj - ppni => /oltNge; case; exact:(aux _ nN p j nf1 ljn).
Qed.

Lemma nat_prime_p7 a: natp a -> \1c <=c a -> exists p n,
   [/\ nat_factor_list p n, natp n & oprodf p n = a ].
Proof.
move => aN; move: (cleR (CS_nat aN)); move: a aN {1 3 4}a; apply:Nat_induction.
  move => a /cle0 -> /cleNgt[]; exact:clt_01.
move => m mN Hrec a am.
case:(cle_eqVlt am) => lekn; last by move/(cltSleP mN): lekn; apply:Hrec.
move => le1a.
case: (equal_or_not \1c a) => ea1.
  exists (fun z => \0c), \0c; split; [ | exact: NS0 |by  rewrite oprod_f0 ].
  split; [ by move => i /clt0 | by move => i /clt0 | by move => i _ /clt0].
move: (nat_prime_p3 (NS_le_nat am (NS_succ mN)) (conj le1a ea1)) => [y npy yda].
pose pr y := nat_prime y /\ y %|c a.
have oy :=(OS_nat (proj31 npy)).
have pry: pr y by [].
move:(least_ordinal4 oy pry); set z := least_ordinal _ _.
move => [oz [npz zda] lz];
move:(npz) => [zN lt1z zpr]. 
move: (cdivides_pr zda) (NS_quo z (proj31 zda)); set q := (a %/c z)=> av qN.
move:(le1a); rewrite av => /(cprod_ge1 zN qN) [_ le1q].
have leqm: q <=c m.
  apply/(cltSleP mN);rewrite - lekn av cprodC; exact:(cprod_M1lt' qN le1q lt1z).
move: (Hrec q leqm le1q) =>[p [n [nflp nN poq]]].
pose p' i := Yo (i <c n) (p i) z.
have eq0: p' n = z by rewrite /p' (Y_false (cleNgt (cleR (CS_nat nN)))).
have eq1: oprodf p' n = oprodf p n.
  by apply: (oprodf_exten nN) => i lin; rewrite /p'; Ytac0.
have  eq2:oprodf p' (csucc n) = z *c q.
  by rewrite (oprod_fS _ nN) eq1 poq eq0 (oprod2_2int qN zN) cprodC.
exists p', (csucc n); split; [ | apply: (NS_succ nN) | done].
split.
- move => i /(cltSleP nN) lin; case: (cle_eqVlt lin) => ltin.
    by rewrite ltin eq0.
  rewrite /p' (Y_true ltin); exact: (proj31 nflp _ ltin).
- move => i /(cltSleP nN) lin; case: (cle_eqVlt lin) => ltin.
    by rewrite ltin eq0.
  rewrite /p' (Y_true ltin); exact: (proj32 nflp _ ltin).
- move => i iN /(cltSleP nN) lesin.
  move:(clt_leT (cltS iN) lesin) => ltin.
  rewrite {2}/p' (Y_true ltin).
  case: (cle_eqVlt lesin) => lesin';last first.
    rewrite /p' (Y_true lesin'); exact: (proj33 nflp _ iN lesin').
  rewrite lesin' eq0.
  move: (cdivides_trans2 zN (nat_prime_p4 nN nflp ltin)).
  rewrite cprodC poq -av => pida.
  move: (proj32 nflp _ ltin) => pip.
  by apply: (lz (p i) (OS_nat (proj31 pip))); split.
Qed.

Definition ord_ptypeF a := nat_prime a.
Definition ord_ptypeI a := exists2 p, \0o <o p & a = osucc (oopow p).
Definition ord_ptypeL a := exists2 p, ordinalp p & a = oopow (oopow p).

Lemma ord_ptypeF_prop a: ord_ptypeF a -> osuccp a /\ a <o omega0.
Proof.                         
move=>[aN ag1 _]; split; last by apply /olt_omegaP.
move:(cpred_pr aN (nesym (proj2 (clt_ltT clt_01 ag1)))) =>[bN bv].
exists (cpred a); [ exact:(OS_nat bN) | by rewrite - (succ_of_nat bN)].
Qed.

Lemma ord_ptypeI_prop a: ord_ptypeI a -> osuccp a /\ omega0 <=o a.
Proof.
move => [p op ->]; split.
  exists (omega0 ^o p) => //.
  apply: (OS_pow OS_omega (proj32_1 op)).
move:op => /oge1P /opow_Mo_le;rewrite oopow1 => op.
apply: (oleT op (oleS (proj32 op))).
Qed.

Lemma ord_ptypeL_prop a: ord_ptypeL a -> limit_ordinal a /\  omega0 <=o a.
Proof.
move=> H; suff h: limit_ordinal a by split; [exact | exact: (limit_ge_omega h)].
move:H => [p op ->];apply:indecomp_limit2; (apply:oopow_pos op).
Qed.

Lemma ord_prime_p1 a:
  ord_prime a <-> [\/ ord_ptypeF a,  ord_ptypeI a | ord_ptypeL a].
Proof.
split; last first.
   case.
   + by move /nat_prime_p1.
   + by move => [p /proj32_1 /succ_pow_omega_prime op ->].
   + move => [p op ->];apply:(ord_prime_prop5' op).
move => aprime; move: (aprime) => [oa ag1 ap].
move: (olt_ltT olt_01 ag1) => ag0.
move: (CNFp_exists ag0) => [p [n [[axb [qa qb /posnat_ordinalp qc]] nN]]].
move: qc; set a2 := (Q (p n));move  => [a2nz a2lo].
move: (OS_CNFp1 axb nN);rewrite /CNFpv.
set a3 := CNFpv1 p n => oa3.
move:(OS_oopow qb); set a1 := oopow _ => oa1.
have oa12: ordinalp (a1 *o a2) by apply: (OS_prod2 oa1 (proj32_1 a2nz)).
move => af; case: (ap _ _ oa12 oa3 af)=> af1.
  case:(ap a1 a2 oa1 (proj32_1 a2nz) af1) => aa1; last first.
    by constructor 1; apply/nat_prime_P; split => //; rewrite aa1.
  constructor 3.
  move:aprime;rewrite aa1 /a1 => apr.
  by move:(indecomp_prop3 (ord_prime_prop4 qb apr)) => [q op ->]; exists q.
move: af1; rewrite /a3 => av.
clear a2 a2lo a2nz oa12 af a1 oa1  a3 oa3 qa qb.
move:n nN axb av; apply:Nat_induction.
  by rewrite CNFp_0 => _ ea1; case:(proj2 ag1).
move => n nN Hrec axn .
rewrite (CNFp_r _  nN).
move:(OS_CNFp1r axn (NS_succ nN) (cleS nN)).
set a1 := (CNFpv1 p n) => oa1.
move: (axn _ (cltS nN)) => [_ ax1 ax2].
rewrite /cantor_pmon (CNFp_pr1 ax1 ax2)/CNFp_value1.
move: (OS_succ (OS_pow OS_omega (proj32_1 ax1))); set a2 := osucc _ => oa2.
move:(OS_nat (proj1 ax2)) => oa3 av.
case:(ap _ _ oa1 (OS_prod2 oa2 oa3) av) => av1; last first.
  case: (ap _ _ oa2 oa3 av1) => av3.
    by constructor 2; rewrite av3; exists (P (p n)).
  move/posnat_ordinalp: ax2 =>[ha hb].
  by constructor 1;  apply/nat_prime_P; split => //; rewrite av3.
by apply: Hrec => // i lin; move:(clt_ltT lin (cltS nN))=> /axn.
Qed.

Definition ord_prime_le a b:=
  (a <o omega0 -> b <o omega0 -> b <=o a)
  /\ (forall p, ordinalp p -> b = oopow (oopow p) ->
     exists2 q, p <=o q & a = oopow (oopow q)).

Definition ord_factor_list (p: fterm) n :=
  [/\ natp n, (forall i, i<c n ->ord_prime (p i)) &
   forall i, natp i -> csucc i <c n -> ord_prime_le (p i) (p (csucc i))].

Lemma ord_factor1 p n: ord_factor_list p n -> ord_below p n.
Proof. by move => [nN H _] i /H []. Qed.

Definition ord_factor_boundary (p: fterm) n k :=
   [/\ k <=c n, forall i, i <c k -> limit_ordinal (p i) &
      forall i, k <=c i -> i <c n -> osuccp (p i)].

Lemma ord_factor2 p n:  ord_factor_list p n -> 
 exists k,  ord_factor_boundary p n k.
Proof.
move => [nN h1 h2].
set E:= Zo n (fun i => ord_ptypeL (p i)).
set F := n -s E.
have prop1 i: inc i E -> limit_ordinal (p i).
  by move => /Zo_hi/ord_ptypeL_prop [].
case:(emptyset_dichot F) => Fe.
  exists n; split => //.
  - apply: (cleR (CS_nat nN)).
  - move => i /(NltP nN) => ein; exact:(prop1 _ (empty_setC Fe ein)).
  - by move => i leni /cltNge.
have cF: cardinal_set F by move => i/setC_P [/(NltP nN)/proj31_1 ].
move: (cle_wor' cF Fe); set k := intersection F; move => [kF lkF].
have Ep1 i: natp i -> inc (csucc i) E -> inc i E.
  move => iN /Zo_P [/(NltP nN) lin tpi ]; apply:Zo_i.
    by move/(NltP nN):(clt_ltT (cltS iN) lin).
  move: tpi => [q qa qb].
  move:(proj2 (h2 i iN lin) q qa qb) => [b qlb bv]; exists b => //.
  exact:(proj32 qlb).
have Ep2 i: inc i F -> csucc i <c n -> inc (csucc i) F.
  move => iF sin; apply/setC_P; split;[ by apply/(NltP nN) | move => siE].
  move/setC_P: iF =>  [lin]; case; apply:(Ep1 _ (NS_inc_nat nN lin) siE).
have lkn: k <c n by move/Zo_P: kF => [/(NltP nN) ].
  exists k; split.
- exact: (proj1 lkn).
- move => i lik;move/(NltP nN):(clt_ltT lik lkn) => iin.
  apply: prop1; ex_middle iinE.
  by move/(setC_P): (conj iin iinE) => /lkF/cleNgt; case.
- move => i ha hb.
  suff h: inc i F.
    case /ord_prime_p1: (h1 _ hb).
    + by case/ord_ptypeF_prop. 
    + by case/ord_ptypeI_prop. 
    + by move => hh; case/setC_P:h => ii;case; apply: Zo_i.
  move:(NS_lt_nat hb nN) => iN.
  move:i iN ha hb; apply: Nat_induction; first by  move => /cle0 => <-.
  move => i iN Hrec le1 le2; move:(clt_ltT (cltS iN) le2) => le3.
  case: (cle_eqVlt le1) => lesin; first by rewrite - lesin.
  move/(cltSleP iN): lesin => lki; exact: (Ep2 _ (Hrec lki le3) le2).
Qed.

Lemma ord_factor3 p n k k':  ord_factor_list p n -> 
  ord_factor_boundary p n k -> ord_factor_boundary p n k' ->
  k = k'.                           
Proof.
move => ofl [lkn llk sgtk] [lkn' llk' sgtk'].
move: (proj31 lkn) (proj31 lkn') => ck ck'.
case: (cleT_ell ck ck').
- exact.
- move => kk'; move : (sgtk _ (cleR  ck) (clt_leT kk' lkn')) => lm.
  case:(limit_nonsucc' (llk' _ kk') lm).
- move => kk'; move : (sgtk' _ (cleR  ck') (clt_leT kk' lkn)) => lm.
  case:(limit_nonsucc'  (llk _ kk') lm).
Qed.

Lemma ord_factor4 p n
      (q := fun i => odegree (odegree (p i)))
      (r := fun i => q (cpred (n -c i))):
  ord_factor_list p n -> 
  (forall i, i <c n -> limit_ordinal (p i)) ->
 [/\ forall i, i <c n -> p i = oopow (oopow (q i)), 
     CNFr_ax r n & oprodf p n = oopow (CNFrv r n)].
Proof.
move => h.
have h0:=(ord_factor1 h).
move: h => [nN axa axb] H.
pose dd x := odegree (odegree x).
have dd1 x: ordinalp x -> ordinalp (dd x).
  move => ox. set T:= OS_degree; exact: (T _ (T _ ox)).
pose oo e := oopow (oopow e).
have Hp x:(exists2 e, ordinalp e & x = oo e) -> x = oo (dd x).
   move => [e oe ->]; move:(OS_oopow  oe) => ooe.
   by rewrite /dd/oo (odegree_opow ooe)  (odegree_opow oe).
have h1: forall i, i <c n -> p i = oo (dd (p i)).
  move => i lin; move: (limit_nonsucc'  (H _ lin)) => p1.
  case /ord_prime_p1: (axa i lin).
    - by move/ord_ptypeF_prop => [hh]; case: p1.
    - by move/ord_ptypeI_prop => [hh]; case: p1.
    - by move => /Hp.
have h2 i: natp i -> (csucc i) <c n ->  q (csucc i) <=o q i.
  move => iN lin; move:(proj2 (axb i iN lin) _ (dd1 _ (h0 _ lin)) (h1 _ lin)).
  move => [e ea eb]; move:(proj32 ea) => oe; move:(OS_pow OS_omega oe) => ooe.
  by rewrite /q  eb (odegree_opow ooe)(odegree_opow oe).
have rp1: ord_below r n. 
  move => i lin; rewrite /r; move:(cdiff_lt_symmetry nN lin) => lrin.
  exact:(dd1 _ (proj31 (H _ lrin))). 
have h3: CNFr_ax r n.
  split; [exact | move => i iN [lin nin]]; rewrite /r.
  move:(cdiff_pr lin) (NS_diff (csucc i) nN); set u := n -c csucc i.
  move => nv uN.
  case: (equal_or_not u \0c) => unz.
    case: nin; rewrite - nv unz csum0r; fprops.
  move: (cpred_pr uN unz) => [ha hb].
  have hc: csucc (cpred u) <c n.
    rewrite - hb - nv csumC; apply:(csum_M0lt uN (@succ_nz _)).
  by move: (h2 _ ha hc);rewrite (cdiff_A1 nN iN lin) - hb.
split => //.
transitivity  (oprodf (fun i => oo (q i)) n).
  by apply: (oprodf_exten nN) => i /h1.
rewrite /r; move: nN rp1; rewrite/r; clear.  
move:n; apply:Nat_induction.
  by move => _; rewrite oprod_f0 CNFr_p5 oopow0.
move => n nN Hrec hr.
rewrite (oprod_fS _ nN).
have ha: \1c +c n = csucc n by rewrite (Nsucc_rw nN) csumC.
have hb: ord_below (fun i => omega0 ^o q (cpred (csucc n -c i))) (\1c +c n).
  by rewrite ha; move => i lin /=; apply: (OS_pow OS_omega); apply: hr.
move:(osum_fA NS1 nN hb); rewrite ha /CNFrv => ->.
have eq1: (omega0 ^o q (cpred (csucc n -c \0c))) = omega0 ^o (q n).
  by rewrite (cdiff_n0 (NS_succ nN)) (cpred_pr2 nN).
have lt1: \0c <c (\1c +c n) by rewrite ha; apply: succ_positive.
have op1: ordinalp
     (osumf (fun z : Set => omega0 ^o q (cpred (csucc n -c (z +c \1c)))) n).
  apply:(OS_osumf nN) => i lin; apply: hb.
  by rewrite csumC; apply:(csum_Meqlt NS1 lin).
have hc: ord_below (fun i => q (cpred (n -c i))) n.
  move => i lin /=; rewrite - (cdiff_succ (CS_nat nN)(proj31_1 lin)).
  by apply:(hr (csucc i) (cltSS lin)).
rewrite (osum_f1 (hb _ lt1)) /oopow (opow_sum OS_omega op1 (hb _ lt1)) eq1.
rewrite (Hrec hc); apply: f_equal2; [apply: f_equal | done].
apply:(osumf_exten nN) => i lin /=.
by rewrite - (csucc_pr4 (proj31_1 lin)) (cdiff_succ (CS_nat nN) (proj31_1 lin)).
Qed.


Lemma ord_factor5 p n p' n':
  ord_factor_list p n -> 
  ord_factor_list p' n' ->
  (forall i, i <c n -> limit_ordinal (p i)) ->
  (forall i, i <c n' -> limit_ordinal (p' i)) ->
  oprodf p n =  oprodf p' n' ->
  (n = n' /\ same_below p p' n).
Proof.
move => ha hb  hc hd eq.
move:(ord_factor4 ha  hc) => [ra rb rc].
move:(ord_factor4 hb hd) =>[sa sb sc].
move: eq; rewrite rc sc.
move:(proj31 ha)(proj31 hb) => nN nN'.
move:(OS_CNFr0 nN rb) (OS_CNFr0 nN' sb).
set u := CNFrv _ _; set v := CNFrv _ _=> ou ov eq2.
case: (oleT_ell ou ov); last first.
- move/opow_Mo_lt => /proj2; case; symmetry; done.
- by move/opow_Mo_lt => /proj2; case. 
- move => eq3.
  move:(CNFr_unique rb sb nN nN' eq3)=> [eq1 eq5]; split; first exact.
  rewrite - eq1 in sa.
  move => i lin; rewrite (ra _ lin) (sa _ lin).
  move:(cdiff_lt_symmetry nN lin) => he.
  have hf: (cpred (n -c cpred (n -c i))) = i.
    have iN := (NS_lt_nat lin nN).
     have hf: csucc i <=c n  by apply/(cleSltP iN).
    by rewrite (cdiff_A1 nN iN hf) (double_diff nN hf) (cpred_pr2 iN).
  by move: (eq5 (cpred (n -c i)) he); rewrite - (eq1) hf => ->.
Qed.

Lemma ord_factor6 p n k (p':= fun i => p (i +c k)):
  ord_factor_list p n -> 
  ord_factor_boundary p n k ->
  [/\ ord_factor_list p k, ord_factor_list p' (n -c k),
     forall i, i<c k -> limit_ordinal (p i),
     forall i, i<c (n -c k) -> osuccp (p' i) &
     [/\ oprodf p n = (oprodf p k) *o (oprodf p' (n -c k)),
      exists2 e, ordinalp e & oprodf p k = oopow e &
      osuccp (oprodf p' (n -c k)) ] ].
Proof.
move => [nN axa axb] [lkn ha hb].
move:(cdiff_pr lkn); move:(NS_diff k nN) => dN dv.
have kN := NS_le_nat lkn nN.
have aux i:  i <c n -c k -> i +c k <c n.
  by move => link; move: (csum_Meqlt kN link); rewrite dv csumC.
have R1:  ord_factor_list p k.
  split; first exact.
    move => i lin; exact:(axa _ (clt_leT lin lkn)).
  move => i iN lin; exact:(axb _ iN (clt_leT lin lkn)).
have R2:  ord_factor_list p' (n -c k).
  split; first exact.
    move => i /aux lin; exact:(axa _ lin).
  move => i iN /aux. rewrite/p' (csum_Sn _ iN) => lin.
  exact:(axb _ (NS_sum iN kN)  lin).
have R4: forall i, i <c n -c k -> osuccp (p' i).
  move => i likn; move:(aux _ likn) => ll; apply:hb ll.
  rewrite csumC; exact(Nsum_M0le i kN).
have R5: oprodf p n = oprodf p k *o oprodf p' (n -c k).
  by rewrite - {1} dv (oprod_fA) //; rewrite dv; apply:ord_factor1.
have R6: exists2 e : Set, ordinalp e & oprodf p k = omega0 ^o e.
  move: (ord_factor4 R1 ha); set f := fun i:Set => _.
  move => [_ resa ->]; move: (OS_CNFr0 kN resa) => oe.
  by exists (CNFrv f k).
have R7: osuccp (oprodf p' (n -c k)).
  move: (n-c k) dN R4; clear; apply: Nat_induction.
    by move => _; exists \0o; [ exact: OS0 |rewrite oprod_f0 osucc_zero].
  move => n nN Hrec hi.
  have h2: forall i, i <c n -> osuccp (p' i).
    move => i lin; exact: (hi _  (clt_ltT lin (cltS nN))).
  move:(hi _ (cltS nN)) (Hrec h2) => r1 r2.
  have oe1: ordinalp (oprodf p' n) by move: r2 =>[t ot ->];exact: (OS_succ ot).
  have oe2: ordinalp (p' n) by move: r1 =>[t ot ->];exact: (OS_succ ot).
  by rewrite (oprod_fS _ nN); apply/oprod_succP.
done.
Qed.

Lemma ord_factor7 p n p' n' k k' (p1:= fun i => p (i +c k))
      (p1':= fun i => p' (i +c k')):
  ord_factor_list p n -> 
  ord_factor_list p' n' -> 
  ord_factor_boundary p n k ->   ord_factor_boundary p' n' k' ->
  oprodf p n = oprodf p' n' ->
  [/\ k = k', same_below p p' k,
    forall i, i <c n -c k -> osuccp (p1 i),
    forall i, i <c n' -c k -> osuccp (p1' i) &
    oprodf p1 (n -c k) = oprodf p1' (n' -c k)].
Proof.
move => fl fl'  kp kp' eq1.
move:(ord_factor6 fl kp); rewrite -/p1; move =>[ha hb hc hd [he hf hg]].
move:(ord_factor6 fl' kp'); rewrite -/p1'; move =>[ra rb rc rd [re rf rg]].
move:hf rf => [e1 oe1 e1v] [e2 oe2 e2v].
move: eq1; rewrite re he e1v e2v => eq2.
move:(ovaluation7 oe1 oe2 hg rg eq2) => [eq3 ->].
have eq5: oprodf p k = oprodf p' k' by rewrite e1v e2v eq3.
move:(ord_factor5 ha ra  hc rc eq5) => [eq7 eq8].
by rewrite [k in n' -c k] eq7. 
Qed.

Definition first_non_int (p: fterm) n :=
  intersection (Zo (csucc n) (fun z => z = n \/ ~ (natp (p z)))).

Lemma first_non_int_p1 p n (i := first_non_int p n):
  natp n ->
  (i = n \/ (i <c n /\ ~ natp (p i)))
  /\ forall j, j <c i -> natp (p j).
Proof.
move => nN; rewrite /i/first_non_int.
set E := Zo _ _. 
have snN := (NS_succ nN).
have nsE: cardinal_set E by move => z /Zo_S /(NltP snN)/proj31_1.
have nee: nonempty E.
  exists n; apply:Zo_i; [ by move/(NltP snN): (cltS nN) | by left].
move:(cle_wor' nsE nee) => [ /Zo_P [ /(NltP snN)ra rb] rc]; split.
  move/(cltSleP nN): ra => /cle_eqVlt; case; first by left.
  by move => lin; right; split => //; case:rb => // iE;case: (proj2 lin).
move => j lji; ex_middle bad.
case: (cltNge lji); apply: rc.
apply:Zo_i; [ by apply/(NltP snN); apply: (clt_ltT lji ra) | by right].
Qed.


Definition ofact_list_succ (p: fterm) n :=
   ord_factor_list p n /\ forall i, i <c n -> osuccp (p i).

Lemma ord_factor9_aux k p: natp k -> 
   (forall j, j <c k -> natp (p j)) ->
   (forall j, j <c k -> osuccp (p j)) ->
  posnatp (oprodf p k).
Proof.
move => kN ha hb.
have: forall i, i <c k ->  posnatp (p i).
  move => i lik; apply: (posnat_prop  (ha _ lik)).
  move: (hb _ lik) => [m om -> ].
  by move => ee; move:(succ_i m); rewrite ee => /in_set0.
move: (k) kN; clear; apply:Nat_induction.
  move:olt_01 => h1 h2;rewrite oprod_f0; apply: PN1.
move => n nN Hrec axi;rewrite (oprod_fS _ nN).
move:(true_below_rec nN axi) => [/Hrec pn1 pn2].
by rewrite(oprod2_2int (proj1 pn1) (proj1 pn2)); apply: PN_prod.
Qed.




Lemma ord_factor8 p n i: ofact_list_succ p n -> i <c n ->
  nat_prime (p i)  \/
  [/\ ordinalp (p i), ~(natp (p i))&
       p i = osucc (oopow (odegree (p i)))].
Proof.
move =>[[_ h1 _] h2] lin.
case/ord_prime_p1:(h1 _ lin).
- by left.
- move => h3; right.
  move/ord_ptypeI_prop: (h3) => [_ cp]; move:(proj32 cp) => op.
  split => //; first by move/olt_omegaP; case/oltNge.
  by case: h3 => d dp ->; rewrite (odegree_succ_pow dp).
- move/ord_ptypeL_prop => [lp _].
  case (limit_nonsucc' lp (h2 _ lin)). 
Qed.

Lemma ord_factor9 p n: ofact_list_succ p (csucc n) -> natp n -> 
   ~ (natp (p \0c)) ->
   exists ec m, [/\ natp m, CNFp_ax1 ec (csucc m),
                  oprodf p (csucc n) = CNFpv1 ec (csucc m),
        let p' := p \o csucc in  Q(ec \0c) = oprodf p' (first_non_int p' n)& 
        P(ec \0c) = odegree (p \0c)].
Proof.
move => ha nN; move: ha.
move:(cleR (CS_nat nN)). move: n nN {-2} n p.
apply: Nat_induction.
  move => n p /cle0 en0 ha h.
  set ec0 := (fun i:Set => J (odegree (p \0c)) \1c).
  rewrite en0 in ha; move:(cltS NS0) => lt01.
  case: (ord_factor8 ha lt01); first by move => [p0n]; case:h.
  move: PN1 => pn1 [hb hc hd].
  have he: \0o <o odegree (p \0c).
      case:(ozero_dichot(OS_degree hb)) => // d0.
      case: hc; rewrite hd d0 oopow0 osucc_one; apply: NS2.
  have ax1: CNFp_ax1 ec0 (csucc \0c).
    rewrite /ec0;move => i _ /=; split; aw;fprops.
  exists ec0, \0c.
  rewrite en0;split => //.
  - exact: NS0.
  - rewrite  succ_zero (oprod_f1 hb) (CNFp_1 ax1 lt01) /ec0 /cantor_pmon;aw.
    by rewrite  (CNFp_pr1 he PN1) /CNFp_value2 -hd (oprod1r hb).
  - rewrite /ec0;move:(first_non_int_p1 (fun i : Set => p (csucc i)) NS0); aw.
    set k :=  first_non_int _ _; move => [hh _]; case: hh.
      by move ->; rewrite oprod_f0.
    by move => [/clt0].
  - by rewrite /ec0 pr1_pair.
move => M MN Hrec n p.
case /cle_eqVlt; last by move/(cltSleP MN); apply: Hrec.
move => nv ofl nn0.
pose p' := fun i => p (csucc i).
have nN: natp n by rewrite nv; apply:(NS_succ MN).
have np :=(succ_positive n).
case: (ord_factor8 ofl np); first by move => [p0n]; case:nn0.
move => [op0 _ p0v].
have dp0: \0o <o odegree (p \0c).
  case:(ozero_dichot(OS_degree op0)) => // d0.
  case: nn0; rewrite p0v d0 oopow0 osucc_one; apply: NS2.
move:(first_non_int_p1 p' nN); set k := first_non_int _ _; move =>[kp1 kp2].
set c0:= oprodf p' k.
set p'' := fun i => p (i +c csucc k).
have obn: ord_below p (csucc n) by move => i /(proj32 (proj1 ofl)); case.
have ha: \1c +c n = csucc n by rewrite (Nsucc_rw nN) csumC.
have eq1: oprodf p (csucc n) = p \0c *o  oprodf p' n by apply:(oprod_f1r).
have  obn': ord_below p' n by move => i lin; apply:obn; apply/cltSS.
have lekn: k <=c n.
  by case: kp1;[ move ->; apply:(cleR (CS_nat nN))| case; case].
have kN := NS_le_nat lekn nN.
have op1: ordinalp c0.
   apply:(OS_oprodf kN) => i leik; exact:(obn' _(clt_leT leik lekn)).
have knN:=(NS_diff k nN).
have kdnv:=(cdiff_pr lekn).
have eq2:  oprodf p' n = c0 *o oprodf p'' (n -c k).
  rewrite - kdnv in obn'.
  rewrite - {1}kdnv (oprod_fA (f := p') kN knN obn'); apply: f_equal.
  by apply: (oprodf_exten knN) => i lin; rewrite /p'' /p' (csum_nS _ kN).
have eq3: oprodf p (csucc n) = (p \0c *o c0) *o oprodf p'' (n -c k).
  have op2:ordinalp (oprodf p'' (n -c k)).
    apply:(OS_oprodf knN) => i lin; apply: obn.
    rewrite (csum_nS _ kN); apply:cltSS.
    by move:(csum_Meqlt kN lin); rewrite kdnv csumC.
  rewrite eq1 eq2 (oprodA op0 op1 op2); reflexivity.
have c0N: posnatp c0.
  apply:(ord_factor9_aux kN  kp2) => j ljk.
    rewrite /p';exact: ((proj2 ofl) _ (cltSS (clt_leT ljk lekn))).
case: kp1 => kp1.
  set ecl := (fun i:Set => J (odegree (p \0c)) c0).
  have ax1: CNFp_ax1 ecl (csucc \0c).
    rewrite/ecl;move => i _ /=; split; aww.
  exists ecl, \0c; rewrite/ecl; aw.
  split => //.
  - exact: NS0.    
  - rewrite eq3 kp1 cdiff_nn oprod_f0 (oprod1r (OS_prod2 op0 op1)).
    rewrite succ_zero (CNFp_1 ax1 (succ_positive \0c)) /ecl /cantor_pmon; aw.
    rewrite (CNFp_pr1 dp0 c0N) /CNFp_value2 - p0v.
    reflexivity.
case: (equal_or_not (n -c k) \0c) => lnk.
  by move:(proj2 (proj1 kp1)); rewrite - kdnv lnk (csum0r (CS_nat kN)).
move: (cpred_pr knN lnk); set m := cpred _; move=> [mN nkv1].
have h1: m <=c M.  apply/(cleSSP (CS_nat mN) (CS_nat MN)). rewrite - nkv1 - nv.
  by apply:(cdiff_ab_le_a _ (CS_nat nN)).
have h00 i: i <c n -c k -> i +c k <c n.
  by move => link; move: (csum_Meqlt kN link); rewrite kdnv csumC.  
have h0 i: i <c csucc m -> (i +c csucc k) <c csucc n.
  by rewrite - nkv1 => /h00 ln; rewrite (csum_nS _ kN); apply:cltSS.
have h2: ofact_list_succ p'' (csucc m).
  move: ofl => [[s ax1 ax2] ax3].
   split; first split.
   - exact (NS_succ mN).
   - by move => i /h0 lim; apply: ax1.
   - move => i iN /h0 lim; rewrite /p''(csum_Sn _ iN); apply: ax2.
      exact: (NS_sum iN (NS_succ kN)).
     by rewrite - (csum_Sn _ iN).
   - by move => i /h0 lim; apply: ax3.
have h3:~ natp (p'' \0c).
  by move: (proj2 kp1); rewrite/p' /p'' (csum0l (CS_succ _)).
move:(Hrec m p'' h1 h2 h3) => [ecs [ln1 [r1 r2 r3 r4 r5]]].
set ecf := fun i => Yo (i = \0c) (J (odegree (p \0c)) c0)  (ecs (cpred i)).
have r1': natp (csucc ln1) by apply: NS_succ.
have h01 i: i <c csucc (csucc ln1) -> i <> \0c ->  cpred i <c csucc ln1.
   move => lin inz; move: (NS_lt_nat lin (NS_succ r1')) => iN.
   move: (cpred_pr iN inz) => [ua ub].
   by apply/(cltSSP (CS_nat ua) (CS_succ ln1)); rewrite - ub.
have r2':CNFp_ax1 ecf (csucc (csucc ln1)).
  rewrite/ecf;move => i min.
  case: (equal_or_not i \0c) => ei0; Ytac0; first split;aww.
have r3': oprodf p (csucc n) = CNFpv1 ecf (csucc (csucc ln1)).
  rewrite eq3 nkv1 r3 {2}/CNFpv1 (oprod_f1r (OS_CNFp0 r2') r1').
  apply: f_equal2.
    rewrite /cantor_pmon/ecf;Ytac0; aw.
    rewrite (CNFp_pr1 dp0 c0N).
    rewrite /CNFp_value2 - p0v; reflexivity.
  apply:(oprodf_exten r1') => i lin.
  rewrite /ecf /cantor_pmon (cpred_pr2 (NS_lt_nat lin r1')).
  by rewrite (Y_false (@succ_nz i)). 
have r4': let p'0 := fun i : Set => p (csucc i) in
   Q (ecf \0c) = oprodf p'0 (first_non_int p'0 n).
   rewrite/ecf; Ytac0; rewrite pr2_pair;  reflexivity.
have r5':(P (ecf \0c)) = odegree (p \0c).
  by  rewrite /ecf Y_true; aw.
exists ecf, (csucc ln1); split => //.
Qed.

Lemma ord_factor10 p n: ofact_list_succ p (csucc n) -> natp n -> 
   ~ (natp (p \0c)) ->
   exists ec m, [/\ natp m, CNFp_ax ec (csucc m),
                  oprodf p (csucc n) = CNFpv ec (csucc m) &
    [/\ ec (csucc m)  = J \0o \1o,
     let p' := p \o csucc in  Q(ec \0c) =  oprodf p' (first_non_int p' n) & 
     P(ec \0c) = odegree (p \0c) ]].
Proof.
move => ha hb hc.
move:(ord_factor9 ha hb hc) => [ec [m [mN r2 r3 r4 r5]]].
pose ec1 i := Yo (i = csucc m) (J \0o \1c)  (ec i).
have smN := NS_succ mN.
have ec1mv: ec1 (csucc m) = J \0o \1c by rewrite /ec1; Ytac0.
have xx: ec1 \0c = ec \0c by  rewrite /ec1 (Y_false (nesym (@succ_nz m))).
rewrite - xx in r4.
have e10v: P(ec1 \0c) = odegree (p \0c). by ue.
have ax1: CNFp_ax ec1 (csucc m).
  rewrite /ec1;split; last by Ytac0; split; aww; apply: PN1.
  by move => i lim; rewrite /ec1 (Y_false (proj2 lim)); apply: r2.
have v1: oprodf p (csucc n) = CNFpv ec1 (csucc m).
  rewrite /CNFpv r3 /ec1; Ytac0; aw; rewrite oopow0 (oprod1r OS1).
   set u := CNFpv1 _ _; set v := CNFpv1 _ _.
   have -> : v = u.
     by apply:(oprodf_exten smN) => i [_ lin]; rewrite/cantor_pmon; Ytac0.
   have ou : ordinalp u by apply:(OS_CNFp1 r2 smN).
   by rewrite (oprod1l ou).
by exists ec1, m; split.  
Qed.
  

Lemma ord_factor11 p n: ofact_list_succ p n -> 
   exists ec m, [/\ natp m, CNFp_ax ec m,
                  oprodf p n = CNFpv ec m &
    ec m  = J \0o (oprodf p (first_non_int p n)) ].
Proof.
move => [[ nN  ax1 ax2] ax3].
move: (first_non_int_p1 p nN). 
set k:= first_non_int p n. move => [kp1 kp2].
have lekn: k <=c n.
  by case: kp1;[ move ->; apply:(cleR (CS_nat nN))| case; case].
have kN := NS_le_nat lekn nN.
set c0 := oprodf p k.
have c0N: posnatp c0.
   apply:(ord_factor9_aux kN kp2) => i ilk.
   exact: (ax3 _ (clt_leT ilk lekn)).
case: kp1 => kp1.
  pose ec (i: Set) := J \0o c0.
  move: (OS_nat(proj1 c0N)) => oc.
  exists ec, \0c; split => //.
  - apply: NS0.
  - split; [ by move => i /clt0 | rewrite/ec;split; aww].
  - rewrite /CNFpv CNFp_0/ec; aw.
    by rewrite  oopow0 (oprod1l oc) (oprod1r oc) /c0 kp1.
move: kp1 => [lkn nn].
have kv1 := (cdiff_pr (proj1 lkn)).
case: (equal_or_not (n -c k) \0c) => dnz.
  by case: (proj2 lkn); rewrite -kv1 dnz (csum0r (CS_nat kN)).
move: (cpred_pr (NS_diff k nN) dnz); set m := cpred _; move => [mN mv].
pose p' i := p (i +c k).
have hb: ofact_list_succ p' (csucc m). 
  have h0 i:  i <c csucc m ->  i +c k <c n.
    by move => link; move: (csum_Meqlt kN link); rewrite - mv kv1 csumC.
  split.
    split; [exact:(NS_succ mN) | by move => i /h0 lin; apply:ax1 |].
    by move=> i iN /h0;rewrite /p' (csum_Sn _ iN);apply: (ax2 _ (NS_sum iN kN)).
  by move => i /h0 lin; apply:ax3.
have hc : ~ natp (p' \0c) by rewrite /p' (csum0l (CS_nat kN)).
move: (@ord_factor9 p' m hb mN hc) => [ec [q[r1 r2 r3 r4 r5]]].
have  sqN := NS_succ r1.
pose ec' i := Yo (i = (csucc q)) (J \0o c0) (ec i).
have r6:   CNFp_ax ec' (csucc q).
  rewrite/ec';split.
     by move => i lin; rewrite (Y_false (proj2 lin)); apply: r2.
  Ytac0; split; aww.
have r7:  oprodf p n = CNFpv ec' (csucc q).
   have ra: CNFpv1 ec' (csucc q) = CNFpv1 ec (csucc q).
     apply: (oprodf_exten sqN).
     by rewrite /ec'/cantor_pmon=>  i  /proj2 lin; Ytac0.
  rewrite /CNFpv ra - r3 /ec'; Ytac0; aw.
  rewrite oopow0 (oprod1l (OS_nat (proj1 c0N))).
  have obl : ord_below p (k +c (n -c k)).
    by rewrite kv1; move => i /(ax1); case.
  by rewrite /c0 -{1} kv1 (oprod_fA kN (NS_diff k nN) obl) mv. 
have r8: ec' (csucc q) = J \0o c0 by rewrite /ec' /=; Ytac0.
by  exists ec', (csucc q). 
Qed.
  
  
Lemma ord_factor12 p n p' n':
  ofact_list_succ p n -> 
  ofact_list_succ p' n' ->
  oprodf p n = oprodf p' n' ->
  (n = n' /\ same_below p p' n).
Proof.
move => ha. have nN:= (proj31 (proj1 ha)).
move: (cleR (CS_nat nN)) => lnn; move: n nN p {-2} n p' n' lnn ha (nN).
have H0 p n: ofact_list_succ p n -> ord_below p n.
 by  move/proj1/ ord_factor1.
have H1 p n: ofact_list_succ p n  -> oprodf p n = \1o -> n = \0c.
  move => Ha;move: (Ha) =>[[nN ax1 _] _].
  case: (equal_or_not n \0c) => // np.
  move:(cpred_pr nN np) => [mN mv]; rewrite mv (oprod_fS _ mN).
  move:(H0 _ _ Ha); rewrite {1}mv => /(true_below_rec mN) [oo1 oo2].
  move/(oprod2_one (OS_oprodf mN oo1) oo2) =>[_ sf1].
  by move: (ax1 _  (cpred_lt nN np)) => [_ /proj2]; case.
have H2 p k n: ofact_list_succ p (k +c n) -> natp k -> natp n ->
   ofact_list_succ (fun i  => p (i +c k)) n.
  move => [[_ ax1 ax2] ax3] kN nN; split.
    split; first exact.
      by  move => i lin; apply: ax1; rewrite csumC; apply: csum_Meqlt.
    move => i iN lin; rewrite (csum_Sn _ iN); apply: ax2; first fprops.
    by rewrite -(csum_Sn _ iN) csumC; apply: csum_Meqlt.
  by  move => i lin; apply: ax3; rewrite csumC; apply: csum_Meqlt.
apply: Nat_induction.
  move => p n p' n' /cle0 -> _ _ osp  /esym.
  by rewrite oprod_f0 => eq1; move:(H1 _ _ osp  eq1) ->; split => // i /clt0.
move => B BN Hrec p n p' n';case/ cle_eqVlt => lnB; last first.
  move/(cltSleP BN): lnB; apply:Hrec. 
move => ofl1 nN  ofl2 eq1.
move:(ord_factor11 ofl1) => [ec1 [m1 [mn1 ax1 prod1 em1]]].
move:(ord_factor11 ofl2) => [ec2 [m2 [mn2 ax2 prod2 em2]]].
have eq2: CNFpv ec1 m1 = CNFpv ec2 m2 by rewrite-  prod1 - prod2.
move: (CNFp_unique ax1  ax2 mn1 mn2 eq2) => [res1 res2].
move:(f_equal Q (res2 _ (cltS mn1))); rewrite em1 res1 em2; aw.
have n'N := proj31 (proj1 ofl2).
move:(first_non_int_p1 p nN) (first_non_int_p1 p' n'N).
set k1 :=(first_non_int p n); set k2 := (first_non_int p' n').
move =>[k11 k12][k21 k22] eq3.
have lk1n: k1 <=c n.
 by case: k11; [ by move ->; apply: (cleR (CS_nat nN)) | case;case].
have lk2n: k2 <=c n'.
 by case: k21; [ by move ->; apply: (cleR (CS_nat n'N)) | case;case].
move:(NS_le_nat lk1n nN)(NS_le_nat lk2n n'N) => k1N k2N.
have nf1: nat_factor_list p k1.
  have hu i: i <c k1 -> (p i) <o omega0 by move/k12/olt_omegaP.
  move:(H0 _ _ ofl1)=> pax4;move:ofl1 => [[_ pax1 pax2] pax3]; split.
  - by move => i lik; move:(pax4 _ (clt_leT lik lk1n)) => pi.
  -  move => i lik; move:(pax1 _ (clt_leT lik lk1n)) => pi.
    move:(oltNge(hu _ lik)) => npi. 
    case/ord_prime_p1:pi; first exact.
    - move/ord_ptypeI_prop => [_ /npi]; case.
    - move/ord_ptypeL_prop => [_ /npi]; case.
  - move => i iN lik; move:(hu _ lik) (hu _ (clt_ltT (cltS iN) lik)) => f1 f2.
    exact:(proj1 (pax2 _ iN (clt_leT lik lk1n))  f2 f1).
have nf2: nat_factor_list p' k2.
  have hu i: i <c k2 -> (p' i) <o omega0 by move/k22/olt_omegaP.
  move:(H0 _ _ ofl2)=> pax4;move:ofl2 => [[_ pax1 pax2] pax3]; split.
  - move => i lik; exact:(pax4 _ (clt_leT lik lk2n)).
  - move => i lik; move:(pax1 _ (clt_leT lik lk2n)) => pi.
    move:(oltNge(hu _ lik)) => npi.
    case/ord_prime_p1:pi; first exact.
    - move/ord_ptypeI_prop => [_ /npi]; case.
    - move/ord_ptypeL_prop => [_ /npi]; case.
  - move => i iN lik; move:(hu _ lik) (hu _ (clt_ltT (cltS iN) lik)) => f1 f2.
    exact:(proj1 (pax2 _ iN (clt_leT lik lk2n))  f2 f1).
move:(@nat_prime_p6 p p' k1 k2 k1N k2N nf1 nf2 eq3) => [k1k2 sbk].
case: (equal_or_not k1 \0c) => k1nz; last first.
  move:(cdiff_pr lk1n); move:(NS_diff k1 nN); set n1 := n -c k1.
  move:(cdiff_pr lk2n); move:(NS_diff k2 n'N); set n2 := n' -c k2.
  move => n2N n'v n1N nv.
  move: (H0 _ _ ofl1) (H0 _ _ ofl2); rewrite - nv -n'v => cax1 cax2.
  move/posnat_ordinalp:(proj33(proj2 ax1)); rewrite em1 -/k1; aw => fcp.
  move: eq1; rewrite -nv -n'v (oprod_fA k1N n1N cax1)(oprod_fA k2N n2N cax2).
  rewrite - eq3.
  set p1 := fun i =>  p (i +c k1);set p2 := fun i =>  p' (i +c k2).
  have oo1: ordinalp (oprodf p1 n1).
    apply:(OS_oprodf n1N) => i lin.
    by apply:cax1; rewrite csumC; apply:(csum_Meqlt k1N lin).
  have oo2: ordinalp (oprodf p2 n2).
    apply:(OS_oprodf n2N) => i lin.
    by apply:cax2; rewrite csumC; apply:(csum_Meqlt k2N lin).
  move/(oprod2_simpl oo1 oo2 (proj1 fcp)) => eq4.
  have aux1: n1 <=c B.
    by apply/(cltSleP BN); rewrite - lnB - nv csumC; apply:csum_M0lt.
  rewrite -nv in ofl1; move: (H2 _ _ _ ofl1 k1N n1N)=> aux2.
  rewrite -n'v in ofl2; move: (H2 _ _ _ ofl2 k2N n2N)=> aux3.
  move:(Hrec p1 n1 p2 n2 aux1 aux2 n1N aux3 eq4)=> [n1n2 eq5]; split.
    by rewrite k1k2 n1n2.
  move => i lik; case:(cleT_el (CS_nat k1N) (proj31_1 lik)); last first.
      apply: sbk.
  move => kli; move:(cdiff_pr kli) => iv.
  move: (eq5 (i -c k1)); rewrite /p1 /p2 - k1k2 csumC iv; apply.
  have iN := (NS_lt_nat lik (NS_sum k1N n1N)).
  by apply:(csum_lt2l k1N (NS_diff k1 iN) n1N); rewrite iv. 
move:k11; rewrite k1nz;case => nz.
  move/esym: eq1;rewrite -nz oprod_f0 => eq1.
  by move:(H1 _ _ ofl2 eq1) ->; clear;  split  => // i /clt0.
move:k21; rewrite -k1k2 k1nz;case => nz'.
  move:eq1;rewrite - nz' oprod_f0 => eq1.
  by move:(H1 _ _ ofl1 eq1) ->; clear;  split  => // i /clt0.
clear k1 k2 k1N k2N k12 k22 eq3 lk1n lk2n nf1 nf2 k1k2 sbk k1nz.
clear mn1 ax1 prod1 em1 mn2 ax2 prod2 em2 eq2 res1 res2.
clear ec1 ec2 m1 m2.
move:nz nz' => [/proj2 /nesym nz pnz] [/proj2 /nesym nz' pnz'].
move:(cpred_pr nN nz) (cpred_pr n'N nz').
set m1 := (cpred n); set m2 := (cpred n'). 
move => [m1N nv][m2N nv'].
rewrite nv in ofl1 eq1; rewrite nv' in ofl2 eq1.
move:(ord_factor10 ofl1 m1N pnz) (ord_factor10 ofl2 m2N pnz').
move => [ec1 [q1 [q1N ax1 f1v [_  _ e10]]]].
move => [ec2 [q2 [q2N ax2 f2v [_ _ e20]]]].
move: (eq1); rewrite f1v f2v => eq2.
move:(CNFp_unique ax1 ax2 (NS_succ q1N) (NS_succ q2N) eq2)=> [_ e1e2].
move: (f_equal P (e1e2 _ (succ_positive (csucc q1)))).
rewrite e10 e20 => eqa.
clear ec1 ec2 q1 q1N ax1 f1v e10 q2N ax2 f2v e20  eq2 e1e2.
case:(ord_factor8 ofl1 (succ_positive m1));first by move=> [pp _ _]; case: pnz.
case:(ord_factor8 ofl2 (succ_positive m2));first by move=> [pp _ _]; case: pnz'.
move => [op01 _ p0v1] [op02 _ p0v2].
have eq2: p\0c = p' \0c by rewrite p0v1 p0v2 eqa.
move:(Nsucc_rw m1N); rewrite csumC => m1v.
move:(Nsucc_rw m2N); rewrite csumC => m2v.
move: eq1.
rewrite (oprod_f1r (H0 _ _ ofl1) m1N) (oprod_f1r (H0 _ _ ofl2) m2N) - eq2.
rewrite m1v in ofl1; rewrite m2v in ofl2.
move: (H2 _ _ _ ofl1 NS1 m1N)(H2 _ _ _ ofl2 NS1 m2N).
set p1 := (fun i => p (i +c \1c)); set p1' := (fun i => p' (i +c \1c)).
move => ofl1' ofl2'.
have ->: oprodf (fun i => p (csucc i)) m1 = oprodf p1 m1.
  apply: (oprodf_exten m1N) => i lin.
  by rewrite /p1 (Nsucc_rw (NS_lt_nat lin  m1N)).
have ->: oprodf (fun i => p' (csucc i)) m2 = oprodf p1' m2.
  apply: (oprodf_exten m2N) => i lin.
  by rewrite /p1 (Nsucc_rw (NS_lt_nat lin  m2N)).
move:(OS_oprodf m1N (H0 _ _ ofl1'))=> op1.
move:(OS_oprodf m2N (H0 _ _ ofl2'))=> op2 eq3.
have cp: \0o <o (p \0c).
  apply:(ord_ne0_pos op02); rewrite p0v2; apply:osucc_nz.
move:(oprod2_simpl op1 op2 cp eq3) => eq4.
have lm1b: m1 <=c B.
  move: nv; rewrite lnB => ss; move:(CS_nat BN) (CS_nat m1N) => c1 c2.
  rewrite (csucc_inj c1 c2 ss); apply:(cleR c2).
move:(Hrec p1 m1 p1' m2 lm1b ofl1' m1N ofl2' eq4) =>[m1m2 etc]; split.
  by rewrite nv nv' m1m2.
rewrite nv => i lin; case: (equal_or_not i \0c)=> eiz; first by rewrite eiz.
move:(cpred_pr (NS_lt_nat lin (NS_succ m1N)) eiz) => [ha hb].
have hc: cpred i <c m1 by apply/(cltSSP(CS_nat ha) (CS_nat m1N)); rewrite - hb.
by move:(etc (cpred i) hc); rewrite /p1 /p1' -(Nsucc_rw ha) - hb.
Qed.

Lemma ord_factor_unique p n p' n':
  ord_factor_list p n -> 
  ord_factor_list p' n' -> 
  oprodf p n = oprodf p' n' ->
  (n = n' /\ same_below p p' n).
Proof.
move => ha hb eq1.
move:(ord_factor2 ha) => [k1 kb1].
move:(ord_factor2 hb) => [k2 kb2].
move:(ord_factor7 ha hb kb1 kb2 eq1) =>[k1k2].
set m := n -c k1; set m' := n' -c k1; rewrite - k1k2.
set p1 := (fun i => p (i +c k1)); set p1' := (fun i => p' (i +c k1)).
move => sb1 sp1 sp2 eq2.
move:(ha)(hb) =>[nN ax1 ax2] [n'N ax1' ax2'].
move:(proj31 kb1) => lenk1; move:(NS_le_nat lenk1 nN)=> k1N.
move:(proj31 kb2) => lenk2.
move: (cdiff_pr lenk1)=> k1v.
have nax1: ofact_list_succ p1 m.
  have hi i: i <c m -> i +c k1 <c n.
    by move => likn; rewrite - k1v csumC; apply:(csum_Meqlt k1N).
  split; [ split |  exact: sp1 ].
      by apply: NS_diff.
    by move => i /hi lim; apply: ax1. 
  move => i iN lim; move: (ax2 (i +c k1) (NS_sum iN k1N)).
  by rewrite /p1 (csum_Sn _ iN) -{1} (csum_Sn _ iN); apply; apply:hi.
have nax2: ofact_list_succ p1' m'.
  move: (cdiff_pr lenk2)=> k2v.
  have hi i: i <c m' -> i +c k1 <c n'.
    by move => likn; rewrite - k2v csumC - k1k2; apply:(csum_Meqlt k1N).
  split; [ split | exact: sp2 ].
      by apply: NS_diff.
    by move => i /hi lim; apply: ax1'.
  move => i iN lim; move: (ax2' (i +c k1) (NS_sum iN k1N)).
  by rewrite /p1' (csum_Sn _ iN) -{1} (csum_Sn _ iN); apply; apply:hi.
move:(NS_diff k1 nN)(NS_diff k1 n'N) => mN mN'.
move: (@ord_factor12 p1 m p1' m' nax1 nax2 eq2) =>[mm etc]; split.
 by rewrite - (cdiff_pr lenk1) - (cdiff_pr lenk2) - k1k2 -/m mm.
move => i lin.
case: (cleT_el (CS_nat k1N) (proj31_1 lin)); last by apply:sb1.
move => ik1; move:(cdiff_pr ik1) => iv.
move:(etc (i -c k1)); rewrite /p1/p1' csumC iv; apply.
move:(NS_lt_nat lin nN)  =>iN.
by move:(csum_lt2l k1N (NS_diff k1 iN) mN); rewrite -/m iv k1v; apply.
Qed.

Lemma ord_factor_exits x: \0o <o x ->
  exists p n, [/\ ord_factor_list p n, natp n & x = oprodf p n].
Proof.
move => xp; move:(CNFp_exists xp) => [p [n  [[ax1 ax2] nN ->]]].
have Hu a: posnatp a -> natp a /\ \1c <=c a.
  by  move=> [aN /proj2/nesym ap]; split => //;apply: (cge1 (CS_nat aN)). 
rewrite /CNFpv.
move: (Hu _ (proj33 ax2)); set lc := Q (p n).
move => [lcN lcp]; move:(nat_prime_p7 lcN lcp) => [p1 [n1 [axp1 n1N f1v]]].
move: (CNFr_exists (proj32 ax2)) => [f [n2 [n2N axf2 ->]]].
set y := oopow _. 
pose oo t := oopow (oopow t).
have oop t: ordinalp t -> ord_prime (oo t).
  by move => ot;apply/ord_prime_p1; constructor 3; exists t.
pose r i := (oo (f (cpred (n2 -c i)))).
have oopm  a b: a <=o b -> oo a <=o oo b.
  move => h; exact  (opow_Mo_le (opow_Mo_le h)).
have oopsm  a b: a <o b -> oo a <o oo b.
  move => h; exact  (opow_Mo_lt (opow_Mo_lt h)).
have ooi a b: ordinalp a -> ordinalp b -> oo a = oo b -> a = b.
  by move => oa ob eq; case: (oleT_ell oa ob) => // /oopsm; rewrite eq; case.
have of2: ord_factor_list r n2.
  split; first exact: n2N.
    by move => i lin; apply: oop; apply (proj1 axf2); apply:cdiff_lt_symmetry.
  move => i iN ltsin.
  move:(cdiff_A1 n2N iN (proj1 ltsin)); set j1 := cpred _ => j1v.
  move: (NS_diff (csucc i) n2N); rewrite - j1v => j1N.
  have j1nz: j1 <> \0c.
    move=> h; move: ltsin => [h']; case; move:(cdiff_pr h').
    by rewrite - j1v h csum0r //; apply: CS_succ.
  have lt1: j1 <c n2.
    rewrite - (cdiff_pr (proj1 ltsin)) - j1v csumC; apply:(csum_M0lt j1N).
    apply: succ_nz.
  move:(cpred_pr j1N j1nz) => [pj1 pj1v].
  move: (proj2 axf2 (cpred j1));rewrite - pj1v => h; move:(h pj1 lt1) => lt2.
  split.
    move: (oopm _ _ (ole0x (proj32 lt2))).
    by rewrite /oo oopow0 oopow1 => W /oltNge.
  move => q op; rewrite /r - j1v -/(oo _) => eq1; exists (f j1) => //.
  by rewrite -(ooi _ _ (proj31 lt2) op eq1).
have Hw i: i <c n2 ->   cpred (n2 -c i) <c n2.
  move => lin2; have iN := (NS_lt_nat lin2 n2N).
  move/(cleSltP iN): lin2 => sil2n.
  rewrite (cdiff_A1 n2N iN sil2n); apply:(cdiff_Mlt n2N n2N sil2n).
  apply: (csum_M0lt n2N (@succ_nz _)).
have Hv i : i <c n2 -> limit_ordinal (r i).
  move => lin2; apply:indecomp_limit2; apply:oopow_pos.
  apply:(proj1 axf2 _ (Hw i lin2)).
have yv: y = oprodf r n2.
  rewrite (proj33 (@ord_factor4 r n2 of2  Hv)).
  apply: f_equal; apply:(osumf_exten n2N) => i il2.
  have ofi := (proj1 axf2 _ il2).
  have iN := (NS_lt_nat il2 n2N).
  move/(cleSltP iN): il2 => sil2n.
  rewrite (cdiff_A1 n2N iN sil2n) /r (double_diff n2N sil2n) (cpred_pr2 iN).
  by rewrite (odegree_opow (OS_pow OS_omega ofi)) (odegree_opow ofi).
suff: (exists p3 n3, [/\ ofact_list_succ p3 n3, natp n3, 
   (\0c <c n3 -> ord_ptypeI (p3 \0c)) &
  oprodf p3 n3 = CNFpv1 p n ]).                    
  move => [p3 [n3 [[axp3 asp3] n3N p30_spec eq3]]].
  set n4 := (n2 +c n1) +c n3.
  pose p4 i := Yo (i <c n2) (r i)
         (Yo (i <c (n2 +c n1)) (p1 (i -c n2)) (p3 (i -c (n2 +c n1)))).
  have n21N := (NS_sum n2N n1N).
  have n4N := (NS_sum n21N n3N).
  have all_prime: forall i, i <c n4 -> ord_prime (p4 i).
    move => i lin; rewrite /p4; move:(NS_lt_nat lin n4N) => iN.
    case: (NleT_el n2N iN) => n2i; last first.
      Ytac0; exact:(proj32 of2 i n2i).
    rewrite (Y_false (cleNgt n2i)); case (NleT_el n21N iN) => n21i.
      rewrite (Y_false (cleNgt n21i)); apply: (proj32 axp3).
      apply: (csum_lt2r n21N (NS_diff (n2 +c n1) iN) n3N).
      by rewrite csumC (cdiff_pr n21i) csumC.
    have lt1: i -c n2 <c n1.
      apply:(csum_lt2r n2N (NS_diff n2 iN) n1N).
      by rewrite csumC (cdiff_pr n2i) csumC.
    Ytac0; exact:(nat_prime_p1 (proj32  axp1 _ lt1)). 
  have ofl4: ord_factor_list p4 n4.
    split; [exact | exact |  move => i iN lin4; rewrite /p4].
    case: (NleT_el n2N iN) => n2i; last first.
      case:(NleT_el n2N (NS_succ iN)) => lt3; last first.
        Ytac0; Ytac0; exact:(proj33  of2 i iN lt3).
      move/(cleSltP iN): (n2i) => lt4.
      move: (cleA lt3 lt4) => sin2.
      have lt5: ~ (csucc i <c n2) by rewrite - sin2; case.
      Ytac0; Ytac0; rewrite sin2 cdiff_nn.
      have ha: cpred (n2 -c i) <c n2 by apply: Hw.
      move: (oopm _ _ (ole0x (proj1 axf2 _ ha))).
      rewrite -/(r i) /oo oopow0 oopow1 => /oltNge W.
      split; [ by move/W | move => q op uv].
      move: (indecomp_limit2 (oopow_pos op)); rewrite - uv.
      set u := Yo _ _ _ => lu.
      suff su: osuccp u by case: (limit_nonsucc' lu su).
      rewrite /u - sin2; case: (equal_or_not n1 \0c) => n1z.
        have nn2: ~(n2 <c n2) by case.
        have  n20:= (csum0r (CS_nat n2N)).
        move: lin4; rewrite /n4 n1z n20 - sin2; Ytac0.
        case: (equal_or_not \0c n3) => [n3z | /(strict_pos_P n3N) /asp3 n3p ].
           by rewrite -n3z n20.
        by move => _; rewrite cdiff_nn.
      rewrite (Y_true (csum_M0lt n2N n1z)).  
      by move/(strict_pos_P1 n1N): n1z => /(proj32 axp1)/ord_ptypeF_prop [].
    rewrite (Y_false (cleNgt n2i)) (Y_false (cleNgt (cleT n2i (cleS iN)))).
    case: (NleT_el n21N iN) => n21i; last first.
      case:(NleT_el n21N (NS_succ iN)) => lt3; last first.
         have diN := (NS_diff n2 iN).
         have lt1 :(csucc (i -c n2)) <c n1.
           apply: (csum_lt2r n2N  (NS_succ diN) n1N).
           by rewrite (csum_Sn _ diN) csumC (cdiff_pr n2i) csumC.
        Ytac0; Ytac0; rewrite  (cdiffSn iN n2i).
        split; first by  move => _ _; apply: (proj33 axp1 _ diN lt1).
        move /olt_omegaP :(proj31 (proj32 axp1 _ lt1)) => lt4 q op H.
        move: lt4; rewrite H => /oltNge; case; rewrite -{1}(opowx1 OS_omega).
        apply/opow_Mo_le; rewrite - (opowx0 omega0);apply/opow_Mo_le.
        by apply: ole0x.
      have le4: n2 +c n1 = csucc i by  apply:(cleA lt3); apply/(cleSltP iN).
      have lt5: ~(csucc i <c csucc i) by case.
      Ytac0; rewrite le4 (Y_false lt5) cdiff_nn.
      have lt6: i -c n2 <c n1 by apply: (cdiff_Mlt n1N iN n2i); rewrite csumC.
      move:(proj32 axp1 _ lt6) => np6.
      have n3p: \0c <c n3.
        apply /(strict_pos_P1 n3N) => n3z; case: (proj2 lin4).
        by rewrite /n4 - le4 n3z (csum0r (CS_sum2 n2 n1)).
      move: (p30_spec n3p) => /ord_ptypeI_prop [wp1 wp2].
      split; first by move => _ /oleNgt; case.
      move => q op pv; case:(limit_nonsucc' _ wp1); rewrite pv.
      by apply:indecomp_limit2; apply:(oopow_pos op).
    have lt5 := (cleT n21i (cleS iN)).
    rewrite (Y_false (cleNgt n21i))(Y_false (cleNgt lt5)).
    have: csucc i -c (n2 +c n1) <c n3. 
      apply: (csum_lt2r n21N (NS_diff (n2 +c n1) (NS_succ iN)) n3N).
      by rewrite csumC (cdiff_pr lt5) csumC.
    rewrite (cdiffSn iN n21i). move => lt4.
    exact: (proj33 axp3 _ (NS_diff (n2 +c n1) iN) lt4).
  move:(ord_factor1 ofl4) => obl4.
  have obl4s: ord_below p4 (n2 +c n1).
    move => i lin; apply:obl4; apply: (clt_leT lin); apply:csum_M0le; fprops.
  have ->:  (y *o lc) *o CNFpv1 p n = oprodf p4 n4.
    rewrite (oprod_fA n21N n3N obl4)(oprod_fA n2N n1N obl4s).
    have <-: y = oprodf p4 n2.
      by rewrite yv; apply: (oprodf_exten n2N) => i lin; rewrite /p4; Ytac0.
    set u2 := oprodf _ _; set u3 := oprodf _ _.
    have ->: CNFpv1 p n  = u3.
       rewrite - eq3; apply:(oprodf_exten n3N) => i lin.
       have le1: n2 +c n1 <=c  i +c (n2 +c n1).
           apply:csum_Mle0; fprops.
       move:(cleT (csum_M0le n1 (CS_nat n2N)) le1) => le2.
       rewrite /p4 (Y_false (cleNgt le1)) (Y_false (cleNgt le2)).
       by rewrite (cdiff_pr1  (NS_lt_nat lin n3N) n21N).
   have <- //: lc = u2.
   rewrite - f1v;apply: (oprodf_exten n1N) => i lin.
   have le1: i +c n2 <c n2 +c n1 by rewrite csumC;exact: (csum_Meqlt n2N lin).
   move:(cleNgt (Nsum_M0le i n2N)); rewrite csumC => lt2.
   by rewrite /p4; Ytac0; Ytac0; rewrite (cdiff_pr1  (NS_lt_nat lin n1N) n2N).
  by exists p4, n4.
have ax2' : forall i, i <c n -> posnatp (Q (p i)).
  by  move => i /ax1/proj33.
clear y oo oop r oopm oopsm ooi of2 Hw Hv yv.
clear p1 n1 axp1 n1N f1v f  n2 axf2 n2N lc lcN lcp  ax2.
move: n nN ax1 ax2'; apply: Nat_induction.
   move => _ _; exists (fun i:Set => \1c), \0c; split => //.
  - split; first  by split; [ exact:NS0 | move => i /clt0 | move => i _ /clt0 ].
     by move => i /clt0.
   - apply: NS0.
   - by case.
   - by rewrite /CNFpv1 oprod_f0 oprod_f0.
move => n nN Hrec ax1 ax2.
move:(true_below_rec nN ax1) =>[ax11 [_ ax12 _]].
move:(true_below_rec nN ax2) =>[ax21 ax22].
move: (Hrec ax11 ax21) =>[p1 [n1 [r1 n1N r2 r3]]].
move: (Hu _ ax22)=> [lcN lcp].
move:(nat_prime_p7 lcN lcp) => [p2 [n2 [axp2 n2N f2v]]].
pose f1:= osucc (oopow (P (p n))). 
pose p3 i := Yo (i <c n1) (p1 i) (Yo (i = n1) f1  (p2 (i -c (csucc n1)))).
have sn1N:= (NS_succ n1N). 
move: (NS_sum sn1N n2N);set n3 := (csucc n1) +c n2; move => n3N.
have r5: \0c <c n3 -> ord_ptypeI (p3 \0c).
  move => r3p; rewrite /p3; case: (equal_or_not n1 \0c) => n1z.
    have nnO: ~(\0c <c \0c) by case.
    by rewrite n1z; Ytac0; Ytac0; exists (P (p n)).  
  by move /(strict_pos_P1 n1N) :n1z => n1p; Ytac0; apply: r2.
have of2x:= (OS_pow OS_omega (proj32_1 ax12)).
have f1p: ord_ptypeI f1 by exists ( P(p n)).
have alsp i: i <c n3 -> osuccp (p3 i).
  move => lin; rewrite /p3.
  have iN:= NS_lt_nat lin n3N.
  case: (NleT_el n1N iN) => lt1; last by Ytac0; exact: (proj2 r1 i lt1).
  rewrite (Y_false (cleNgt lt1)).
  case: (cle_eqVlt lt1) => lt2.
     by rewrite lt2 (Y_true (erefl i)) /f1; exists (oopow (P (p n))).
  rewrite (Y_false (nesym (proj2 lt2))).
  move/(cleSltP n1N): lt2 => lt3.
  have lt4: i -c csucc n1 <c n2 by apply:(cdiff_Mlt n2N iN lt3);rewrite csumC.
  by case: (ord_ptypeF_prop (proj32 axp2 _ lt4)).
have opl i: i <c n3 -> ord_prime (p3 i).
  move => lin; rewrite /p3.
  have iN:= NS_lt_nat lin n3N.
  case: (NleT_el n1N iN) => lt1; last first.
    Ytac0; exact: (proj32 (proj1 r1) i lt1).
  rewrite (Y_false (cleNgt lt1)).
  case: (cle_eqVlt lt1) => lt2.
    rewrite lt2 (Y_true (erefl i)) /f1.
    by apply:(succ_pow_omega_prime (proj32_1 ax12)).
  rewrite (Y_false (nesym (proj2 lt2))).
  move/(cleSltP n1N): lt2 => lt3.
  have lt4: i -c csucc n1 <c n2.
    by apply:(cdiff_Mlt n2N iN lt3);rewrite csumC.
  exact: (nat_prime_p1 (proj32 axp2 _ lt4)).
have r4 : ofact_list_succ p3 n3.
  split; [ split; [ exact | exact | ] | exact].
  move => i iN lin3; rewrite /p3.
  move: (ord_ptypeI_prop f1p) => [f1p1 f1p2].
  case: (NleT_el n1N iN) => lin1; last first.
    move/(cleSltP iN): (lin1) => /cle_eqVlt; case => lt2.
      have nn: ~(csucc i <c n1) by rewrite lt2; case. 
      Ytac0; Ytac0; Ytac0; split;first by move => _ /oltNge; case.
      move => q op eqf1. 
      have lf1: limit_ordinal f1.
        by rewrite eqf1; apply:indecomp_limit2; apply:oopow_pos.
      case: (limit_nonsucc' lf1 f1p1).
    Ytac0; Ytac0;exact: (proj33 (proj1 r1) i iN lt2).
  move: (cle_ltT lin1 (cltS iN)) => [lt2 lt3].
  rewrite (Y_false (cleNgt lin1)) (Y_false (cleNgt lt2)); Ytac0.
  have Hk q j:  ordinalp q -> j <c n2 -> p2 j <> oopow (oopow q).
    move => op /(proj32 axp2)/ord_ptypeF_prop [_ /oltNge js] eq; case: js.
    move:(opow_Mo_le (opow_Mo_le (ole0x op))).
    by rewrite oopow0 oopow1 - eq.
  case: (equal_or_not i n1) => ein1; Ytac0.
    rewrite ein1 cdiff_nn; split; first by case/oltNge.
    have lt1: \0c <c n2.
      apply/(strict_pos_P1 n2N)=> n2z;move:(proj2 lin3).
      rewrite /n3 n2z ein1 csum0r;fprops.
    move=> q op eq1; case: (Hk q \0c op lt1 eq1).
  have lt4: csucc n1 <=c i by apply/(cleSltP n1N); split; [exact | apply:nesym].
  have eq4:= (cdiffSn iN lt4); rewrite eq4.
  have lt5: csucc (i -c csucc n1) <c n2.
    rewrite - eq4;apply:(csum_lt2r sn1N (NS_diff (csucc n1) (NS_succ iN)) n2N).
    by rewrite csumC (cdiff_pr (cleSS lin1)) csumC.
  have dN:= NS_diff (csucc n1) iN.
  split; first by move => _ _; exact: (proj33 axp2 _ dN lt5). 
  move => q op eq1; case:(Hk q _ op lt5 eq1).
have r6:  oprodf p3 n3 = CNFpv1 p (csucc n).
  have obl:= (ord_factor1 (proj1 r4)).
  have ln1n3: n1 <c n3 by apply:(clt_leT (cltS n1N)); apply:csum_M0le; fprops.
  have of1: ordinalp (oprodf p1 n1).
    apply:(OS_oprodf n1N) => i lin; move:(obl i (clt_ltT lin ln1n3)).
    by rewrite /p3;Ytac0.
  have of2 :=(OS_succ of2x).
  have Ha i: i <c n2 -> (p3 (i +c csucc n1))  = (p2 i).
    move => lin.
    have lt2: n1 <c i +c (csucc n1).
      by apply:(clt_leT (cltS n1N)); apply:csum_Mle0; fprops.
    rewrite /p3 (cdiff_pr1 (NS_lt_nat lin n2N) sn1N).
    by rewrite (Y_false (cleNgt (proj1 lt2))) (Y_false (nesym (proj2 lt2))). 
  have of3: ordinalp (oprodf p2 n2).
    apply:(OS_oprodf n2N) => i lin. 
    move:(csum_Mlteq sn1N lin); rewrite (csumC n2) -/n3  => lim.
    by move:(obl _ lim); rewrite (Ha i lin).
  rewrite /CNFpv1 (oprod_fS _ nN) {2} /cantor_pmon (CNFp_pr1 ax12  ax22). 
  rewrite /CNFp_value2 - f2v (oprod_fA sn1N n2N obl)  -/(CNFpv1  _ _) - r3.
  rewrite (oprodA of1 of2 of3) (oprod_fS _ n1N); apply: f_equal2.
    apply: f_equal2.
      by apply:(oprodf_exten n1N) => i lin; rewrite /p3; Ytac0.
    have nn: ~ (n1 <c n1) by case.
    by rewrite /p3; Ytac0; Ytac0. 
  by apply:(oprodf_exten n2N) => i /Ha.
by exists p3, n3.
Qed.


End Ordinals3b.
Export  Ordinals3b.
