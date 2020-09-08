(** * Theory of Sets  EIII-6  Infinite sets
  Copyright INRIA (2009-2013) Apics; Marelle Team (Jose Grimm).
*)

(* $Id: sset10.v,v 1.5 2018/09/04 07:57:59 grimm Exp $ *)


Set Warnings "-notation-overridden".
From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Export sset9.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module InfiniteSets.
(** ** EIII-6-1 The set of natural integers *)

(** ** EIII-6-2 Definition of mappings by induction *)

Definition change_target_fun f t := triple (source f) t (graph f).

  
Definition induction_defined1 (h: fterm2) a p :=
   induction_defined0 (fun n x => Yo (n <c p) (h n x) a) a.

Definition induction_defined_set s a E:= 
  change_target_fun (induction_defined s a) E.

Definition induction_defined_set0 h a E:= 
  change_target_fun (induction_defined0 h a) E.
 
Definition induction_defined_set1 h a p E:= 
  change_target_fun (induction_defined1 h a p) E.
 
Lemma induction_defined_pr1 h a p (f := induction_defined1 h a p):
    natp p ->
    [/\  source f = Nat, surjection f, 
      Vf f \0c = a,
      (forall n,  n <c p -> Vf f (csucc n) = h n (Vf f n)) &
      (forall n, natp n -> ~ (n <=c p) -> Vf f n = a)].
Proof.
move=> pN.
move: (induction_defined_pr0 (fun n x => Yo (n <c p) (h n x) a) a).
rewrite /f /induction_defined1.
set g := (induction_defined0 _ a).
move=> [pa pb pc pd]; split => // n np.
  by rewrite (pd _ (NS_le_nat (proj1 np) pN)); Ytac0.
move => cnp.
have nnz: (n <> \0c) by dneg nz; rewrite nz; apply:(cle0n pN).
have [pnN nsp]:= (cpred_pr np nnz).
rewrite nsp (pd _ pnN) Y_false //; apply /(cleSltP pnN); ue.
Qed.
 
Lemma integer_induction1 h a p: natp p ->
  exists! f, [/\ source f = Nat, surjection f,
    Vf f \0c = a ,
     (forall n,  n <c p -> Vf f (csucc n) = h n (Vf f n)) &
     (forall n, natp n -> ~ (n <=c p) -> Vf f n = a)].
Proof. 
move=> pN; exists (induction_defined1 h a p); split.
  by apply: induction_defined_pr1.
have [sx sjx x0 xs xl] := (induction_defined_pr1 h a pN).
move => y  [sy sjy y0 ys yl].
apply function_exten4=>//; first by ue.
rewrite sx; apply: Nat_induction; first by ue.
move=> n nN eq.
case: (p_or_not_p (n <c p)) => np.  
  by rewrite  (xs _ np) (ys _ np) eq.
have snp: (~ (csucc n) <=c p) by move /cleSltP; fprops. 
have snN:= (NS_succ nN).
by rewrite  (xl _ snN snp) (yl _ snN snp).
Qed.

Lemma integer_induction_stable E g  a: 
  inc a E -> (forall x, inc x E -> inc (g x) E) ->
  sub (target (induction_defined g a)) E.
Proof. 
move=> eA agE t tt.
have [sf sjf f0 fn]:=(induction_defined_pr g a).
have [x xsf ->] := ((proj2 sjf) _ tt).
move:x xsf; rewrite sf;apply: Nat_induction; first by ue.
by move=> n nN WE; rewrite fn //; apply: agE.
Qed.

Lemma integer_induction_stable0 E h a: 
  inc a E -> (forall n x, inc x E -> natp n -> inc (h n x) E) ->
  sub (target (induction_defined0 h a)) E.
Proof. 
move=> aE ahE t tt.
have [sf sjf f0 fn] := (induction_defined_pr0 h a).
have [x xsf ->] :=(proj2 sjf _ tt).
move: x xsf;rewrite sf;apply: Nat_induction; first by ue.
by move=> n nN WE; rewrite fn //; apply: ahE.
Qed.

Lemma integer_induction_stable1 E h a p: 
  natp p ->
  inc a E -> (forall n x, inc x E -> n <c p -> inc (h n x) E) ->
  sub (target (induction_defined1 h a p)) E.
Proof. 
move=> pN aE ahE t tt.
have [sf sjf f0 fs lf] := (induction_defined_pr1 h a pN).
have [x xsf ->] :=(proj2 sjf _ tt).
move: x xsf; rewrite sf;apply: Nat_induction; first by ue.
move=> n nN vE.
case:(p_or_not_p (n <c p)) => np.  
  by rewrite (fs _ np); apply: ahE.
rewrite lf; fprops; move /cleSltP; fprops.
Qed.

Lemma change_target_pr f E (g:= change_target_fun f E): 
   function f -> sub (target f) E ->
   (function_prop g (source f) E 
     /\ forall x, inc x (source f) -> Vf g x = Vf f x).
Proof.
move => ff stf; rewrite /g/change_target_fun; saw.
  have h := (sub_trans (f_range_graph ff) stf).
  have [_ pc pb] := ff.
  saw; exact: function_pr.
by move=> x xsf; rewrite /Vf; aw.
Qed.

Lemma induction_defined_pr_set  E g a (f := induction_defined_set g a E):
    inc a E -> (forall x, inc x E -> inc (g x) E) -> 
     [/\ function_prop f Nat E, Vf f \0c = a & 
     forall n, natp n -> Vf f (csucc n)  = g (Vf f n)].
Proof. 
move => aE ag. 
have st:= (integer_induction_stable aE ag).
have [sf [ff _] f0 fs] := (induction_defined_pr g a).
move: (change_target_pr  ff st); rewrite -/(induction_defined_set g a E) -/f.
rewrite sf; move => [pa pd].
split => //; first by rewrite -f0 pd //; exact: NS0.
by move => n nb; rewrite (pd _ (NS_succ nb)) (fs _ nb) -pd.
Qed.

Lemma induction_defined_pr_set0 E h a (f := induction_defined_set0 h a E):
    inc a E -> (forall n x, inc x E -> natp n -> inc (h n x) E) ->
     [/\ function_prop f Nat E, Vf f \0c = a & 
     forall n, natp n -> Vf f (csucc n) = h n (Vf f n)].
Proof. 
move=> aE ag. 
have st := (integer_induction_stable0 aE ag).
have [sf [ff _] f0 fs] := (induction_defined_pr0 h a).
move: (change_target_pr  ff st); rewrite -/(induction_defined_set0 h a E) -/f.
rewrite sf; move => [pa pd].
split => //; first by rewrite -f0 pd //; exact: NS0.
by move => n nb; rewrite (pd _ (NS_succ nb)) (fs _ nb) -pd.
Qed.

Lemma induction_defined_pr_set1  E h a p (f := induction_defined_set1 h a p E):
    natp p ->
    inc a E -> (forall n x, inc x E -> n <c p -> inc (h n x) E) ->
    [/\ function_prop f Nat  E, Vf f \0c = a, 
      (forall n, n <c p -> Vf f (csucc n) = h n (Vf f n)) &
      (forall n, natp n -> ~ (n <=c p) -> Vf f n = a)].
Proof.
move=> pN aE ag. 
have st := (integer_induction_stable1 pN aE ag).
have [sf [ff _] f0 fs1 fs2] := (induction_defined_pr1 h a pN).
move: (change_target_pr  ff st); rewrite -/(induction_defined_set1 h a E) -/f.
rewrite sf; move => [pa pd].
split => //; first by  rewrite -f0 pd //; exact: NS0.
  move => n np.
  have nN:= NS_lt_nat np pN.
  by rewrite (pd _ nN) (pd _ (NS_succ nN)) fs1. 
by move => n nN np; rewrite (pd _ nN) (fs2 _ nN np). 
Qed.



Definition transdef_ord_prop (p:fterm) (f:fterm) x := f x = p (Lg x f).
Definition transdef_ord (p:fterm) x :=
  (Vg (transfiniteg_defined (ordinal_o (osucc x)) p) x).

Lemma transdef_ord_unique p f1 f2:
   (forall x, ordinalp x ->  transdef_ord_prop p f1 x) ->
   (forall x, ordinalp x ->  transdef_ord_prop p f2 x) ->
   f1 =1o f2.
Proof.
move => H1 H2; apply:least_ordinal2' => y oy yp.
by rewrite (H1 y oy) (H2 y oy);f_equal; apply: Lg_exten.
Qed.

Lemma transdef_ord_pr (p:fterm) x: 
  ordinalp x -> transdef_ord_prop p (transdef_ord p) x.
Proof.
pose F y := (transfiniteg_defined (ordinal_o y) p).
have ha: forall y, ordinalp y -> worder (ordinal_o y).
  by move => y oy; apply:ordinal_o_wor.
have hb: forall y, ordinalp y -> transfiniteg_def (ordinal_o y) p (F y).
  move => y oy; apply: (transfinite_pr1 p (ha _ oy)). 
have hd: forall y z g, ordinalp y -> inc z y -> 
  p (restr g (segment (ordinal_o y) z )) = p (Lg z (Vg g)).
  move => y z g oy zy. 
  by rewrite (ordinal_segment oy zy) /restr. 
have he: forall y z, z <o y -> Vg (F y) z = p (Lg z (Vg (F y))).
  move => y z /oltP0 [oz oy lzy]; move: (hb _ oy) => [pa pb pc].
  by rewrite - (hd _ _ _ oy lzy);apply: pc; rewrite ordinal_o_sr. 
have he': forall y z, ordinalp y -> inc z y -> Vg (F y) z = p (Lg z (Vg (F y))).
  move => y z oy  lzy; move: (hb _ oy) => [pa pb pc].
  by rewrite - (hd _ _ _ oy lzy);apply: pc; rewrite ordinal_o_sr. 
have hc: forall z, ordinalp z ->
    forall y1 y2, z <o y1 -> z <o y2 ->  Vg (F y1) z = Vg (F y2) z.
   apply: least_ordinal2 => b ob bp y1 y2 lt1 lt2.
   rewrite (he _ _ lt1) (he _ _ lt2).
   f_equal; apply:Lg_exten => s /(oltP (proj31_1 lt1)) sb; apply: (bp _ sb).
      apply: (olt_ltT sb lt1).
      apply: (olt_ltT sb lt2).
move => ox;set f := (transdef_ord p).
hnf; have <-: Vg (F (osucc x)) x = f x by [].
rewrite (he _ _ (oltS ox)); f_equal; apply: Lg_exten.
move => t /(oltP ox) ltx; move:(proj31_1 ltx) => ot.
apply: (hc _ ot)  (olt_ltT ltx (oltS ox)) (oltS ot).
Qed.


Section StratifiedInduction.
Variable W: property.
Variable H: fterm2.
Variable idx: fterm.
Hypothesis OS_idx: forall x, W x -> ordinalp (idx x).
Hypothesis Wi_coll: forall i, ordinalp i ->
     exists E, forall x,  inc x E <-> (W x /\ idx x <o i).

Definition stratified_set i := 
    choose (fun E => forall x,  inc x E <-> (W x /\ idx x <o i)).

Definition stratified_setr i := 
   Zo (stratified_set (osucc i)) (fun z => idx z = i).

Lemma stratified_setP i (E:= stratified_set i):
   ordinalp i -> (forall x,  inc x E <-> (W x /\ idx x <o i)).
Proof.
move => /Wi_coll h; exact: (choose_pr h).
Qed.

Lemma stratified_setrP i (E:= stratified_setr i):
   ordinalp i -> (forall x,  inc x E <-> (W x /\ idx x = i)).
Proof.
move => oi.
have H1 :=(stratified_setP (OS_succ oi)).
move => x; split; first by move/Zo_P => [/H1 []].
move => [sa sb];apply:Zo_i => //; apply/H1; split => //.
by rewrite sb; apply:oltS. 
Qed.

Definition stratified_fct_aux:= 
  transdef_ord (fun G => Lg (stratified_setr (domain G))
    (fun z =>  (H z (unionb G)))).

Definition  stratified_fct x := Vg (stratified_fct_aux (idx x)) x.

Lemma stratified_fct_aux_p1 x ( g:= stratified_fct_aux) : 
  ordinalp x -> g x = Lg (stratified_setr x) (fun z => H z (unionf x g)).
Proof.
move => ox.
rewrite /transdef_ord_prop /g /stratified_fct_aux.
rewrite (transdef_ord_pr _ ox) /unionb; aw.
apply: Lg_exten => t ts /=; apply: f_equal; set_extens w.
  move => /setUf_P [y yx]. rewrite LgV// => ha; union_tac.
move => /setUf_P [y yx wy]; union_tac; rewrite LgV//.
Qed.

Lemma stratified_fct_pr x  (f := stratified_fct):
  W x -> f x =  H x (Lg (stratified_set (idx x)) f).
Proof.
have H2: forall x,  W x -> f x =  H x (unionf (idx x) stratified_fct_aux).
  move => t wt; move: (OS_idx wt) => oi.
  rewrite /f/stratified_fct (stratified_fct_aux_p1 oi); rewrite LgV //.
  by apply /(stratified_setrP oi).
move => wx; rewrite  (H2 _ wx); apply: f_equal.
have oi := OS_idx wx.
have ha: forall t, ordinalp t -> sgraph (stratified_fct_aux t).
  move => t ot u ;rewrite (stratified_fct_aux_p1 ot). 
  move/funI_P => [w wa ->]; fprops.
have hb: sgraph (unionf (idx x) stratified_fct_aux).
  by move => y /setUf_P [z za]; apply: (ha _ (Os_ordinal oi za)).
have hc: stratified_set (idx x) = domain (unionf (idx x) stratified_fct_aux).
  set_extens t.
    move => /(stratified_setP oi) [h1 h2] ; apply/(domainP hb).
    have oit:= (proj31_1 h2).
    have : inc t (domain (stratified_fct_aux (idx t))).
       rewrite  (stratified_fct_aux_p1 oit); aw; apply/(stratified_setrP oit).
       by split.
    move/(domainP (ha _ oit)) => [y ya]; exists y.
    by apply/setUf_P; exists (idx t) => //; apply/(oltP).
  move => /(domainP hb) [y /setUf_P [z zi]].
  have oz :=  (Os_ordinal oi zi).
  rewrite (stratified_fct_aux_p1 oz).
  move => /funI_P [u /(stratified_setrP oz) [wu iz] /pr1_def ->].
  by apply/(stratified_setP oi); split => //; rewrite iz; apply/(oltP).
have hbb: fgraph (unionf (idx x) stratified_fct_aux).
  split; first by exact.
  move => u v /setUf_P [y1 y1x y1v]  /setUf_P [y2 y2x y2v].
  move: (Os_ordinal oi y1x) (Os_ordinal oi y2x) => oy1 oy2.
  move: y2v; rewrite (stratified_fct_aux_p1 oy2).
  move: y1v; rewrite (stratified_fct_aux_p1 oy1).
  move => /funI_P [z1 z1i z1v] /funI_P [z2 z2i z2v].
  move /(stratified_setrP oy1): z1i => [wz1 iz1].
  move /(stratified_setrP oy2): z2i => [wz2 iz2].
  by rewrite z1v z2v - iz1 - iz2; aw => ->.
symmetry;apply:fgraph_exten.
+ fprops.
+ exact.
+ by aw.
+ aw => t ts; rewrite LgV//;move/(stratified_setP oi):ts => [Wt lt1].
  have oit:= (proj31_1 lt1).
  have h := (stratified_fct_aux_p1 oit). 
  have pa: inc t (stratified_setr (idx t)).
    by apply/(stratified_setrP oit).
  rewrite /f /stratified_fct.
  set u := Vg (stratified_fct_aux (idx t)) t.
  have pb: fgraph (stratified_fct_aux (idx t)) by rewrite h; fprops.
  have pc: inc t (domain (stratified_fct_aux (idx t))) by rewrite h; aw.
  move: (fdomain_pr1 pb pc); rewrite -/u => sa.
  have sb: inc (J t u) (unionf (idx x) stratified_fct_aux).
     by apply/setUf_P; exists (idx t) => //;apply/(oltP oi).
  by move: (pr2_def (in_graph_V hbb sb)); aw. 
Qed.

End StratifiedInduction.


(** ** EIII-6-3 Properties of infinite cardinals *)


Definition aleph0 :=  omega0.

Lemma cardinal_Nat: cardinal Nat = Nat.
Proof. apply: card_card; apply: CS_omega. Qed.

Lemma aleph0_pr1: aleph0 = cardinal Nat. 
Proof. symmetry; exact:cardinal_Nat. Qed.

Lemma CIS_aleph0: infinite_c aleph0. 
Proof. by move /infinite_setP: infinite_Nat; rewrite aleph0_pr1. Qed.

Lemma CS_aleph0: cardinalp aleph0. 
Proof. exact: (proj1 CIS_aleph0). Qed. 

Lemma aleph0_nz: aleph0 <> \0c.
Proof. exact: (infinite_nz CIS_aleph0). Qed.

Lemma infinite_gt1 x: infinite_c x -> \1c <c x.
Proof. by move=> h; apply: clt_fin_inf => //; fprops. Qed.

Lemma infinite_ge2 x: infinite_c x -> \2c <=c x.
Proof. move => h; apply: (cle_fin_inf finite_2 h). Qed.

Lemma infinite_greater_countable1 E:
  infinite_set E -> aleph0 <=c (cardinal E).
Proof.
move=>iE; have cE :=(CS_cardinal E).
by split; [ exact CS_aleph0 | | apply/(omega_P1 (proj1 cE)) ].
Qed.

Lemma infinite_greater_countable E:
  infinite_set E -> exists F, sub F E /\ cardinal F = aleph0.
Proof. 
move=> /infinite_greater_countable1.
rewrite aleph0_pr1 => /eq_subset_cardP1/set_leP [F e /card_eqP /esym ef]. 
by exists F. 
Qed.


Lemma infinite_greater_countable_alt E:
  infinite_set E -> exists F, sub F E /\ cardinal F = aleph0.
Proof. 
move=> /infinite_greater_countable1.
rewrite aleph0_pr1 => /eq_subset_cardP1/set_leP  [F e /card_eqP /esym ef]. 
by exists F. 
Qed.


Lemma cprod_Mle_square x:  x <=cc x \times x.
Proof.
rewrite - cprod2_pr1 - cprod2cr - cprod2cl; set a := cardinal x.
case: (equal_or_not a \0c) => anz.
  by rewrite anz cprod0r;apply: (cleR CS0).
apply:  (cprod_M1le (CS_cardinal x) anz).
Qed.


Lemma equipotent_N2_N: (coarse Nat) \Eq Nat.
Proof.
pose g2 a := (binom (csucc a) \2c).
pose mi n m := n +c (g2 (n +c m)).
have g2N: forall a, natp a -> natp (g2 a).
   move => a aN; apply: (NS_binom (NS_succ aN) NS2).
have miN: forall n m, natp n -> natp m -> natp (mi n m).
  move=> n m nN mN; apply: (NS_sum nN (g2N _  (NS_sum nN mN))).
have ha: forall n m, natp n -> natp m ->  (g2 (n +c m)) <=c (mi n m).
  move=> n m nN mN. 
  apply: Nsum_Mle0; apply:(g2N _ (NS_sum nN mN)).
have hc: forall n, natp n -> g2 (csucc n) = (g2 n) +c (csucc n).
  by move=> n nN; rewrite /g2 (binom_2plus0 (NS_succ nN)). 
have hb: forall n m, natp n -> natp m ->  (mi n m) <c (g2 (csucc (n +c m))).
  move=>  n m nN mN.
  have sN:= (NS_sum nN mN).
  rewrite (hc _ sN) /mi csumC; apply:(csum_Meqlt (g2N _ sN)). 
  apply /(cltSleP sN); apply: (Nsum_M0le _ nN).
exists (Lf (fun z => (mi (P z) (Q z))) (coarse Nat) Nat); hnf;saw.
apply: lf_bijective; first by move => t /setX_P  [_ pN qN]; apply:miN.
  move=> u v /setX_P [pu puN quN] /setX_P [pv pvN qvN] sm.
  suff ss: (P u) +c (Q u) = (P v) +c (Q v).
    move: sm; rewrite /mi ss => ss2.
    have wN:= (g2N _ (NS_sum pvN qvN)).
    have sp:= (csum_eq2r wN puN pvN ss2).
    rewrite sp in ss; apply: (pair_exten pu pv sp).  
    apply: (csum_eq2l pvN quN qvN ss).
  move: (ha _ _ puN quN)(hb _ _ puN quN)(ha _ _ pvN qvN)(hb _ _ pvN qvN).
  rewrite sm; move=> r1 r2 r3 r4.
  move: (cle_ltT r1 r4)(cle_ltT r3 r2)=> r5 r6.
  have ls2: forall z, natp z -> \2c <=c  (csucc (csucc z)).
    move => z zN; rewrite - succ_one - succ_zero.
    apply:(cleSS (cleSS (cle0n zN))).
  suff gi: forall x y, natp x -> natp y -> 
      (g2 x) <c (g2 (csucc y)) -> x <=c y.
    move: (NS_sum puN quN) (NS_sum pvN qvN) => sun svn.
    apply: (cleA (gi _ _ sun svn r5)(gi _ _ svn sun r6)).
  move=> x y xN yN; rewrite /g2.
  move: (NS_succ xN) (NS_succ yN) (NS_succ (NS_succ yN)) => qa qb qc.
  rewrite - (binom_monotone2 NS2 qa qc card2_nz (ls2 _ xN) (ls2 _ qb)). 
  by move /(cltSleP qb)/(cleSSP (CS_nat xN)(CS_nat yN)).
move=> y yN.
have g2z: g2 \0c = \0c by rewrite /g2 succ_zero (binom_bad NS1 NS2 clt_12).
case: (equal_or_not y \0c) => yz.
  rewrite yz; exists (J \0c \0c); first exact: (setXp_i NS0 NS0).
  by rewrite pr1_pair pr2_pair /mi (Nsum0l NS0) g2z (Nsum0l NS0). 
have pc:  y <c (g2 (csucc y)).
  rewrite (hc _ yN) (csum_nS _ yN) csumC;apply/(cltSleP (NS_sum yN (g2N _ yN))).
  apply: (Nsum_M0le _ yN). 
case: (least_int_prop2 (NS_succ yN) pc (p := fun k =>y <c (g2 k))).
  by rewrite g2z; move=> /clt0. 
set x := cpred _; move => [xN psx npx].
have bp:= (hc _ xN).
have g2Nx:= (g2N _ xN).
have p1: y <=c ((g2 x) +c x).
  by apply /(cltSleP (NS_sum g2Nx xN)); rewrite - (csum_nS _ xN) - bp.
have p2: g2 x <=c y by case: (cleT_el (CS_nat g2Nx) (CS_nat yN)).
move: (cdiff_pr p2); move:(NS_diff (g2 x) yN);set n:= (y -c (g2 x)).
move=> nN p3;rewrite -p3 in p1. 
have lenx:= (csum_le2l g2Nx nN xN p1).
move: (cdiff_pr lenx); move:(NS_diff n xN); set m:= (x -c n).
move=> mN p4;rewrite -p4 in p3.
exists (J n m); first by apply: setXp_i. 
by rewrite /mi pr1_pair pr2_pair csumC p3.
Qed.
  
Theorem equipotent_inf2_inf E: infinite_c E ->
  E ^c \2c = E.
Proof. 
move=> ciE; move: (ciE) => [cE ioE].
have H F: cardinal F = (cardinal F) *c (cardinal F) <-> (F \Eq (coarse F)).
  rewrite /coarse cprod2cl cprod2cr cprod2_pr1; exact:card_eqP.
have cEE:cardinal E = E by apply: card_card.
have isE:infinite_set E by hnf; rewrite cEE.
set (base := sub_functions E (coarse E)).
pose pr z :=  injection z /\ Imf z = coarse (source z).
have [psi [psibase prpsi ispsi]]:
  exists psi, [/\ inc psi base, pr psi & infinite_set (source psi)].
  have [F [FE cFN]] := (infinite_greater_countable isE).
  have [f [bf sf tf]]: (F \Eq (coarse F)).
    apply/H;rewrite cFN aleph0_pr1; apply/H /EqS/equipotent_N2_N.
  have ff: function f by fct_tac. 
  have pm: (sub (target f) (coarse E)) by rewrite tf; apply: setX_Slr.
  move: (change_target_pr ff pm); set y := (change_target_fun _ _).
  move => [[fy sy ty] yv].
  exists y; rewrite /base sy sf; split => //.
      by apply /sfunctionsP; split => //;  rewrite sy sf.
    split; last first.  rewrite sy sf -tf -(surjective_pr0 (proj2 bf)).
      by rewrite (ImfE ff) (ImfE fy) /y/change_target_fun corresp_g.
    split => // u v; rewrite sy => uf vf. 
    by rewrite yv // yv //; apply: (bij_inj bf).
  by apply/infinite_setP; rewrite cFN; apply: CIS_aleph0.
set (odr := opp_order (extension_order E (coarse E))).
set (ind := Zo base (fun z => pr z /\ sub (graph psi) (graph z))).
have [oe se]:= (extension_osr E (coarse E)).
have [oo soo] := (opp_osr oe). 
have so: sub ind (substrate odr) by rewrite soo se;apply: Zo_S.
have [oi soi] := (iorder_osr oo so).
have ii: inductive (induced_order odr ind). 
  move => X; rewrite (iorder_sr oo so) => Xind. 
  have aux1 := (sub_trans Xind so).
  rewrite (iorder_trans _ Xind)/total_order iorder_sr //; move => [iot tot]. 
  case: (emptyset_dichot X)=> neX.  
    exists psi; split; first by rewrite iorder_sr //; apply: Zo_i =>//; fprops. 
    by rewrite neX; move=> u /in_set0.
  have [rx rxX]:= neX.
  have Hla:forall i, inc i X -> function i.
    by move => i /Xind  /Zo_hi  [[[ok _] _] _].
  have Hlb:forall i, inc i X -> target i = coarse E.
    by move => i /Xind /Zo_S /sfunctionsP [_ _ h].
  have Hlc: forall x y, inc x X -> inc y X -> gle odr x y \/ gle odr y x.
    move=> x y xX yX; case: (tot _ _  xX yX) => h;move: (iorder_gle1 h); fprops.
  set si := Lg X source.
  have Hd: forall i j, inc i (domain si) -> inc j (domain si) -> 
      agrees_on ((Vg si i) \cap (Vg si j)) i j.
    rewrite /si;aw;move=> i j iX jX; rewrite !LgV//.
    split; [ apply: subsetI2l |  by apply: subsetI2r |].
    move=> a /setI2_P [asi asj].
    by case: (Hlc _ _ iX jX)=> h; [ | symmetry ];apply: (extension_order_pr h). 
  have He:forall i, inc i (domain si) -> function_prop i (Vg si i) (coarse E).
    rewrite /si Lgd => i iX; rewrite LgV //; split;fprops.
  move: (extension_covering He Hd).
  set x := common_ext _ _ _; rewrite/si Lgd ;move=> [[fx sx tx] agx _ etc].
  have xb: inc x base.
    apply /sfunctionsP; split => // t; rewrite sx.
    move /setUb_P;aw; move=> [y yX]; move: (Xind _ yX). 
    move => /Zo_S /sfunctionsP [_ pa _ ] ; rewrite LgV//; apply: pa.
  have Hg: forall i, inc i X -> sub (graph i) (graph x). 
    move=> i iX. 
    apply /(sub_functionP (Hla _ iX) fx).
    move: (etc _ iX); rewrite /agrees_on !LgV//;move=> [p1 p2 p3]; split => //.
    move=> a asi; symmetry; exact: p3.
  have sgp:(sub (graph psi) (graph x)).
    apply: sub_trans (proj2 (Zo_hi (Xind _ rxX))) (Hg _ rxX).
  have injx: injection x.
     split=>//; move => u v;rewrite sx.
     move => /setUb_P1  [a aX usa]/setUb_P1 [b bX vsb].
     have [z [zX usz vsz]]:
        (exists z, [/\ inc z X, inc u (source z) & inc v (source z)]).
      by case: (Hlc _ _  aX bX);
         move /igraph_pP /extension_orderP => [_ _ /extends_Ssource h];
          [exists  b | exists a ]; split => //; apply: h.
     move: (etc _ zX); rewrite /agrees_on !LgV//;move => [_ _ aux].
     rewrite (aux _ usz) (aux _ vsz).
     by move: (Zo_hi (Xind _ zX)) => [[[_ iz] _] _]; apply: iz.
  have rgx: Imf x = coarse (source x). 
    set_extens a. 
      move /(Imf_P (proj1 injx)) => [b bsx aW]; move: bsx. 
      rewrite sx; move /setUb_P1=> [c cy bsc].
      move: (etc _ cy); rewrite/agrees_on !LgV//;move => [_ _ aux].
      rewrite (aux _ bsc) in aW.
      move: (Xind _ cy) => /Zo_hi [[ic rc] _].
      have: inc a (coarse (source c)).
        by rewrite -rc aW; Wtac; move: bsc; aw.
      move /setX_P => [pa Ps Qs]; apply /setX_P.
      split => //; apply /setUb_P1; ex_tac.
    move => /setX_P [pa]; rewrite sx. 
    move /setUb_P1 => [b bX psb] /setUb_P1 [c cX qsc].
    have [z [zX usz vsz]]:
        (exists z, [/\ inc z X, inc (P a) (source z) & inc (Q a) (source z)]).
      by case: (Hlc _ _  bX cX);
         move /igraph_pP /extension_orderP => [_ _ /extends_Ssource h];
         [exists  c | exists b ]; split => //; apply: h.
    have :inc a (coarse (source z)) by apply /setX_i.
    move: (Xind _ zX) => /Zo_hi  [[ic rc] _].
    rewrite -rc; move  /(Imf_P (proj1 ic)) => [d dsz ->].
    move: (etc _ zX); rewrite/agrees_on !LgV//;move => [_ _ aux].
    rewrite -(aux _ dsz); apply /(Imf_P fx); exists d => //.
    rewrite sx; apply /setUb_P1; ex_tac.
  have xi: (inc x ind) by apply: Zo_i.
  exists x;split; first by rewrite iorder_sr.
  move=> z zX; move: (Xind _ zX) => zi.
  move: (zi) => /Zo_S zb.
  apply /iorder_gle0P => //; apply /igraph_pP /extension_orderP;split => //.
  move: zb => /sfunctionsP [_ _ tz]; hnf; rewrite tx tz; split; fprops.
move: (Zorn_lemma oi ii) => [x].
rewrite /maximal (iorder_sr oo so); move => [xi aux].
have maxp: forall u, inc u ind -> extends u x -> u = x.
  move=> u ui ue;apply: aux; apply /iorder_gle0P => //.
  move: (Zo_S ui) (Zo_S xi)=> ub xb.
  apply /igraph_pP /extension_orderP;split => //.
clear aux ii.
move: xi => /Zo_P [] /sfunctionsP [fx ssxE txE] [[ijx rgx] sgx].
set (F := source x); set b:= cardinal F. 
have binf:infinite_c b.
  have ss: (sub (source psi) (source x)).
    have fspi: function psi by move: prpsi=> [ip _]; fct_tac.
    move: (domain_S sgx);  rewrite ! domain_fg //.
  move: (sub_smaller ss); rewrite -/F -/b => p1. 
  by apply: (cle_inf_inf _ p1); apply /infinite_setP.
have bsq: (b = b *c b)
  by apply/H; rewrite /F -rgx; apply: Eq_src_range.
case: (equal_or_not b E) => bE; first by rewrite -bE cpowx2 =>//. 
have cb:= proj1 binf.
have bltE: (b <c E) by split ; [rewrite - cEE; exact: (sub_smaller ssxE) |]. 
have b2b : b = b +c b.
  apply:cleA; first by apply: (csum_M0le _ cb).
  rewrite csum_nn cprodC.
  by move: (cprod_Meqle b (infinite_ge2 binf));rewrite - bsq.
have [/cardinal_le_aux1 lbEF _]: (cardinal b <c (cardinal(E -s F))). 
  case: (cleT_el (CS_cardinal (E -s F)) (CS_cardinal b)); last by done.
  move /(csum_Meqle b). 
  by rewrite (card_card cb) (cardinal_setC ssxE) -b2b cEE => /(cltNge bltE).
move:lbEF; move/(eq_subset_cardP b _) => /set_leP [Y syc /card_eqP cY].
set (Z:= F \cup Y). 
set (a1:= coarse F); set (a2 := F \times Y); set (a3 := Y \times Z).
move: (card_card cb) => ccb.
case: (finite_not_infinite _ binf). 
suff: (Y= emptyset).
  move => eq; move: cY; rewrite eq cardinal_set0 ccb => ->; exact finite_0.
have dFY: disjoint F Y.
  by apply: disjoint_pr; move=> u uF uy; move: (syc _ uy) => /setC_P [_].
move: (csum2_pr5 dFY). 
rewrite -/Z -/b - (csum2cl _ Y) - (csum2cr _ Y) - cY ccb - b2b => cZ.
have ca1: cardinal (a2 \cup a3) = b. 
  have di: disjoint a2 a3.
    apply: disjoint_pr; move => t /setX_P [_ af _] /setX_P [_ ay _].
    by move: (syc _ ay) => /setC_P [_].
  rewrite (csum2_pr5 di) - (csum2cr a2) - (csum2cl a2) - 2! cprod2_pr1. 
  rewrite - cprod2cr - cprod2cl -/b -(cprod2cl Y) - cY - (cprod2cr _ Z) cZ ccb.
  by rewrite -bsq -b2b.
have pzz:  (coarse Z  = (coarse F) \cup (a2 \cup a3)).
  set_extens t.
    move /setX_P => [pt]; case /setU2_P => r1.
      by case /setU2_P => r2; [| apply: setU2_2]; apply: setU2_1 ;apply: setX_i.
    move => xx; apply: setU2_2; apply: setU2_2 ;apply: setX_i => //.
  case /setU2_P; first by apply: setX_Sll; apply: subsetU2l.
  case /setU2_P => /setX_P [pa pb pc]; apply /setX_P;split => //;
    try (by apply: setU2_1); (by apply: setU2_2).
have dzz: (disjoint (coarse F) (a2 \cup a3)). 
  hnf in dFY.
  apply: disjoint_pr; move=> u /setX_P [_ pF qF];case /setU2_P.
     move /setX_P => [_ _ qY]; empty_tac1 (Q u).
     move /setX_P => [_ pY _]; empty_tac1 (P u).
have: (Y \Eq (a2 \cup a3)) by apply /card_eqP; rewrite - cY ca1.
move=> [x0 [bx0 sx0 tx0]].
set (g:= triple Z (coarse E) ((graph x) \cup (graph x0))).
have Hga: source g = Z by rewrite /g;aw. 
have Hgb:graph g = ((graph x) \cup (graph  x0)) by rewrite /g;aw.
have fx0: function x0 by fct_tac.
have Hgd: range (graph g) = coarse (source g).
  move: bx0 => [_ sjx0].
  rewrite Hga pzz - tx0 - rgx -(surjective_pr0 sjx0).
  by rewrite (ImfE fx0)  (ImfE fx) - range_setU2 /g;aw.
have Hhf: target g = coarse E by rewrite /g; aw.
have Hge:domain (graph g) = (source g).
  rewrite Hgb Hga domain_setU2 !domain_fg //  sx0 //.
have ze: sub Z E.
  by move=> t /setU2_P []; [apply: ssxE | move /syc => /setC_P []].
have fg: function g. 
  rewrite /g;apply: function_pr.
      apply: fgraph_setU2; fprops; rewrite !domain_fg // sx0; exact dFY.
    rewrite - Hgb Hgd /coarse Hga; apply: setX_Slr =>//.
  by rewrite -Hgb Hge Hga.
rewrite - (ImfE fg) in Hgd.
have ig: injection g.
   have aux1: forall a b c, inc (J a b) (graph x) -> inc (J c b) (graph x0) ->
    False.  
     move=> u v w J1 J2; empty_tac1 v.
     rewrite /F - rgx (ImfE fx); ex_tac.
     rewrite -tx0; apply: (p2graph_target fx0 J2).
  apply: injective_pr_bis =>//; rewrite /related Hgb.
  move=> u v w; case  /setU2_P => h1; case /setU2_P => h2.
    apply: (injective_pr3 ijx h1 h2).
    case: (aux1 _ _ _ h1 h2).
    case: (aux1 _ _ _ h2 h1).
    move: bx0 => [ijx0 _]; apply: (injective_pr3 ijx0 h1 h2).
have sg: sub (graph x) (graph g) by rewrite Hgb;apply: subsetU2l. 
have gi: inc g ind. 
  apply: Zo_i; first by  apply /sfunctionsP; rewrite Hga; split => //.
  split => //; apply: sub_trans sgx sg.
have egx: extends g x by rewrite /extends; split => //; rewrite txE Hhf; fprops.
apply /set0_P; move=> y yY; move: (syc _ yY) => /setC_P [_ yF].
by case: yF; rewrite/F - (maxp _  gi egx) Hga; apply: setU2_2.
Qed.

Lemma csquare_inf a: infinite_c a -> a *c a = a.
Proof. by move=> /equipotent_inf2_inf ai; rewrite - cpowx2. Qed.

Lemma cpow_inf a n: infinite_c a -> natp n ->
  n <> \0c -> a ^c n = a.
Proof.
move => ai; move:n; apply: Nat_induction => // n nN hrec _.
case: (equal_or_not n \0c) => nz.
  by rewrite nz succ_zero (cpowx1 (proj1 ai)).
by rewrite (cpow_succ _ nN) (hrec nz) (csquare_inf ai).
Qed.

Lemma cpow_inf1 a n: infinite_c a -> natp n ->
  (a ^c n) <=c  a.
Proof.
move=> ia nN.
case: (equal_or_not n \0c) => h.
  rewrite h cpowx0; apply: (cle_fin_inf finite_one ia). 
rewrite (cpow_inf ia nN h);apply:cleR; exact: (proj1 ia).
Qed.

Lemma finite_family_product a f: fgraph f ->
  finite_set (domain f) -> infinite_c a ->
  (forall i, inc i (domain f) -> (Vg f i) <=c a) ->
  card_nz_fam f ->
  (exists2 j,  inc j (domain f) & (Vg f j) = a) ->
  cprod f = a.
Proof.
move=> fgf fsd ifa alea alnz [j0 j0d vj0].
set (g:= cst_graph (domain f) a). 
have fgg: fgraph g by rewrite /g /cst_graph; fprops. 
have df: domain f = domain g by rewrite /g/cst_graph Lgd.
have le1:forall x, inc x (domain f) -> (Vg f x) <=c (Vg g x). 
  by move=> t tdf; rewrite /g/cst_graph LgV//; apply: alea.
move: (cprod_increasing  df le1); rewrite [cprod g] cprod_of_same.
set (n:= cardinal (domain f)). 
have nN: natp n by fprops.
have nz: n <> \0c by apply: card_nonempty1; exists j0 =>//.
rewrite - cpowcr (cpow_inf ifa nN nz)=> le0. 
set (j:= singleton j0).
have alc: (forall x, inc x (domain f) -> cardinalp (Vg f x)). 
  by move=> x xdf; move: (alea _ xdf) => [h _].
move: (alc _ j0d); rewrite vj0 => ca.
have sjd: (sub j (domain f)) by  move=> t /set1_P => ->.
move: (cprod_increasing1 alnz sjd). 
by rewrite /j cprod_trivial4 // vj0 (card_card ca) => /(cleA le0).
Qed.

Lemma cprod_inf a b: b <=c a ->
  infinite_c a -> b <> \0c -> a *c b = a.
Proof. 
move=> leba ia nzb.
move:(cprod_Meqle a leba); rewrite  (csquare_inf ia) => h.
exact: (cleA h (cprod_M1le (proj32 leba) nzb)).
Qed.

Lemma cprod_inf6 a b: cardinalp a -> cardinalp b ->
  (infinite_c a \/ infinite_c b) -> a <> \0c -> b <> \0c ->
  a *c b = cmax a b.
Proof.
move => ca cb H anz bnz.
case: (cleT_ee ca cb)=> le1.
  rewrite (cmax_xy le1).
  have ib: infinite_c b by case H => // h; move:(cle_inf_inf h le1).
  by rewrite cprodC (cprod_inf le1 ib anz).
rewrite (cmax_yx le1).
have ib: infinite_c a by case H => // h; move:(cle_inf_inf h le1).
by rewrite (cprod_inf le1 ib bnz).
Qed.

Lemma cprod_inf1 a b: b <=c a ->
  infinite_c a -> a *c b <=c a.
Proof.
move =>leba ia.
case: (equal_or_not b \0c) => h.
  rewrite h cprod0r; apply: (cle_fin_inf finite_0 ia).
rewrite (cprod_inf leba ia h); exact (cleR  (proj1 ia)).
Qed.

Lemma cprod_inf2 a b: finite_c b ->
  infinite_c a -> (a *c b) <=c a.
Proof.
move => fb ia; exact: (cprod_inf1 (cle_fin_inf fb ia) ia).
Qed.

Lemma cprod_inf4 a b c:
   a <=c c -> b <=c c -> infinite_c c -> a *c b <=c c.
Proof.
move=> ac bc ci.
wlog lab: a b ac bc / a <=c b.
   move => H; case: (cleT_ee (proj31 ac) (proj31 bc)) => ab; first by apply: H.
   by rewrite cprodC; apply: H.
case: (Nat_dichot (proj31 bc)) => fc.
  apply: (Nat_le_infinite (NS_prod (NS_le_nat lab fc) fc) ci).
move: (cprod_inf1 lab fc); rewrite cprodC => h; exact:(cleT h bc).
Qed.

Lemma cprod_inf5 a b c:
    a <c c -> b <c c -> infinite_c c -> a *c b <c c.
Proof.
move => l1 l2 ic.
move: (proj31_1 l1) (proj31_1 l2) => ca cb. 
move:(cmax_p1 ca cb) => [da db].
have dc:= (Gmax_S (p:=fun z => z <c c) cardinal_le l1 l2).
case: (finite_or_infinite (proj31_1 dc)) => fd.
  move: (cle_fin_fin fd da) (cle_fin_fin fd db).
  move /NatP => aN /NatP bN.
  by apply: clt_fin_inf => //; apply /NatP; apply: NS_prod.
exact (cle_ltT (cprod_inf4 da db fd) dc).
Qed.

Lemma cprod_inf7 a b: natp a -> a <> \0c -> infinite_c b -> a *c b = b.
Proof.
move => /NatP an anz ib; rewrite cprodC.
exact: (cprod_inf (cle_fin_inf an ib) ib anz).
Qed.

Lemma cprod_eq2lx a b b': natp a -> cardinalp b -> cardinalp b' ->
  a <> \0c -> a *c b = a *c b' -> b = b'. 
Proof.
move=> aN cb cb' naz eql.
wlog: b b' cb cb' eql / b <=c b'.
  move => H; case: (cleT_ee cb cb'); first by apply: H.
  move => bb'; symmetry; apply: H => //.
move => lebb.
case: (finite_or_infinite cb') => fb'.
  move/NatP: fb' => b'N; apply:(cprod_eq2l aN (NS_le_nat lebb b'N) b'N naz eql).
case: (finite_or_infinite cb) => fb.
  move:(cprod_inf7 aN naz fb'); rewrite - eql => ha.
  rewrite - ha in fb'.
  have fb'': finite_c (a *c b) by apply/NatP; fprops.
  case:(finite_not_infinite fb'' fb').
by rewrite -(cprod_inf7 aN naz fb')  -(cprod_inf7 aN naz fb).
Qed.


Lemma CIS_pow x y: infinite_c x -> y <> \0c -> infinite_c (x ^c y).
Proof.
move=> ix ynz; exact: (cle_inf_inf ix (cpow_Mle1 (proj1 ix) ynz)).
Qed.

Lemma CIS_pow2 x y: infinite_c x ->  infinite_c y ->
   infinite_c (x ^c y).
Proof. move=> ix iy; exact: (CIS_pow ix (infinite_nz iy)). Qed.

Lemma CIS_pow3 x y : \2c <=c x -> infinite_c y -> infinite_c (x ^c y).
Proof.
move => sa sb.
have sc:= (cpow_Mleeq y sa card2_nz).
exact:(cle_inf_inf sb (cleT (proj1 (cantor (proj1 sb))) sc)).
Qed.


Lemma notbig_family_sum a f: 
  infinite_c a -> (cardinal (domain f)) <=c a -> 
  (forall i, inc i (domain f) -> (Vg f i) <=c a) ->
  (csum f) <=c a.
Proof. 
move=> ifa leda alea.
set (g:= cst_graph (domain f) a).
have dg : domain f = domain g by rewrite /g Lgd.
have ale: forall x, inc x (domain f) -> (Vg f x) <=c (Vg g x). 
  by move=> x xdf; rewrite /g LgV//; apply: alea. 
move: (cprod_inf1 leda ifa) (csum_increasing dg ale).
rewrite [csum g]csum_of_same  cprod2cr => r1 r2; apply: cleT r2 r1.
Qed.

Lemma notbig_family_sum1 a f:
  infinite_c a -> (cardinal (domain f)) <=c a -> 
  (forall i, inc i (domain f) -> (Vg f i) <=c a) ->
  (exists2 j,  inc j (domain f) & (Vg f j) = a) ->
  csum f = a.
Proof. 
move=> ifa leda alea [j0 j0d vj0].
apply: (cleA (notbig_family_sum ifa leda alea)).
by rewrite -vj0; apply:csum_increasing6  j0d; rewrite vj0; case:ifa.
Qed.

Lemma csum_inf1 a: infinite_c a -> a +c a = a.
Proof. 
move=> ia.
by rewrite csum_nn cprodC (cprod_inf (infinite_ge2 ia) ia card2_nz).
Qed.

Lemma csum_inf a b: b <=c a ->
  infinite_c a -> a +c b = a.
Proof. 
move=> leba ia; move :(leba) => [cb ca _]. 
apply: cleA; last by apply: csum_M0le.
by rewrite - {2} (csum_inf1 ia); apply: csum_Meqle. 
Qed.

Lemma csum_inf6 a b: cardinalp a -> cardinalp b ->
  (infinite_c a \/ infinite_c b) ->  a +c b = cmax a b.
Proof.
wlog: a b / b <=c a.
  move => HH ca cb; case (cleT_ee cb ca)=> le1; first by apply: HH.
  by move => h; rewrite (cmaxC ca cb) csumC; apply:HH => //;apply/or_comm.
move => lba ca cb cm;rewrite (cmax_yx lba); apply:(csum_inf lba).
case:cm => // bi; exact:(cle_inf_inf bi lba).
Qed.


Lemma csum_inf5 a b c:
    a <c c -> b <c c -> infinite_c c -> a +c b <c c.
Proof.
move => l1 l2 ic.
wlog lba: a b l1 l2 / b <=c a.
  move => h; case: (cleT_ee (proj31_1 l2)  (proj31_1 l1)); first  by apply:h.
  by rewrite csumC; apply:h.  
case: (finite_or_infinite (proj31_1 l1)) => ia; last by rewrite (csum_inf lba).
move/NatP: ia => na; move/NatP:(NS_sum na (NS_le_nat lba na)) => fs.
apply: (clt_fin_inf fs ic).
Qed.

Lemma csum_inf2 a b c: cardinalp c -> infinite_c a ->
  b <c a -> a = b +c c -> a = c.
Proof.
move => cc ica lba sv.
case: (cleT_el (proj32_1 lba) cc) => lac.
  by apply:(cleA lac); rewrite sv; apply:csum_Mle0. 
by case: (proj2(csum_inf5 lba lac ica)); rewrite - sv.
Qed.

Lemma csum_Mltlt a b c d : a <c b -> c <c d -> a +c c <c b +c d.
Proof.
move: a b c d.
suff: forall a b c d, b <=c d -> a <c b -> c <c d -> a +c c <c b +c d.
  move => H a b c d le1 le2.
  move: (proj32_1 le1)(proj32_1 le2) => cb cd.
  case: (cleT_ee cb cd) => le3; first by apply: H.
  by rewrite (csumC a) (csumC b); apply: H.
move => a b c d lebd lt1 lt2.
case: (finite_or_infinite (proj32_1 lt2)).
  move /NatP => dN.
  exact: (csum_Mlelt (NS_le_nat lebd dN) (proj1 lt1) lt2).
move => ifd.
rewrite (csumC b) (csum_inf lebd ifd).
exact: (csum_inf5 (clt_leT lt1 lebd) lt2 ifd).
Qed.

Lemma csum2_pr6_inf1 a b X: infinite_c X ->
  cardinal a <=c X -> cardinal b <=c X -> 
  cardinal (a \cup b) <=c X.
Proof.
move => pa pb pc.
move: (csum_Mlele pb pc); rewrite (csum_inf1 pa) csum2cl csum2cr.
move: (csum2_pr6 a b); apply:cleT.
Qed.

Lemma csum2_pr6_inf2 a b X: infinite_c X ->
  cardinal a <c X -> cardinal b <c X -> 
  cardinal (a \cup b) <c X.
Proof.
move => pa pb pc.
move: (csum_Mltlt pb pc); rewrite (csum_inf1 pa) csum2cl csum2cr.
move: (csum2_pr6 a b); apply:cle_ltT.
Qed.

Lemma infinite_compl A B:
   infinite_set B -> cardinal A <c cardinal B ->
   cardinal (B -s A) = cardinal B.
Proof.
move => /infinite_setP p1 p2.
ex_middle nsc.
move: (csum2_pr6_inf2 p1 p2 (conj (sub_smaller (@sub_setC B A)) nsc)).
by rewrite setU2Cr2; move: (sub_smaller (@subsetU2r A B)) => /cleNgt.
Qed.

Lemma card_setC1_inf E x:
  infinite_set E -> cardinal E = cardinal (E -s1 x).
Proof.
move => iE; symmetry;apply:infinite_compl => //.
rewrite cardinal_set1; apply: (clt_fin_inf finite_1).  
by apply/infinite_setP. 
Qed.

Lemma infinite_union2 x y z:
    infinite_c z -> cardinal x <c z -> cardinal y <c z ->
    nonempty (z -s (x \cup y)).
Proof.
move => h1 h2 h3.
move: (csum2_pr6_inf2 h1 h2 h3) => h.
apply /nonemptyP => h4; move: (sub_smaller (empty_setC h4)).
by rewrite (card_card (proj1 h1)) => /(cltNge h).
Qed.

Lemma cdiff_inf a b: infinite_c a -> b <c a -> a -c b = a.
Proof.
move => ica lba.
move: (cdiff_pr (proj1 lba)) => /esym h1.
by rewrite - (csum_inf2 (CS_diff _ _) ica lba h1).
Qed.

Lemma cdiff_Mle_gen a b c:
  cardinalp a -> cardinalp b -> cardinalp c ->
  c <=c (a +c b) -> (c -c b) <=c a.
Proof.
move => ca cb cc h.
case:(cleT_el cc cb); first by move /cdiff_wrong=> ->; apply:cle0x.
move => bc.
case: (finite_or_infinite cc) => fc; last first.
  rewrite (cdiff_inf fc bc).
  case: (cleT_el cc ca) => // lac; case:(cltNge (csum_inf5 lac bc fc) h).
case: (finite_or_infinite ca) => fa.
  move/NatP:fc => cN; move/NatP:fa => aN.
  move: h; rewrite - {1}(cdiff_pr (proj1 bc)).
  rewrite csumC;apply:(csum_le2r (NS_lt_nat bc cN) (NS_diff _ cN) aN).
apply: (cleT(cdiff_ab_le_a b cc) (cle_fin_inf fc fa)).
Qed.

Lemma cdiff_pr1_gen a b: cardinalp a -> cardinalp b ->
  (finite_c b \/ b <c a) -> (a +c b) -c b = a.
Proof.
move => ca cb h.
case: (finite_or_infinite ca).   
   move /NatP => fa; apply: cdiff_pr1 => //; case: h; first by move /NatP.
   move => pa;apply: (NS_lt_nat pa fa).
move => ica.
have ba : b <c a by case: h => //; move => hh; apply: clt_fin_inf.
by rewrite (csum_inf (proj1 ba) ica) cdiff_inf.
Qed.

Lemma cdiff_pr2_gen a b: infinite_c b -> a <=c b -> (a +c b) -c b = \0c.
Proof.
move => icb ab.
by rewrite csumC (csum_inf) // cdiff_nn.
Qed.

Lemma cprod_Meqlt_gen a b b':
  natp a -> b <c b' -> a <> \0c -> (a *c b) <c (a *c b').
Proof.
move => aN lbb anz.
case: (finite_or_infinite (proj32_1 lbb)) => fb'.
  move/NatP: fb' => b'N; exact: (cprod_Meqlt aN b'N lbb anz).
rewrite (cprod_inf7 aN anz fb').
case: (finite_or_infinite (proj31_1 lbb)) => fb.
move/NatP: fb => bN;  move: (NS_prod aN bN) => /NatP fp.
 exact: (clt_fin_inf fp fb').
by rewrite (cprod_inf7 aN anz fb).
Qed.

Lemma cprod_inf3 E F: nonempty E ->  E <=cc F -> infinite_set F ->
   (F \times E) =c  F.
Proof.
move=> /card_nonempty1 neE le1 /infinite_setP infF.
by rewrite - cprod2_pr1 - cprod2cl - cprod2cr; apply:cprod_inf.
Qed.

Lemma Exercise6_5a  E F: 
  (functions E F) <=cc (sub_functions E F).
Proof.
apply: sub_smaller => t /functionsP [pa pb pc].
apply /sfunctionsP;split => //;rewrite pb; fprops.
Qed.



Lemma Exercise6_5b E F:
  (sub_functions E F) <=cc  (\Po (product E F)).
Proof.
move: (card_bijection (graph_of_function_fb E F)).
by rewrite /graph_of_function; aw => ->; apply: sub_smaller; apply: Zo_S.
Qed.


Lemma Exercise6_5c E: infinite_set E ->
  (permutations E) <=cc (\Po E).
Proof.
move=> isE.
set C:= (functions E E).
have pb: sub (Zo C bijection) C by apply: Zo_S.
apply: (cleT (sub_smaller pb)).
apply: (cleT (Exercise6_5a E E)).
case: (emptyset_dichot E) => neE.
  move: isE; rewrite neE => /infinite_setP; rewrite cardinal_set0.
  by move/(finite_not_infinite finite_0).
have cle2: (cardinal E) <=c (cardinal E) by fprops.
move: (Exercise6_5b E E) (cprod_inf3 neE cle2 isE) => ca  cb.
have -> : (cardinal (\Po E) = cardinal (\Po (product E E))) => //.
by rewrite !card_setP - (cpowcr _ (E\times E)) cb cpowcr.
Qed.


(** ** EIII-6-4 Countable sets *)
Definition countable_set E:= E <=s Nat.
Definition countable_infinite E := countable_set E /\ infinite_set E.

Lemma countableP E:
  countable_set E  <-> (cardinal E) <=c aleph0.
Proof. 
apply: (iff_trans (eq_subset_cardP E Nat)).
rewrite aleph0_pr1; apply:cardinal_le_aux2P; fprops.
Qed.

Lemma infinite_countableP E:
  countable_infinite E  <-> (cardinal E) = aleph0.
Proof. 
split. 
  move => [/countableP sa /infinite_greater_countable1 sb]; apply:(cleA sa sb).
move => ce; split; first by apply/countableP; rewrite - ce; fprops.
apply/infinite_setP; rewrite ce; exact:CIS_aleph0.
Qed.


Lemma finite_is_countable X: finite_set X -> countable_set X.
Proof.
move => /card_finite_setP /NatP h; apply/countableP.
apply(cle_fin_inf h CIS_aleph0).
Qed.

Lemma aleph0_countable E: cardinal E = aleph0 -> countable_set E.
Proof. by move/infinite_countableP => []. Qed.


Lemma countable_infinite_Nat: countable_infinite  Nat.
Proof. by apply /infinite_countableP; rewrite aleph0_pr1. Qed.

Lemma countable_Nat : countable_set Nat.
Proof. exact (proj1 countable_infinite_Nat). Qed.

Lemma countable_finite_or_N E: countable_set E ->
  finite_c (cardinal E) \/ cardinal E = aleph0.
Proof. 
move /countableP => leB.
case: (equal_or_not (cardinal E) aleph0) => ne; [by right | left].
apply/NatP; exact:(olt_i(oclt (conj leB ne))).
Qed.

Theorem countable_sub E F: sub E F -> countable_set F  ->
  countable_set E.
Proof. 
move=> /sub_smaller h1 /countableP h; apply /countableP; exact:cleT h1 h.
Qed.

Lemma countable_sub_Nat x : sub x Nat -> countable_set x.
Proof. move => h; apply: (countable_sub h countable_Nat).  Qed.

Lemma countable_fun_image z f:
  countable_set z -> countable_set (fun_image z f).
Proof.
move /countableP => h; apply /countableP.
exact:(cleT (fun_image_smaller z f) h).
Qed.

Theorem countable_product f:
  finite_set (domain f) -> 
  (allf f countable_set) -> 
  countable_set (productb f).
Proof. 
move=> /NatP fsd alc; apply /countableP.
rewrite [X in X <=c _ ]cprod_pr.
apply: (@cleT  (cprodb (domain f) (fun i =>aleph0))).
  apply: cprod_increasing; aw; trivial => x xdf. 
  by rewrite !LgV//; move: (alc _ xdf) => /countableP.
rewrite cprod_of_same - cpowcr.
exact:(cpow_inf1 CIS_aleph0 fsd). 
Qed.


Theorem countable_union f:
  countable_set (domain f) -> 
  (allf f countable_set) ->
  countable_set (unionb f).
Proof. 
move=> cs alc; apply /countableP.  
set d:= domain f.
apply: (@cleT (csumb d (fun i => cardinal (Vg f i)))). 
  apply: csum_pr1 =>//.
set (h:=  cst_graph d aleph0).
apply: (@cleT (csumb d (fun i => aleph0))).
  rewrite/h;apply: csum_increasing; aww.
  move=> x xd;rewrite !LgV//; move: (alc _ xd) => /countableP //.
rewrite csum_of_same - cprod2cr. 
by apply: cprod_inf1 CIS_aleph0; apply/countableP.
Qed.
  
Lemma countable_setU2 a b: 
   countable_set a -> countable_set b -> countable_set (a \cup b).
Proof.
move => /countableP ca /countableP cb; apply/countableP.
move: (csum_Mlele ca cb); rewrite (csum_inf1 CIS_aleph0).
by apply: cleT; move: (csum2_pr6 a b); rewrite - csum2cl - csum2cr. 
Qed.

Lemma countable_setX2 a b: 
  countable_set a -> countable_set b -> countable_set (a \times b).
Proof.
move => /countableP ca /countableP cb; apply/countableP.
rewrite - (cprod2_pr1 a b)- cprod2cl - cprod2cr. 
exact: (cprod_inf4 ca cb CIS_aleph0).
Qed.

Theorem infinite_partition E: infinite_set E ->
  exists f, [/\ partition_w_fam f E, (domain f) \Eq E &
    (forall i, inc i (domain f) -> (countable_infinite (Vg f i)))]. 
Proof. 
move=> iE; move: (infinite_greater_countable1 iE) => h1.
have iE': infinite_c (cardinal E) by apply /infinite_setP.
move: (cprod_inf h1 iE' aleph0_nz).
rewrite cprod2_pr1; move /card_eqP=> [f [bf sf tf]].
move: (bf) => [injf sjf].
pose G a := (indexedr a aleph0).
set (g:= Lg (cardinal E) (fun a => Vfs f (G a))).
have ff: function f by fct_tac.
have ppa: forall i, inc i (cardinal E) -> sub (G i) (source f).
  by move => i ie;rewrite sf; apply: setX_Sl; apply/sub1setP.
exists g; rewrite /g; aw; split => //; [ | by apply/card_eqP; aw | ]. 
  split => //; fprops.
    apply: mutually_disjoint_prop;aw; move=> i j y inE jnE;rewrite !LgV//.
    move: (ppa _ inE)(ppa _ jnE) => pa pb.
    move /(Vf_image_P ff pa) => [u u1 u2] /(Vf_image_P ff pb)  [v v1 v2].
    rewrite u2 in  v2; move: (proj2 injf _ _ (pa _ u1) (pb _ v1) v2).
    by move: u1 v1 => /setX_P [_ /set1_P <-] _ /setX_P [_ /set1_P <-] _ ->.
   set_extens t.
     move=> /setUb_P1 [y ycE]; move/(Vf_image_P ff (ppa _ ycE)).
     by move => [u u1 ->]; rewrite -tf; Wtac; apply: (ppa _ ycE).
  move => tE.
  have tt: inc t (target f) by rewrite tf.
  move: (proj2 sjf _ tt);move=> [x xsf jG].
  move: xsf; rewrite sf; move /setX_P => [pax px qx].
  apply /setUb_P1;ex_tac; apply /(Vf_image_P ff (ppa _ px)).
  exists x => //; apply /setX_P; split;fprops.
move => i inE; rewrite LgV//.
have sd: (sub (G i) (source f)) by apply: ppa.
apply /infinite_countableP. 
by rewrite (cardinal_image sd injf) cardinal_indexedr (card_card (CS_aleph0)).
Qed.

Lemma countable_inv_image f: surjection f ->
  (forall y, inc y (target f) ->   countable_set (Vfi1 f y)) ->
  infinite_set (target f) ->
  (source f) =c (target f).
Proof. 
move => sf alc it.
apply: cleA; last by apply: surjective_cle; exists f.
have ff: function f by fct_tac.
set (pa := Lg (target f) (fun  z=> (Vfi1 f z))).
have ->: source f = unionb pa.
  set_extens t;last by move /setUb_P1 => [y ytf] /(iim_fun_set1_P _ ff) [].
  move => tsf; apply /setUb_P1; exists (Vf f t)=> //; first by  Wtac.
  apply (iim_fun_set1_P _ ff);split => //.
have ->: cardinal(unionb pa) = csum pa.
  apply: Eqc_disjointU => //.
  - rewrite /pa /disjointU_fam; split => //;fprops.
  - rewrite/disjointU_fam /pa !Lgd//.
  - by rewrite /disjointU_fam /pa Lgd; move=> i idf; rewrite !LgV//; aw.
  - rewrite /pa;apply: mutually_disjoint_prop; aw. 
    move=> i j y itf jtf; rewrite !LgV//. move /(iim_fun_set1_P _ ff) => [_ ->].
    by move /(iim_fun_set1_P _ ff) => [_ <-].
  - fprops.
    have ->: cardinal (target f) = aleph0 *c domain pa.
  rewrite /pa Lgd - cprod2cr cprodC cprod_inf //.
  + by apply: infinite_greater_countable1.
  + by apply/infinite_setP. 
  + exact: aleph0_nz.
rewrite - csum_of_same (csum_pr pa) /pa; apply: csum_increasing;aw; trivial.
move => x xa; rewrite !LgV//; apply /countableP; apply: alc =>//.
Qed.

  

Theorem infinite_finite_subsets E: infinite_set E ->
  (Zo (\Po E) finite_set) =c E.
Proof. 
move=> inE.
have icE: infinite_c (cardinal E) by split; [apply: CS_cardinal | exact].
set bF:=Zo _ _ .
pose T n :=  Zo (\Po E) (fun z  => cardinal z = n).
have le1: (forall n, natp n -> (cardinal (T n)) <=c (cardinal E)).
  move=> n nN; rewrite /T. 
  have cn:= card_nat nN.
  set (K:= injections n E).
  have ta: lf_axiom  (fun z => Imf z) K (T n).
    move=> z /Zo_P [] /functionsP [fz sz tz] inz; apply: Zo_i.
       apply /setP_P;rewrite -tz => //; apply: Imf_Starget => //.
    by rewrite (cardinal_range inz) sz cn.
  set (f:= Lf (fun z => Imf z) K (T n)).
  have ff: function f by apply: lf_function.
  set (q:= permutations n).
  set (c := cardinal q). 
  have fc: (finite_c c).
    apply/NatP; rewrite /c /q (card_permutations) /finite_set cn; fprops.
    by apply: NS_factorial.
  have cii: (forall x, inc x (target f) -> cardinal (Vfi1 f x) = c). 
    move=> x ;rewrite/f; aw; move => /Zo_P [] /setP_P xE cx.
    have /card_eqP [x0 [bx0 sx0 tx0]]:  n =c x by rewrite - cx; aw.
    set x1 := triple n E (graph x0).
    have sx1: (source x1 = n) by rewrite /x1; aw.
    have tx1: (target x1 = E) by rewrite /x1; aw.
    have fx1: function x1.
      have fx0 := (proj1 (proj1 bx0)).
      have ha := (function_fgraph fx0).
      have hb:sub (range (graph x0))  E. 
        apply: (sub_trans (f_range_graph fx0)); ue.
      by apply: (function_pr ha hb); rewrite domain_fg.
    have ix1:  injection x1.
      apply:injective_pr_bis => //.
      rewrite /x1;aw;move=> u v w p1 p2.
      apply: (injective_pr (proj1 bx0) p1 p2).
    set iif := Vfi1 _ _.
    set (g:= Lf (fun z=>  (x1 \co z)) q iif).
    have ta2:  (lf_axiom (fun z=> (x1 \co z)) q iif). 
      rewrite/q/iif => z zq; apply /iim_fun_set1_P => //.
      move: zq => /Zo_P [] /functionsP [fz sz tz] bz.
      have cxz: (x1 \coP z) by split => //; ue.
      set (t:= x1 \co z).  
      have fr: (function t) by rewrite /t; fct_tac.
      have tk: (inc t K).  
        apply: Zo_i; first by apply /functionsP;split => //; rewrite /t; aw.
        apply: inj_compose1 =>//; [ move: bz => [iz _] => // | ue].
      split; first by aw.
      have gz: sgraph (graph z) by fprops.
      suff: (x = Vf f t) by move => ->; rewrite /f; aw.
      rewrite /f LfV  // (ImfE fr) /t /compose; aw.
      rewrite (compg_range _ gz) - (ImfE fz)  (surjective_pr0 (proj2 bz)).
      by rewrite - tx0 - (surjective_pr0 (proj2 bx0)) tz - sx0 /x1; aw.
    have fg: function g by  rewrite /g; apply: lf_function =>//.
    symmetry;apply /card_eqP; exists g; split => //; rewrite /g; aw; trivial.
    apply: lf_bijective => //.  
        move=> u v /Zo_P [] /functionsP [fu su tu] bu
          /Zo_P [] /functionsP [fv sv tv] bv sc.
        apply: function_exten; try fct_tac; try ue.
        move=> w wsu.
        have : (Vf (x1 \co u) w = Vf (x1 \co v) w) by ue.
        have c1: x1 \coP v by  split => //; try fct_tac; try ue.
        have c2: x1 \coP u by  split => //; try fct_tac; try ue.
        have wsv :inc w (source v) by rewrite sv - su.
        rewrite !compfV //; apply: (proj2 ix1). 
          rewrite sx1 -tu; Wtac;fct_tac. 
          rewrite sx1 -tv; Wtac;fct_tac.
     move => y /(iim_fun_set1_P _ ff) [].
     rewrite /f lf_source => pa; rewrite LfV// => rgy.
     move: pa; rewrite /f; aw; move => /Zo_P [y1 iy].
     have w2: Imf y = Imf x0 by rewrite (surjective_pr0 (proj2 bx0)) tx0.
     have w3: Imf x0 = Imf x1.
       by rewrite  (ImfE fx1) (ImfE (proj1 (proj1 bx0))) /x1;aw.
     have ww: sub (Imf y) (Imf x1) by rewrite w2 w3.
     move: y1 => /functionsP [fy sy ty].
     rewrite -tx1 in ty; move: ww;rewrite -(exists_right_composable fy ix1 ty). 
     move => [h [cph ch]]; exists h => //. 
     have sh: (source h = n) by rewrite - sy - ch; aw. 
     have th: (target h = n) by move: cph => [_ _ hq]; rewrite -hq.
     have ih: injection h. 
       split;first by fct_tac. 
       move => v w vsh wsh sw.
       have: Vf y v = Vf y w by rewrite - ch !compfV //  sw.
       apply: (proj2 iy); [rewrite sy - sh // |rewrite sy - sh //].
    have bh: bijection h.
      apply: bijective_if_same_finite_c_inj; rewrite ? th ? sh //.
        by rewrite /finite_set cn; fprops.
    apply: Zo_i => //; apply /functionsP;split => //; fct_tac.
  move: (shepherd_principle ff cii).
  rewrite /f; aw; move => cK.
  case: (equal_or_not n \0c) => nz. 
    have te: (T \0c = singleton emptyset).
      apply: set1_pr.
        apply: Zo_i; [apply:setP_0i | apply:cardinal_set0].
      move => z /Zo_P  [_ aux]; rewrite (card_nonempty aux) //.
    rewrite nz -/(T _) te cardinal_set1.  
    apply: cle_fin_inf; [ fprops | exact].
  case: (finite_or_infinite (CS_cardinal (T n))) => finT.
    apply: cle_fin_inf =>//.
  set (K1:= cardinal (functions n E)). 
  have k1E: (K1 = cardinal E).
    by rewrite /K1 -/(E ^c n) - cpowcl; apply:  cpow_inf.
  have: (cardinal K <=c cardinal E).
     rewrite -k1E; apply: sub_smaller;apply: Zo_S.
  apply: cleT; rewrite cK.
  have i2: (c <=c (cardinal (T n))) by  apply: cle_fin_inf. 
  have i3: (c <> \0c). 
    rewrite /c/q.
    have fsn: finite_set n by rewrite /finite_set cn; fprops.
    rewrite (card_permutations fsn) cn; apply: (factorial_nz nN).
  rewrite (cprod_inf i2 finT i3); fprops.
set Fn := Lg Nat T.
apply: cleA; last first.
  apply /eq_subset_cardP1.
  exists (Lf (fun x => singleton x) E bF); saw.
  apply: lf_injective. 
    move=> x xe /=;  rewrite/bF; apply: Zo_i; last by apply: set1_finite.
    by apply /setP_P; apply /sub1setP.
  move=> u v _ _;apply: set1_inj. 
have <-: csumb (domain Fn) (fun i => (cardinal E)) = cardinal E.
  rewrite /Fn csum_of_same Lgd.
  exact: cprod_inf (infinite_greater_countable1 inE) icE aleph0_nz.
have ->: (bF = unionb Fn). 
  set_extens t.
    move /Zo_P => [pa pb]; apply /setUb_P1;  exists (cardinal t).
       rewrite -/(natp _); fprops.
    apply /Zo_i => //. 
  move /setUb_P1 => [y yb] /Zo_P [pa pb]; apply /Zo_P;split => //.
  by apply /NatP; rewrite pb.
have ->: (unionb Fn) =c  (unionb (disjointU_fam Fn)).
  apply: Eqc_disjointU; rewrite/Fn/disjointU_fam.  
  + split => //; aww=> i iN; rewrite !LgV//; aw; trivial; apply: Eqc_indexed2.
  + apply: mutually_disjoint_prop; rewrite /Fn Lgd.
    by move=> i j y iN jN; rewrite !LgV//;aw; move => /Zo_hi <- /Zo_hi <-.
  + apply: mutually_disjoint_prop3. 
rewrite -/(csum Fn) (csum_pr Fn).
apply: csum_increasing; fprops;rewrite /Fn !Lgd //; move=> x xd.
rewrite !LgV //; apply: le1 =>//. 
Qed.

Lemma infinite_finite_sequence E: infinite_set E ->
 (Zo (sub_functions Nat E) (fun z=> finite_set (source z))) =c E.
Proof.
move=> iE.
have iE': infinite_c (cardinal E) by  apply /infinite_setP.
set q:= Zo _ _.
apply: cleA.
  move: (infinite_finite_subsets infinite_Nat).
  set Fn:=Zo _ _ =>  fse.
  have qu:q = unionb (Lg Fn (fun z=> (functions z E))).
    set_extens t.
      move => /Zo_P [] /sfunctionsP [ft sst tt] fst.
      apply /setUb_P1;exists (source t) => //. 
         apply: Zo_i =>//; by apply /setP_P.
      apply /functionsP;split => //.
    move => /setUb_P1 [y] /Zo_P [] /setP_P pa pb /functionsP [ft st tt].
    apply: Zo_i; [ apply /sfunctionsP;split => //; ue | rewrite st; fprops ].
  have ze: (forall z, inc z Fn -> 
    (cardinal (functions z E)) <=c (cardinal E)).
    move=> z zFn ; rewrite -/(E ^c z) - cpowcl - cpowcr.
    apply: cpow_inf1 =>//; move: zFn => /Zo_P [_ pa]; fprops. 
  move: (csum_pr1 (Lg Fn (functions^~ E))). 
  rewrite -qu; rewrite Lgd /csumb.
  set (g:= (Lg Fn (fun _:Set  => cardinal E))).
  set f0:= (Lg Fn _ ).
  have fg1: (fgraph f0) by rewrite /f0; fprops. 
  have fg2: (fgraph g) by rewrite /g; fprops.  
  have df0g: domain f0 = domain g by  rewrite /f0  /g !Lgd.
  have ale: (forall x, inc x (domain f0) -> (Vg f0 x) <=c (Vg g x)).
    by rewrite /f0/g Lgd; move=> x xdf; rewrite !LgV//; apply: ze.
  move: (csum_increasing  df0g ale); rewrite [csum g]csum_of_same => le1 le2.
  move: (infinite_greater_countable1 iE) => le3.
  move: (cprod_inf1 le3 iE'). rewrite aleph0_pr1 - fse cprod2cr.
  exact: cleT (cleT le2 le1).
apply /eq_subset_cardP1.
have aux: forall v, inc v E ->
   lf_axiom (fun _  => v) (singleton \0c) E by move=> vE t //=.  
exists (Lf (fun z  => (Lf ((fun _:Set => z))(singleton \0c) E)) E q).
saw; apply: lf_injective.
  move=> z  zE; apply: Zo_i.
    apply /sfunctionsP;saw.
       apply: lf_function =>//.  
    apply: set1_sub; apply: NS0.
   aw; apply: set1_finite.
have zs:= set1_1 \0c.
by move=> u v uE vE /(f_equal (Vf ^~ \0c)); rewrite !LfV //; apply: aux.
Qed.

(** Aleph zero *)

Lemma aleph0_pr2:  aleph0 +c aleph0 = aleph0.
Proof.  by apply: (csum_inf1 CIS_aleph0). Qed.

Lemma aleph0_pr3:  aleph0 *c aleph0 = aleph0.
Proof. by apply: (csquare_inf CIS_aleph0). Qed.

Lemma aleph0_plus1: aleph0 +c \1c = aleph0.
Proof. 
symmetry.
move:CIS_aleph0 => ai; rewrite -(csucc_pr4 (proj1 ai));apply/csucc_inf;fprops.
Qed.

(** ** EIII-6-5 Stationary sequences *)

Definition stationary_sequence f :=
  [/\ fgraph f, domain f = Nat &
  exists2 m, natp m & forall n, natp n -> m <=c n ->
    Vg f n = Vg f m].

Definition increasing_sequence f r:=
  [/\ fgraph f, domain f = Nat, sub (range f) (substrate r) &
  forall n m, natp n -> natp m -> n <=c m ->
    gle r (Vg f n) (Vg f m)].

Definition decreasing_sequence f r:=
  [/\ fgraph f, domain f = Nat, sub (range f) (substrate r) &
  forall n m, natp n -> natp m -> n <=c m ->
    gle r  (Vg f m) (Vg f n)].

Lemma increasing_seq_prop f r: order r ->
  function f -> source f = Nat -> sub (target f) (substrate r) ->
  (forall n, natp n -> gle r (Vf f n) (Vf f (csucc n))) ->
  increasing_sequence (graph f) r.
Proof. 
move => or ff sf tf ale.
split;fprops; rewrite ? domain_fg //.
   apply: (@sub_trans (target f)) => //;  apply: f_range_graph=>//.
move=> n m nN mN /cdiff_pr <-.
rewrite -/(Vf _ _ ) -/(Vf _ _).
move: (m -c n) (NS_diff n mN); apply: Nat_induction.
  by rewrite (Nsum0r nN); order_tac; apply: tf; Wtac;rewrite sf.
move=> p pN le1.
rewrite (csum_nS _ pN); move: (ale _ (NS_sum nN pN))=> le2; order_tac.
Qed.

Lemma decreasing_seq_prop f r: order r ->
  function f -> source f = Nat -> sub (target f) (substrate r) ->
  (forall n, natp n -> gle r (Vf f (csucc n))  (Vf f n)) ->
  decreasing_sequence (graph f) r.
Proof. 
move => or ff sf tf ale.
split;fprops; rewrite ?domain_fg //.
   apply: (@sub_trans (target f)) => //;  apply: f_range_graph=>//.
move=> n m nN mN nm;rewrite- (cdiff_pr nm).  
rewrite -/(Vf _ _ ) -/(Vf _ _).
move: (m -c n)  (NS_diff n mN);apply: Nat_induction. 
  by rewrite (Nsum0r nN);order_tac; apply: tf; Wtac;rewrite sf.
move=> p pN le1.
rewrite (csum_nS _ pN).
move: (ale _ (NS_sum nN pN)) => le2; order_tac.
Qed.

Theorem  increasing_stationaryP r: order r ->
  ((forall X, sub X (substrate r) -> nonempty X ->
     exists a,  maximal (induced_order r X) a) <->
  (forall f, increasing_sequence f r -> stationary_sequence f)).
Proof. 
move=> or;split.
  move=> hyp f [fgf df rf incf]; rewrite /stationary_sequence;split => //. 
  have ner: (nonempty (range f)).
    exists (Vg f \0c); apply: (inc_V_range fgf); rewrite df; apply:NS0.
  move: (hyp _ rf ner) => [a];rewrite /maximal iorder_sr //.
  move => [ha]; move: (ha) => /(range_gP fgf) [x pa eq] alv; rewrite df in pa.
  exists x => // n nN xn.
  move: (incf _ _ pa nN xn); rewrite -eq => h; apply: alv. 
  apply / iorder_gle0P => //; apply /(range_gP fgf); exists n=> //; ue.
move=> h X Xsr neX.
pose T x := Zo X (fun y => glt r x y). 
case: (emptyset_dichot (productb (Lg X T))) => pe.
  have [x xX Tx]: (exists2 x, inc x X & T x = emptyset). 
    ex_middle eh.
    have p1: (fgraph (Lg X T)) by fprops.
    have p2: (forall i, inc i (domain (Lg X T)) -> nonempty (Vg (Lg X T) i)).
      aw;move=> i iX; rewrite LgV// ;case: (emptyset_dichot (T i))=> //ie. 
      case: eh; ex_tac. 
    by move: (setXb_ne p2); rewrite pe; move /nonemptyP.
  exists x;split => //; first by rewrite iorder_sr //.
  move => t xt; move:(iorder_gle1 xt) => xt1.
  move: (iorder_gle3 xt) => [_ tX].
  ex_middle w; empty_tac1 t; apply: Zo_i =>//; split;fprops.
move:pe=> [y yp].  
have p1:  (forall x, inc x X -> glt r x (Vg y x)). 
  have aux: fgraph (Lg X T) by fprops.
  move: yp => /setXb_P;aw; move => [pa pb pc] x xX.
  by move: (pc _ xX); rewrite LgV // =>/Zo_P [].
have p2: (forall x, inc x X -> inc (Vg y x) X).
  have aux: fgraph (Lg X T) by fprops.
  move: yp => /setXb_P; aw; move => [pa pb pc] x xX.
  by move: (pc _ xX); rewrite LgV // =>/Zo_P [].
move:neX => [y0 y0X].
move: (integer_induction_stable y0X p2).
move:(induction_defined_pr (Vg y) y0); simpl.
set f:= induction_defined _ _.
move=> [sf [ff _] f0 fn] tfX.
have p3: (forall n, natp n -> glt r (Vf f n) (Vf f (csucc n))).
  move=> n nN; rewrite fn //; apply: p1; apply: tfX; Wtac; ue.
have p4: (forall n, natp n -> gle r (Vf f n) (Vf f (csucc n))).
  by move=> n nN; move: (p3 _ nN)=> [ok _].  
have s2: sub (target f) (substrate r) by apply: (sub_trans tfX).
move:(h _ (increasing_seq_prop or ff sf s2 p4)) => [_ _ [m mN sm]].
have sN: natp (csucc m) by fprops.
move: (sm _ sN (cleS mN)); move: (p3 _ mN); rewrite /Vf.
by move=> /proj2 h1 h2; move: h1; rewrite h2.
Qed.

Theorem  decreasing_stationaryP r: total_order r ->
  ((worder r) <->
  (forall f, decreasing_sequence f r -> stationary_sequence f)).
Proof. 
move=> tor; split  => hyp. 
  move=> f [fgf df rf incf]; rewrite /stationary_sequence;split => //.
  have ner: (nonempty (range f)). 
    exists (Vg f \0c); apply: (inc_V_range fgf);rewrite df; apply: NS0.
  move: hyp=> [or wor]; move: (wor _ rf ner) => [y []]; rewrite iorder_sr//.
  move /(range_gP fgf) => [x xdf xv] hb.
  rewrite df in xdf.
  exists x => // n nN xn.
  move: (incf _ _ xdf nN xn) => pa.
  have hh: inc (Vg f n) (range f) 
     by apply /(range_gP fgf); exists n => //; ue.
  move: (iorder_gle1 (hb _ hh)); rewrite xv => leq1; order_tac.
set (r':= opp_order r). 
have or: order r by move: tor => [or _].
move: (opp_osr or) => [or' sr'].
split =>// x xsr nex.
have la:= (total_order_lattice (total_order_sub tor xsr)).
have srsr': (substrate r = substrate r') by rewrite sr'.
have aux: (forall f, increasing_sequence f r' -> stationary_sequence f).
  move=> f fi; apply: hyp; move : fi => [p1 p2 p3 p4]; split => //; try ue.
  move=> n m nN mN nm; move: (p4 _ _ nN mN nm); rewrite /r'.
  by move  /igraph_pP.
move: (iorder_osr or xsr) => [oi soi].
move: aux; move /(increasing_stationaryP or'); rewrite - srsr' => aux.
move: (aux _ xsr nex) => [a]; rewrite /r' (iorder_opposite x or). 
move/(maximal_opp oi) => mi.
exists a; apply: (left_directed_minimal (proj2 (lattice_directed la)) mi).
Qed.


Definition decreasing_strict_sequence f r :=
 [/\ fgraph f, domain f = Nat, sub (range f) (substrate r)
   & forall n m, natp n -> natp m -> n <c m -> glt r (Vg f m) (Vg f n)].

Lemma total_order_worder_dichot r: total_order r ->
   (worder r \/ exists f, decreasing_strict_sequence f r).
Proof.
move => tor.
move:(decreasing_stationaryP tor) => H.
case: (p_or_not_p (worder r)) => ha; [by left | right].
ex_middle hb; case: ha; apply/H => f [qa qb qc qd]; split => //.
ex_middle hc; case hb.
pose Z n := Zo Nat (fun m => n <c m /\ glt r (Vg f m) (Vg f n)).
have sif: forall n, natp n -> nonempty (Z n).
   move => n nN; apply /nonemptyP => ze; case hc; exists n => // m mN lemn.
   move: (qd _ _ nN mN lemn) => ha; ex_middle he; empty_tac1 m.
   by apply Zo_i => //; split => //; split => // hf; case he; rewrite hf.
pose F n := intersection (Z n). 
have Fp: forall n, natp n -> 
  [/\ natp (F n),  n <c (F n) & glt r (Vg f (F n)) (Vg f n)].
   move => n nN. 
   have sN: sub (Z n) Nat by apply:Zo_S.
   by move: (proj1 (inf_Nat sN (sif _ nN))) => /Zo_P [hu [hv hw]].
move: (induction_defined_pr F \0c) =>[].
set g := (induction_defined F \0c). 
move => sg sjg g0 gs.
have gN: forall n, natp n -> natp (Vf g n).
  apply: Nat_induction; first by rewrite g0; apply:NS0.
  by move => n nN hr; rewrite (gs _ nN); exact: (proj31 (Fp _ hr)). 
pose h n := Vg f (Vf g n).
have hr: forall n, natp n -> glt r (h (csucc n))  (h n) .
   move => n nN; rewrite /h (gs _ nN); exact:(proj33 (Fp _ (gN _ nN))).
have fgh: fgraph (Lg Nat h) by fprops.
exists (Lg Nat h); saw.
  move => t /(range_gP fgh); aw; move => [z zN ->]; rewrite LgV//.
  move : (proj1 (hr _ zN)) => le1; order_tac.
move => n m nN mN nm.
rewrite - (cdiff_pr (proj1 nm)).
move:(NS_diff n mN) (cdiff_nz nm).
move:(m -c n); clear mN nm m; apply: Nat_induction => //.
  move => m mN Ha _.
  have sN:= NS_sum nN mN.
  have sN1:= (NS_succ sN).
  rewrite (csum_nS _ mN) /h !LgV//  (gs _ sN).
  case: (equal_or_not m \0c).
     move => ->; rewrite (csum0r (CS_nat nN)).
     exact: (proj33 (Fp _ (gN _ nN))).
    move /Ha; move:(proj33 (Fp _ (gN _ sN))); rewrite /h !LgV //.
   move => pa pb; exact: (lt_lt_trans (proj1 tor) pa pb).
Qed.

Theorem  finite_increasing_stationary r: order r -> 
  finite_set (substrate r) ->
  (forall f, increasing_sequence f r -> stationary_sequence f).
Proof. 
move=> or fs; apply /(increasing_stationaryP or). 
move=> X Xsr neX; move: (iorder_osr or Xsr) => [pa pb].
apply: finite_set_maximal => //; rewrite pb => //.
apply: (sub_finite_set Xsr fs).
Qed.

Theorem noetherian_induction r F:  order r ->
  (forall X, sub X (substrate r) -> nonempty X ->
    exists a,  maximal (induced_order r X) a) ->
  sub F (substrate r) ->
  (forall a, inc a (substrate r) -> (forall x, glt r a x -> inc x F)
    -> inc  a F) 
  -> F = substrate r.
Proof.
move=> or p1 p2 p3.
set (c := (substrate r) -s F).
case: (emptyset_dichot c) => ce.
  apply: extensionality => //; move=> x xsr; ex_middle xsf.
  empty_tac1 x; apply /setC_P;split => //.
have cs: sub c (substrate r) by rewrite /c; apply: sub_setC.
move: (p1 _ cs ce) => [a]; rewrite / maximal iorder_sr//; move => [ac am].
have aux: (forall y, glt r a y -> inc y F). 
  move=> y xy;  ex_middle w.
  have yc: (inc y c) by apply /setC_P;split => //; order_tac.
  move: xy => [xy nxy]; case: nxy.
  have ham: gle (induced_order r c) a y by  apply /iorder_gleP.
  by rewrite  (am _ ham).  
by move: (p3 _ (cs _ ac) aux); move: ac => /setC_P [].
Qed.


End InfiniteSets.
Export  InfiniteSets.

