(** * The set Q of rational numbers part 2
  Copyright INRIA (2013-2014 2018) Marelle Team (Jose Grimm).
*)
(* $Id: ssetq2.v,v 1.4 2018/09/04 07:58:00 grimm Exp $ *)


Set Warnings "-notation-overridden".
From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat. 
Set Warnings "notation-overridden".

Require Export sset10 ssetq1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 


Module RationalNumbers2.


(** ** The eta ordering of Cantor *)

(* Definition of eta like *)

Definition eta_like0 r  (E:=substrate r) :=
  [/\ total_order r, countable_set E,
     (forall x, inc x E ->  exists y, glt r y x),
     (forall x, inc x E ->  exists y, glt r x y) &
     (forall x y, glt r x y -> exists z, glt r x z /\ glt r z y)].
Definition eta_like r := eta_like0 r  /\ cardinal (substrate r) = aleph0.


Lemma eta_like_pr1 r: eta_like0 r -> 
    substrate r = emptyset \/ cardinal (substrate r) = aleph0.
Proof.
move => [ha hb hc hd he].
case: (emptyset_dichot (substrate r)) => hf; [by left | right].
case:(countable_finite_or_N hb) => hg.
  move: (finite_set_torder_greatest ha hg hf) => [x [ /hd [y yp yq]]].
  have /yq ysr: inc y (substrate r) by order_tac.
  case: (not_le_gt (proj1 ha) ysr yp).
by rewrite hg.
Qed.

Lemma eta_likeQ: eta_like BQ_order.
Proof.
move: BQor_sr BQor_tor cardinal_Q  => pa pb pc.
have pd: countable_set BQ by apply/countableP; rewrite pc aleph0_pr1; fprops.
rewrite/eta_like /eta_like0 pa; split => //; split => //.
+ move => x xQ; exists (x -q \1q); apply/BQlt_P.
  move:(BQsum_Mps (QS_diff xQ QS1) QpsS1).
  by rewrite -  (BQdiff_sum_comm xQ QS1 QS1) BQsumC (BQdiff_sum QS1 xQ).
+ move => x xQ; exists (x +q \1q); apply/BQlt_P.
  apply:(BQsum_Mps xQ QpsS1). 
+ move => x y /BQlt_P /BQmiddle_comp [l1 l2]. 
  by exists (BQmiddle x y); split; apply/BQlt_P.
Qed.

Definition BQ_int01 := Zo BQ (fun x => \0q <q x /\ x <q \1q).
Definition BQps_order := induced_order BQ_order BQps.
Definition BQ_int01_order := induced_order BQ_order BQ_int01.

Lemma BQps_or_osr: order_on BQps_order BQps.
Proof.
set r := (induced_order BQ_order BQps).
move: BQor_sr BQor_tor => pa [pb _].
have sr1: sub BQps (substrate BQ_order) by rewrite pa; apply:BQps_sBQ.
exact:(iorder_osr pb sr1).
Qed.

Lemma BQ_int01_or_osr: order_on BQ_int01_order BQ_int01.
Proof.
set r := (induced_order BQ_order BQ_int01).
move: BQor_sr BQor_tor => pa pb.
have sr1: sub BQ_int01 (substrate BQ_order) by rewrite pa; apply: Zo_S.
exact:(iorder_osr (proj1 pb) sr1). 
Qed.


Lemma eta_likeQps: eta_like BQps_order.
Proof.
rewrite /BQps_order.
set r := (induced_order BQ_order BQps).
move: BQor_sr BQor_tor cardinal_Q  => sr' tor' cq.
have sr1: sub BQps (substrate BQ_order) by rewrite sr'; apply:BQps_sBQ.
move:(iorder_osr (proj1 tor') sr1)(total_order_sub tor' sr1); rewrite -/ r.
move => [or sr] tor.
move: cardinal_Qps => cq'.
have pd: countable_set BQps by apply/countableP; rewrite cq' aleph0_pr1; fprops.
have H: forall x y, glt r x y <-> (inc x BQps /\ x <q y).
  move => x y; split; move => [xs lxy].
    by move/iorder_gleP: xs => [za zb /BQle_P zc].
  move: lxy => [lxy nxy];split => //; apply/iorder_gle0P => //.
    move / qlt0xP: xs => ha1; apply / qlt0xP; BQo_tac.
  by apply /BQle_P. 
rewrite/eta_like /eta_like0 sr; split => //; split => //.
+ move => x xq; move: (BQhalf_pos xq)(BQhalf_pos1 xq) => qa qb.
  by exists (BQhalf x); apply/H.
+ move => x xq; exists (x +q \1q); apply/H; split => //.
  apply:(qlt_succ (BQps_sBQ xq)).
+ move => x y /H [xp /BQmiddle_comp [l1 l2]]. 
  exists (BQmiddle x y); split; apply/H => //; split => //.
  move / qlt0xP: xp => ha1; apply / qlt0xP; BQo_tac.
Qed. 

Lemma cardinal_BQ_int01: cardinal BQ_int01 = aleph0.
Proof.
apply: cleA; first by rewrite - cardinal_Q; apply: sub_smaller; apply: Zo_S.
pose f i :=  (BQ_of_Zinv (BZ_of_nat (i+c \2c))).
suff H : lf_axiom f Nat BQ_int01.
  have: injection (Lf f Nat  BQ_int01).
    apply: lf_injective => // i j iN jN /pr2_def /pr1_def.
    by move /(csum_eq2r NS2 iN jN).
  by move/inj_source_smaller; aw; rewrite cardinal_Nat.
move => i iN; move: (NS_sum iN NS2) => /BZ_of_natp_i i2N.
have pa: inc (BZ_of_nat (i +c \2c)) BZps. 
  apply/ BZps_iP;split => // /pr1_def => h.
  have: \2c <=c i +c \2c by apply: csum_Mle0; fprops.
  by rewrite h => /(cltNge clt_02).
move:(BQ_of_Zi_iQps pa) => pb.
move: (BQps_sBQ pb) => pc.
apply:Zo_i => //; split; first by apply/ qlt0xP.
split; last first.
  move /pr2_def /pr1_def => h.
  have: \2c <=c i +c \2c by apply: csum_Mle0; fprops.
  by rewrite h=> /(cltNge clt_12).  
have q1 := QS1.
have q2:= BZps_sBZp ZpsS1.
have sa: intp (BZ_of_nat (i +c \2c)) by apply:BZps_sBZ.
have sb:= ZS1.
split => //; rewrite /BQle_aux /f /BQ_of_Zinv /BQ_one /BQ_of_Z; aw.
rewrite !BZprod_1r //.
have h: \2c <=c i +c \2c by apply: csum_Mle0; fprops.
apply /zle_P1 => //; rewrite /BZ_one /BZ_of_nat ; aw.
apply: (cleT cle_12 h).
Qed.

Lemma eta_likeQp_int01: eta_like BQ_int01_order.
Proof.
rewrite /BQ_int01_order.
set r := (induced_order BQ_order BQ_int01).
move: BQor_sr BQor_tor cardinal_Q  => sr' tor' cq1.
have sr1: sub BQ_int01 (substrate BQ_order) by rewrite sr'; apply: Zo_S.
move:(iorder_osr (proj1 tor') sr1)(total_order_sub tor' sr1); rewrite -/ r.
move => [or sr] tor.
have cq2:= cardinal_BQ_int01.
have pd: countable_set BQ_int01
   by apply/countableP; rewrite cq2 aleph0_pr1; fprops.
have H: forall x y, glt r x y <-> [/\ \0q <q x, x <q y & y <q \1q].
  move => x y; split. 
    move => [ /iorder_gleP [/Zo_P [_ [ha _]] /Zo_P [_ [_ hb]] /BQle_P hc] hd].
    by split.
  move => [ha [hb hc] hd]; split => //; apply/iorder_gleP; split.
  + apply/Zo_P; split; [rewrite -/(ratp x); BQo_tac |  split => //; BQo_tac].
  + apply/Zo_P; split; [rewrite -/(ratp y); BQo_tac |  split => //; BQo_tac].
  + by apply /BQle_P. 
rewrite/eta_like /eta_like0 sr; split => //; split => //.
+ move => x /Zo_P [xq [x0 x1]]. 
  have xp: inc x BQps by apply/ qlt0xP.
  move: (BQhalf_pos xp)(BQhalf_pos1 xp) => qa qb.
  exists (BQhalf x); apply/H; split => //; by apply/  qlt0xP.
+ move => x /Zo_P [xq [x0 x1]];  move:(BQmiddle_comp x1) => [sa sb].
  exists (BQmiddle x \1q); apply/H; split => //. 
+ move => x y /H [xp /BQmiddle_comp [l1 l2] y1]. 
  exists (BQmiddle x y); split; apply/H => //; split => //; BQo_tac.
Qed.


Lemma perm_ints n f: 
  natp n -> surjection f -> source f = n -> target f = n ->
  inc f  (permutations n).
Proof.
move => nN pb pc pd; apply/permutationsP; split => //.
apply:bijective_if_same_finite_c_surj => //; first by rewrite pc pd.
by rewrite pc; apply:finite_set_nat.
Qed.

Definition EPperm_extend_aux n k s := 
  fun z => Yo (z <c k) (Vf s z) (Yo (z = k) n (Vf s (cpred z))).

Definition EPperm_extend n k s :=
  Lf (EPperm_extend_aux n k s) (csucc n) (csucc n).

Lemma EPperm_extend_perm n k s : natp n -> k <=c n -> inc s (permutations n) ->
  [/\ lf_axiom (EPperm_extend_aux n k s) (csucc n) (csucc n)
     &  inc (EPperm_extend n k s) (permutations (csucc n))].
Proof.
move => nN lin /permutationsP [[_ [ff sf]] pc pd].
have nsN := (NS_succ nN).
have ax: lf_axiom (EPperm_extend_aux n k s) (csucc n) (csucc n). 
  rewrite/EPperm_extend_aux;move => z za /=; Ytac h1.
    apply (proj33 (cleS nN)); rewrite - pd; apply:(Vf_target ff); rewrite pc.
    by move/(NltP nN): (clt_leT h1 lin).
  case: (equal_or_not z k) => ekz; Ytac0; first by apply: (Nsucc_i nN).
  apply (proj33 (cleS nN)); rewrite - pd; apply:(Vf_target ff); rewrite pc.
  case: (equal_or_not z \0c) => zz.
    case: h1; split => //; rewrite zz; apply: (cle0x (proj31 lin)).
  have zN:= (NS_inc_nat nsN za).
  move:(cpred_pr zN zz) => [qa qb].
  by apply/(NltP nN) /(cleSltP qa); rewrite - qb; apply/(NleP nN).
split=> //.
rewrite /EPperm_extend; apply:perm_ints; aw; trivial.
apply:(lf_surjective ax); rewrite /EPperm_extend_aux.
move => y /(NleP nN) yn; case: (equal_or_not y n).
  move => ->; exists k; first by apply/(NleP nN). 
  Ytac h;[ by case: (proj2 h) | by Ytac0 ].
move => nyn.
have : inc y (target s) by rewrite pd; apply/(NltP nN).
move/sf => [z sz ->]; rewrite pc in sz. 
move/(NltP nN): sz =>  sz; move: (NS_lt_nat sz nN) => nz.
case: (cleT_el (proj31 lin) (CS_nat nz)) => h; last first.
  exists z; [  apply/(NleP nN); exact: (proj1 sz) | by  Ytac0]. 
move: (cltS nz) => h3; move:(cle_ltT h h3) => [h4 h5].
exists (csucc z); first by apply/(NltP nsN); apply:cltSS.
rewrite (Y_false (cleNgt h4)) (Y_false (nesym h5)) cpred_pr2//.
Qed.


Section EtaProp.

Variables r1 r2 f g: Set.
Hypothesis bij_f:  bijection_prop f Nat (substrate r1).
Hypothesis bij_g:  bijection_prop g Nat (substrate r2).
Hypothesis eta_like_r1: eta_like r1.
Hypothesis eta_like_r2: eta_like r2.

Definition EPperm_M s n:=
   inc s (permutations n) /\
   forall i j, i<c j -> j <c n -> glt r1 (Vf f (Vf s i)) (Vf f (Vf s j)).

Definition EPperm_compat0 r h n k x :=
   [/\ k <=c n,
    (k = \0c -> glt r x (h \0c)),
    (k = n -> k <>\0c -> glt r (h (cpred n)) x) &
    (k <c n -> k <> \0c -> (glt r (h (cpred k)) x) /\ glt r x (h k)) ].

Definition EPperm_compat s n k :=
   EPperm_compat0 r1 (fun i =>  (Vf f (Vf s i))) n k (Vf f n).

Definition EPperm_next_index  n s :=
  Yo (n= \0c) \0c (select (EPperm_compat s n) Nat).

Lemma EPperm_compat_0 s: EPperm_next_index \0c s = \0c.
Proof. by rewrite /EPperm_next_index; Ytac0. Qed.

Lemma EPperm_compat_uniq s n i j:
  natp n -> EPperm_M s n ->
  EPperm_compat s n i ->  EPperm_compat s n j -> i = j.
Proof.
move =>  pc [pd pe] [lin qa qb qc] [ljn qa' qb' qc'].
have or: order r1 by move:eta_like_r1 => [[[]]].
have jN:= NS_le_nat ljn pc. 
have iN:= NS_le_nat lin pc.
have aux1: n <> \0c -> \0c <c n by apply:card_ne0_pos; fprops.
pose F i := (Vf f (Vf s i)).
have rpe: forall i j, i <c n -> j <c n  ->  glt r1 (F i) (F j) -> i <c j.
  move => i1 j1 lin1 ljn1 [le1 ne1].
  case: (cleT_ell (proj31_1 lin1)(proj31_1 ljn1)) => // h.
     by case: ne1; rewrite h.
  move:(pe _ _ h lin1) => le2; order_tac.
have re: forall k, k <=c n -> glt r1 (F (cpred k)) (F \0c) -> False.
  move => k lkn H.
  case: (equal_or_not k \0c) => knz.
    by case:(proj2 H); rewrite knz cpred0.
  have ha:= (clt_leT (cpred_lt (NS_le_nat lkn pc) knz) lkn).
  case: (equal_or_not n \0c) => nz. 
     by case knz; apply: (cle0); rewrite  - nz.
  by move: (rpe _ _ ha (aux1 nz) H) => /(clt0).
case: (equal_or_not i \0c) => iz.
  case: (equal_or_not j \0c) => jz; first by rewrite iz jz.
  have ha: glt r1 (Vf f (Vf s (cpred j))) (Vf f n).
    case: (equal_or_not j n) => jn; first by move:(qb' jn jz); rewrite jn.
    by case: (qc' (conj ljn jn) jz).
  case:(re _ ljn (lt_lt_trans or ha (qa iz))).
case:(equal_or_not n \0c) => enz; first by case: iz; apply:cle0;  ue.
have Ha: glt r1 (Vf f (Vf s (cpred i))) (Vf f n).
  case: (equal_or_not i n) => jn; first by move:(qb jn iz); rewrite jn.
  by case:(qc (conj lin jn) iz).
have rf: forall k, k <c n -> ~ glt r1 (Vf f (Vf s (cpred n))) (Vf f (Vf s k)).
  move => k kn H.
  have [sa sb]:=(cpred_pr pc enz).
  move:(rpe _ _ (cpred_lt pc enz) kn H) =>/(cleSltP sa). 
  by rewrite - sb => /(cltNge kn).
have [sa sb]:=(cpred_pr iN iz).
case: (equal_or_not i n) => ein.
  rewrite ein in iz sa sb |- *.
  case: (equal_or_not j \0c) => jnz.
    case: (re _ lin (lt_lt_trans or Ha (qa' jnz))).
  ex_middle jn; move:(conj ljn (nesym jn)) => ltjn; case: (rf j ltjn).
  by move:(lt_lt_trans or Ha (proj2 (qc' ltjn jnz)));rewrite ein.
have Hb:= (proj2 (qc (conj lin ein) iz)).
have sc: (cpred i) <c n by apply/(cleSltP sa); rewrite - sb.
case:(equal_or_not j \0c) => jz. 
  case:(re _ lin (lt_lt_trans or Ha (qa' jz))).
case:(equal_or_not j n) => jn.
  by move:(lt_lt_trans or (qb' jn jz) Hb) => ha; case: (rf i (conj lin ein)).
move: (qc' (conj ljn jn) jz) => [Hc Hd].
have [sa1 sb1]:=(cpred_pr jN jz).
have sd: (cpred j) <c n by apply/(cleSltP sa1); rewrite - sb1.
move:(rpe _ _ sc (conj ljn jn) (lt_lt_trans or Ha Hd)) => ra.
move:(rpe _ _ sd (conj lin ein) (lt_lt_trans or Hc Hb)) => rb.
case: (NleT_ell iN jN); first by exact.
  by rewrite sb1; move/(cltSleP sa1) => /(cltNge rb).
by rewrite sb;  move/(cltSleP sa) => /(cltNge ra). 
Qed.

Lemma EPperm_compat0_exists r n h x:
  natp n -> n <> \0c -> total_order r ->
  (inc x (substrate r)) -> 
  (forall i, i <c n -> inc (h i) (substrate r)) ->
  (forall i, i <c n -> (h i) <> x) ->
  exists k, (EPperm_compat0 r h n k x).
Proof.
move => nN nz [or tor] xsr hsr xnr.
move:(cpred_pr nN nz) => [sa sb].
have nn:= (cpred_lt nN nz).
have cpi: inc (cpred n) n by apply /(NltP nN).
set y := h (cpred n).
have ysr: inc y (substrate r) by apply: hsr.
have xny: y <> x by apply: xnr.
case: (tor _ _ ysr xsr) => lta.
  exists n; split; fprops.
  + by move => ha;case: (@succ_nz (cpred n)).
  + by move => _ _. 
  + by case.
pose prop z := z <c n /\ glt r x (h z).
have nE: prop (cpred n) by split => //;split => //; apply: nesym.
case:(least_int_prop2 sa nE). 
  by move => [/proj1 qa [qb qc]]; exists \0c; split.
set i := cpred _; move => [iN [ha hb]] aE.
have lin:=(cle_ltT (cleS iN) ha).
have hc:inc i n by apply/(NltP nN).
have hix: h i <> x by  apply:xnr.
have he: glt r (h i) x.
  case: (tor _ _  (hsr _ lin) xsr) => // hf. 
  by case: aE; split => //;  split => //; apply: nesym.
exists (csucc i); split.
+ exact: (proj1 ha).
+ by move => hw; case: (@succ_nz i).
+ by move: (proj2 ha).
+ by move => ua ub; rewrite (cpred_pr2 iN).
Qed.

Lemma EPperm_compat_exists  n s:
  natp n -> n <> \0c -> EPperm_M s n ->
  exists k, EPperm_compat s n k.
Proof.
move => nN np [ /permutationsP [[ins [fs ss]] qc qd] _].
have tor: total_order r1 by move:eta_like_r1 => [[]].
move:bij_f => [[[ff ijf] _] sf tf].
have nsf: inc n (source f) by ue.
have aux: forall i, inc i n ->  inc (Vf s i) (source f).
  move => i ii; rewrite sf; apply/(NS_inc_nat nN); Wtac.
apply:EPperm_compat0_exists => //.
+ by Wtac. 
+ move => i /(NltP nN) ii; Wtac.
+ move => i /(NltP nN) ii eq.
  move:(cpred_pr nN np) => [sa sb].
  move: (ijf (Vf s i) n (aux _ ii) nsf eq) => bad.
  have /(NltP nN) [_ [//]]: inc  (Vf s i) n by Wtac. 
Qed.

Lemma EPperm_next_indexP n s (k:= EPperm_next_index n s):
  natp n -> n <> \0c -> EPperm_M s n ->
  (EPperm_compat s n k).
Proof.
move => nN nz pe.
suff [ //]: ((EPperm_compat s n k) /\ (inc k Nat)).
rewrite /k / EPperm_next_index; Ytac0.
apply: select_pr.
  move:(EPperm_compat_exists nN nz pe) => [j ja].
  exists j => //;move: ja => [ja _ _ _]; apply: (NS_le_nat ja nN).
move => j1 j2 _ ja _ jb; exact:(EPperm_compat_uniq nN  pe ja jb).
Qed.

Lemma EPperm_next_unique2 n s l (k:= EPperm_next_index n s):
  natp n -> n <> \0c -> EPperm_M s n ->
  EPperm_compat s n l -> l = k.
Proof.
move => nN nz sm h.
exact: (EPperm_compat_uniq nN sm h (EPperm_next_indexP nN nz sm)).
Qed. 


Lemma EPperm_extend_M n s k:
  natp n -> n <> \0c ->
  EPperm_M s n -> (EPperm_compat s n k) -> 
  EPperm_M (EPperm_extend n k s) (csucc n).
Proof.
move => nN nz [pe pf] [ph pg1 pg2 pg3].
have [ax pi]:=(EPperm_extend_perm nN ph pe).
split => // i j ij jn.
have snN:= NS_succ nN.
have jN: inc j (csucc n) by apply /(NltP snN).
have iN: inc i (csucc n) by apply /(NltP snN); apply: (clt_ltT ij jn).
rewrite /EPperm_extend !LfV//.
rewrite /EPperm_extend_aux. 
have kc:= (proj31 ph).
case: (p_or_not_p (j <c k)) => ljk; Ytac0.
  have ik:= (clt_ltT ij ljk).
  Ytac0; apply: pf => //; exact:(clt_leT ljk ph).
have or: order r1 by move:eta_like_r1 => [[[]]].
case (equal_or_not j k) => ejk; Ytac0.
  rewrite ejk in ij; Ytac0.
  case (equal_or_not k \0c) => ekz; first by case: (@clt0 i);rewrite - ekz.
  have ha: glt r1 (Vf f (Vf s (cpred k))) (Vf f n).
    case (equal_or_not k n) => ekn.
     by move: (pg2 ekn ekz); rewrite ekn.
     exact:(proj1 (pg3 (conj ph ekn) ekz)). 
  have [sa sb]:= (cpred_pr (NS_le_nat ph nN) ekz).
  case: (equal_or_not i (cpred k)); [ by move -> | move => nin].
  have ra: i <c cpred k by split => //;  apply/(cltSleP sa); ue.
  have rb: cpred k <c k by rewrite {2} sb; apply: cltS.
  exact:(lt_lt_trans or (pf _ _ ra (clt_leT rb ph))). 
have lkj: k <c j by case: (cleT_ell (proj32_1 ij) kc).
case: (equal_or_not j \0c) => jz; first by move: lkj; rewrite jz => /clt0. 
move /(cltSleP nN): (jn) => jn1.
have [sa sb] := (cpred_pr (NS_le_nat jn1 nN) jz).
have sc: cpred j <c n by apply/(cleSltP sa); rewrite - sb.
have sd: k <=c cpred j by apply /(cltSleP sa); ue.
case: (p_or_not_p (i <c k)) => lik; Ytac0; first apply: pf (clt_leT lik sd) sc.
case: (equal_or_not i k) => eik; Ytac0.
  case: (equal_or_not k \0c) => ei0. 
     move:(pg1 ei0) => ha; 
     case: (equal_or_not (cpred j) \0c);[by move -> | move => h].
     have h1: \0c <c cpred j by apply: card_ne0_pos; fprops.
     exact:(lt_lt_trans or ha (pf _ _ h1 sc)).
  have lin:= cle_ltT sd sc.
  move:(pg3 lin ei0)=> [_ sv];case (equal_or_not k (cpred j)) =>h; first by ue.
  exact:(lt_lt_trans or sv (pf _ _ (conj sd h) sc)).
case: (equal_or_not i \0c) => iz.
  by case lik; rewrite iz; apply:(card_ne0_pos kc) => kz; case eik; rewrite kz.
have kp1: i <=c (cpred j) by apply /(cltSleP sa); ue.
have [se sf] := (cpred_pr (NS_le_nat kp1 sa) iz).
have ip2: cpred i <c cpred j by apply/(cleSltP se); ue.
exact: (pf _ _ ip2 sc).
Qed.


Lemma EPperm_extend_M2 n s 
    (k:= EPperm_next_index n s) (s':= (EPperm_extend n k s)):
  natp n -> n <> \0c -> EPperm_M  s n -> EPperm_M s' (csucc n).
Proof.
move => pc pd pe.
exact: (EPperm_extend_M pc pd pe (EPperm_next_indexP pc pd pe)).
Qed.

Lemma EPperm_extend_M3: EPperm_M empty_function \0c.
Proof.
split; last by move => i j _ /clt0.
have [pa pb pc]:= empty_function_function.
by apply: (perm_ints NS0 _ pb pc);split => //; rewrite pc => y /in_set0.
Qed.

Lemma EPperm_extend_M4: EPperm_M (identity \1c) \1c.
Proof.
split; first by apply: permutation_id.
move => i j  lij lj1; move: (lj1) => [_ nj1].
case:(clt2 (clt_ltT lj1 clt_12)) => // jz.
by move: lij; rewrite jz => /clt0.
Qed.

Definition EPperm_rec :=
   induction_term (fun n s =>
       (Yo (n = \0c) (identity \1c)  
          (EPperm_extend n (EPperm_next_index n s) s))) empty_function.

Lemma EPperm_rec0: (EPperm_rec \0c) =  empty_function.
Proof. apply: induction_term0. Qed.

Lemma EPperm_rec1: (EPperm_rec \1c) = (identity \1c).
Proof. 
by rewrite - {1} succ_zero /EPperm_rec (induction_terms _ _ NS0); Ytac0. 
Qed.

Lemma EPperm_recs n: natp n -> n <> \0c ->
   (EPperm_rec (csucc n)) = 
   EPperm_extend n (EPperm_next_index n (EPperm_rec n)) (EPperm_rec n).
Proof.
move => pa pb.
by rewrite /EPperm_rec (induction_terms _ _ pa); Ytac0.
Qed.

Lemma EPperm_recs_mon n: natp n -> EPperm_M (EPperm_rec n) n.
Proof.
move:n; apply:Nat_induction.
  rewrite EPperm_rec0; apply:EPperm_extend_M3.
move => n nN Hrec;case: (equal_or_not n \0c) => nz.
  rewrite nz succ_zero EPperm_rec1; apply :EPperm_extend_M4.
by rewrite (EPperm_recs nN nz); apply:EPperm_extend_M2.
Qed.

Definition EPpermi_fct h n k := 
    intersection (Zo Nat (fun j => EPperm_compat0 r2 h n k (Vf g j))).

Lemma EPpermi_pr0  h n k: natp (EPpermi_fct h n k).
Proof. by apply:NS_inf_Nat; apply:Zo_S. Qed.

Lemma EPpermi_compat0_exists r h n k G :
  natp n -> n <> \0c -> k <=c n ->  
  eta_like r -> bijection_prop G Nat (substrate r) ->
  (forall i j, i<c j -> j <c n -> glt r (h i) (h j)) ->
  (forall j, j <c n -> inc (h j) (substrate r))  ->
  exists2 i, inc i Nat &   EPperm_compat0 r h n k (Vf G i).
Proof. 
move => nN nz lin [[[or1 tor1] _ pa pb pc] _ ] [bG sG tG] ha hb.
have fG: function G by fct_tac.
have qb: inc (h \0c) (substrate r).
  by apply: hb; apply:(card_ne0_pos (CS_nat nN) nz).
case: (equal_or_not k \0c) => iz.
  have [y ya] := (pa _ qb).
  have : inc y (substrate r) by order_tac.
  rewrite - tG; move /(proj2 (proj2 bG))=> [jj ja jb].
  rewrite iz in lin; rewrite sG in ja. 
  by ex_tac; hnf; rewrite iz; split => //;rewrite - jb.
have [sa sb]:= (cpred_pr nN nz).
case (equal_or_not k n) => ein.
  move: (cltS sa); rewrite - sb => /hb /pb [y ya].
  have : inc y (substrate r) by order_tac.
  rewrite - tG; move /(proj2 (proj2 bG))=> [jj ja jb].
  rewrite sG in ja; ex_tac; hnf; split => //;[ by rewrite -jb | by move => [_]].
have [sc sd]:= (cpred_pr (NS_le_nat lin nN) iz).
move:(cltS sc); rewrite - sd => hc.
have [y [ya yb]]:= (pc _ _  (ha _ _ hc (conj lin ein))).
have : inc y (substrate r) by order_tac.
rewrite - tG; move /(proj2 (proj2 bG))=> [jj ja jb].
by rewrite sG in ja; ex_tac; hnf; split => //; rewrite -jb.
Qed.


Lemma EPpermi_pr  h n k (j := EPpermi_fct h n k)
   (P := fun m => EPperm_compat0 r2 h n k (Vf g m)) :
   (forall i j, i<c j -> j <c n -> glt r2 (h i) (h j)) ->
   (forall j, j <c n -> inc (h j) (substrate r2)) ->
   natp n -> k <=c n -> n <> \0c ->
  [/\ inc j Nat, P j & forall k, inc k Nat -> P k -> j <=c k].
Proof.
move:eta_like_r2 bij_g => [[tor _ pa pb pc] _ ][bg sg tg] iss qa nN lin nz.
set E := (Zo Nat (fun j => EPperm_compat0 r2 h n k (Vf g j))).
have ha: sub E Nat by apply: Zo_S.
have [z za zb]:exists2 j, inc j Nat & EPperm_compat0 r2 h n k (Vf g j).
  by apply:EPpermi_compat0_exists.
have hb: nonempty E by exists z;apply : Zo_i.
move: (inf_Nat ha hb) => [/Zo_P [hc hd] he]; split => //m ka kb; apply:he.
by apply : Zo_i.
Qed.

Lemma EPpermi_exten h1 h2 n k:
  natp n -> n <> \0c ->
  (forall i, i<c n -> h1 i = h2 i) ->
  EPpermi_fct h1 n k = EPpermi_fct h2 n k.
Proof.
move => nn nz sv.
rewrite /EPpermi_fct; apply: f_equal.
have zn1: \0c <c n by apply: card_ne0_pos; fprops.
have cp1: cpred n <c n by apply: cpred_lt.
apply:Zo_exten2 => x;  rewrite /EPperm_compat0. 
rewrite (sv _  zn1) (sv _ cp1).
case: (equal_or_not k \0c) => kz.
   split; move => [xN [pa pb pc pd]]; split =>//; split => //.
case: (equal_or_not k n) => kn.
  rewrite kn;split; move => [xN [pa pb pc pd]]; split =>//; split => // [][] //.
case (p_or_not_p ( k <=c n)) => hh; last first.
  split; move => [xN [pa _ _ _]]; split =>//; split => //.
have ckn: cpred k <c n. 
   move:(cpred_pr (NS_le_nat hh nn) kz) => [sa sb].
   by apply /(cleSltP sa); rewrite - sb.
rewrite sv // sv //.
Qed.

Definition EPpermi_next ph n (s:= EPperm_rec n)
   (h := fun i => Vf g (Vf ph (Vf s i)))
   (k := (EPperm_next_index n s)) :=
  Yo (n = \0c) \0c (EPpermi_fct h n k).

Definition EPpermi_prop ph n := 
  [/\ function ph, source ph = n, sub (target ph) Nat &
     (forall i j, i <c n -> j <c n -> 
       (glt r1 (Vf f i) (Vf f j) <->
       glt r2 (Vf g (Vf ph i)) (Vf g (Vf ph j))))].


Lemma EPpermi_next_pr1 ph n
  (k1 := EPpermi_next ph n)
  (ph1 := extension ph n k1):
  natp n -> (EPpermi_prop ph n) -> 
  [/\ (Vf ph1 n) = k1, forall i, i <c n -> Vf ph1 i = Vf ph i &
    (EPpermi_prop ph1 (csucc n))].
Proof. 
move => nN [fh sh th mh].
have nns: ~(inc n (source ph)) by  rewrite sh => /(NltP nN) [_].
have fe := (extension_f k1 fh nns).
have Vo := (extension_Vf_out k1 fh nns).
have Vi := (extension_Vf_in k1 fh nns).
have Vi1: forall i, i <c n -> Vf ph1 i = Vf ph i.
  by move => i /(NltP nN) lin; apply:Vi; rewrite sh.
have sph1: source ph1 = csucc n.
  by rewrite /ph1 /extension corresp_s sh (succ_of_nat nN).
have tph1: sub (target ph1) Nat.
   rewrite /ph1 /extension; aw => t /setU1_P;case;[by apply: th| move ->].
   rewrite /k1 /EPpermi_next; Ytac w; [apply: NS0 | exact: EPpermi_pr0].
set s:=  (EPperm_rec n).
have pa: EPperm_M s n by apply: EPperm_recs_mon.
case: (equal_or_not n \0c) => nz.
  rewrite nz; split => //.
  + by rewrite - Vo /ph1 nz.
  + by move => i /clt0.
  + split => //; first by rewrite - nz.
  by move => i j /(cltSleP NS0) /cle0 ->
     /(cltSleP NS0) /cle0 ->; split => [][_].
have pb:= (EPperm_next_indexP nN nz pa).
move:pa => [/permutationsP [bs ss ts] sis]; move: (proj1 (proj1 bs)) => fs.
pose h i :=(Vf g (Vf ph (Vf s i))).
move: bij_g => [bg sg tg]; move: (proj1 (proj1 bg)) => fg.
have pc: forall k, k<c n -> (Vf s k) <c n.
  by move=> k /(NltP nN) kn; apply /(NltP nN); Wtac.
have pe:(forall j, j <c n -> inc (h j) (substrate r2)).
  move => j /(NltP nN) ljn; rewrite /h - tg; Wtac; rewrite sg; apply: th; Wtac.
  rewrite sh; Wtac; fct_tac. 
have pd:(forall i j, i <c j -> j <c n -> glt r2 (h i) (h j)). 
  move => i j lij ljn.
  apply/(mh _ _ (pc i (clt_ltT lij ljn)) (pc j ljn)); by apply: sis.
move: (pb) =>[lk0n _ _ _ ].
move:(EPpermi_pr pd pe nN lk0n nz).
set k0:=  (EPperm_next_index n s). 
have <-: k1 = EPpermi_fct h n k0 by rewrite /k1 /EPpermi_next; Ytac0.
move => [k1N qb qc].
have [or1 tor1]:total_order r1  by move: (eta_like_r1) =>[[]].
have [or2 tor2]:total_order r2  by move: (eta_like_r2) =>[[]].
move: bij_f => [bf sf tf]; move: (proj1 (proj1 bf)) => ff.
have snN:= (NS_succ nN). 
rewrite -/k0 in pb.
have [qb1 qb2 qb3 qb4] := qb.
have [pb1 pb2 pb3 pb4] := pb.
have qd1:forall j, j <c n -> 
  glt r1 (Vf f n) (Vf f j) -> glt r2 (Vf g k1) (Vf g (Vf ph j)).
  move => j ljn la.
  have jts: inc j (target s) by rewrite ts; apply/(NltP nN).
  move: (proj2(proj2 bs) _ jts) => [i iss iv]; rewrite iv -/(h i).
  rewrite iv in la.
  have lin: i<c n by apply/(NltP nN); ue.
  case: (equal_or_not k0 \0c) => ke0.
    have ra:= (qb2 ke0).
    case (equal_or_not i \0c) => iz; first by rewrite iz.
    have ip: \0c <c i by apply:(card_ne0_pos (proj31_1 lin) iz).
    by move: (pd \0c i ip lin) => ha; order_tac.
  have kN :=(NS_le_nat qb1 nN).
  have [re rf]:= (cpred_pr kN ke0).
  have nn: cpred k0 <c n by apply/(cleSltP re); ue.
  case: (equal_or_not k0 n) => ken.
    move:(qb3 ken ke0) (pb3 ken ke0) => ra rb.
    have rc:= (lt_lt_trans or1 rb la).
    rewrite - ken in lin.
    have lein: i <=c (cpred k0) by apply /(cltSleP re); ue.
    case: (equal_or_not i (cpred n)) => ltin; first by case: (proj2 rc); ue.
    rewrite - ken in ltin rc.
    move:(sis  _ _ (conj lein ltin) nn) => rg; order_tac.
  have [ra rb ] := (qb4 (conj qb1 ken) ke0). 
  have [rc rd]:= (pb4 (conj qb1 ken) ke0).
  case:(cleT_ell (proj31_1 lin) (proj31 qb1)) => rg.
  + by rewrite rg.
  + move:(lt_lt_trans or1 rc la) => rh.
    have lein: i <=c (cpred k0) by apply /(cltSleP re); ue.
    case: (equal_or_not i (cpred k0)) => ltin; first by case: (proj2 rh); ue.
    move: (sis _ _ (conj lein ltin) nn) => ri; order_tac.
  + by move: (pd _ _ rg lin) => rh; order_tac.
have qd2:forall j, j <c n -> 
  glt r1 (Vf f j) (Vf f n) -> glt r2 (Vf g (Vf ph j)) (Vf g k1).
  move => j ljn la.
  have jts: inc j (target s) by rewrite ts; apply/(NltP nN).
  move: (proj2(proj2 bs) _ jts) => [i iss iv]; rewrite iv -/(h i).
  rewrite iv in la.
  have lin: i<c n by apply/(NltP nN); ue.
  case: (equal_or_not k0 \0c) => ke0.
    have ra := (lt_lt_trans or1 la (pb2 ke0)).
    case (equal_or_not i \0c) => iz; first by case: (proj2 ra);rewrite iz.
    have ip: \0c <c i by apply:(card_ne0_pos (proj31_1 lin) iz).
    move: (sis _ _ ip lin) => rb; order_tac.
  have kN :=(NS_le_nat qb1 nN).
  have [re rf] := (cpred_pr kN ke0).
  have nn: cpred k0 <c n by apply/(cleSltP re); ue.
  case: (equal_or_not k0 n) => ken.
    have ra:= (qb3 ken ke0).
    rewrite ken in re rf nn.
    have lein: i <=c (cpred n) by apply /(cltSleP re); ue.
    case: (equal_or_not i (cpred n)) => ltin; first by rewrite ltin.
    move:(pd  _ _ (conj lein ltin) nn) => rg; order_tac.
  have [ra rb] :=(qb4 (conj qb1 ken) ke0). 
  have [rc rd] := (pb4 (conj qb1 ken) ke0).
  have rg := (lt_lt_trans or1 la rd).
  case:(cleT_ell (proj31_1 lin) (proj31 qb1)) => rh.
  + by case: (proj2 rg); rewrite rh.
  + have lein: i <=c (cpred k0) by apply /(cltSleP re); ue.
    case: (equal_or_not i (cpred k0)) => ltin; first by  rewrite ltin.
    move: (pd _ _ (conj lein ltin) nn) => ri; order_tac.
  + by move: (sis _ _ rh lin) => ri; order_tac.
have sra: inc (Vf f n) (substrate r1) by Wtac; ue.
have jinv: forall j,  j <c n ->  (Vf f j) <>  (Vf f n).
  move => j [lejn nejn] eq.
  have ijs: inc j (source f) by rewrite sf; apply:(NS_le_nat lejn nN).
  have ins: inc n (source f) by rewrite sf. 
  by move:(proj2 (proj1 bf) _ _ ijs ins eq).
have qd3: forall j,  j <c n ->
     ( glt r1 (Vf f n) (Vf f j) <-> glt r2 (Vf g k1) (Vf g (Vf ph j))).
  move => j ljn; split; [ by apply: qd1 | move => ha].
  have ji := (jinv _ ljn).
  have srb: inc (Vf f j) (substrate r1). 
    Wtac; rewrite sf; apply:(NS_lt_nat ljn nN).
  case: (tor1 _ _ sra srb) => ra; first by split => //; exact:(nesym ji).
  move:(qd2 _ ljn (conj ra ji)) => rb; order_tac.
have qd4: forall j,  j <c n ->
     ( glt r1 (Vf f j) (Vf f n) <-> glt r2 (Vf g (Vf ph j))  (Vf g k1)).
  move => j ljn; split; [ by apply: qd2 | move => ha].
  have ji := (jinv _ ljn).
  have srb: inc (Vf f j) (substrate r1). 
    Wtac; rewrite sf; apply:(NS_lt_nat ljn nN).
  case: (tor1 _ _ sra srb) => ra; last by split => //; exact:(nesym ji).
  move:(qd1 j ljn (conj ra (nesym ji))) => rb; order_tac.
split => //; split => //.
move => i j /(cltSleP nN) lin /(cltSleP nN) ljn.
case (equal_or_not i n) => ein.
  rewrite ein Vo.
  case (equal_or_not j n) => ejn.
     by rewrite ejn Vo; split; move => [_ ];case.
  by rewrite (Vi1 _ (conj ljn ejn)); apply: qd3.
move: (conj lin ein) => ltin; rewrite  (Vi1 _ ltin).
case (equal_or_not j n) => ejn; last first.
  rewrite  (Vi1 _ (conj ljn ejn));exact: (mh _ _  ltin (conj ljn ejn)).
by rewrite ejn Vo; apply: qd4.
Qed.

Definition EPfun_aux :=
 transfinite_defined Nat_order (fun u => (EPpermi_next u (source u))).



Lemma EPfun_aux_pr1 (h := EPfun_aux) :
  [/\ surjection h, source h = Nat, sub (target h) Nat,
      Vf h \0c = \0c &
     forall n, natp n -> Vf h n = EPpermi_next (restriction1 h n) n].
Proof.
move:Nat_order_wor => [pa pb].
move:(transfinite_defined_pr (fun u => (EPpermi_next u (source u))) pa).
rewrite -/EPfun_aux -/h; move => [ha hb hc].
rewrite pb in hc hb.
have hh: forall x, natp x -> source (restriction1 h (segment Nat_order x)) = x.
  move => x xN; rewrite / restriction1; aw.
  by rewrite (segment_Nat_order1 xN).
have sth: sub (target h) Nat.
  move => t /(proj2 ha) [n nN ->]; rewrite hb in nN.
  rewrite (hc _ nN) /EPpermi_next; Ytac w; [exact: NS0 |exact: EPpermi_pr0].
split => //.
  by rewrite (hc _ NS0) (hh _ NS0) / EPpermi_next; Ytac0.
move => n nN.
rewrite (hc _ nN) (hh _ nN) .
by rewrite (segment_Nat_order1 nN) - (NintE nN).
Qed.


Lemma EPfun_aux_pr2 n: natp n ->
  EPpermi_prop (restriction1  EPfun_aux n) n.
Proof.
pose H k := (restriction1 EPfun_aux k).
move:(EPfun_aux_pr1) => [q1 q2 q3 q4 q5].
have fh := proj1 q1.
have H0: forall k, natp k -> sub k (source EPfun_aux). 
   by move => k kN;rewrite q2; apply: NS_inc_nat.
have sjn: forall k, natp k -> surjection (H k).
  move => k kN;apply: (restriction1_fs fh (H0 _ kN)).
have ssn: forall k, natp k -> source (H k) = k.
  by move => k kN; rewrite /H/ restriction1; aw.
move: n; apply: Nat_induction.
  rewrite -/(H \0c); split => //. 
  + exact: (proj1(sjn _ NS0)). 
  + exact: (ssn _ NS0).
  + rewrite /H / restriction1; aw => t.
    have ww: sub \0c (source EPfun_aux) by fprops.
    by move/(Vf_image_P (proj1 q1) ww) => [u  /in_set0].
  + by move => i j /clt0.
move => n nN Hrec.
have snN := NS_succ nN.
move: (EPpermi_next_pr1 nN Hrec).
rewrite -/(H n) -/(H (csucc n)).
set ph1 := extension _ _ _; move => [p1 p2 p3].
have -> // : (H (csucc n)) = ph1.
have nnI: ~inc n (source (H n)).
   by rewrite /H/ restriction1; aw;move /(NltP nN) => [].
have shn := sjn n nN.
have fhn:= proj1 shn.
move: (H0 _ nN)(H0 _ snN) => qa qb.
apply: function_exten4 => //.
+ by rewrite  /ph1 /extension corresp_s ! ssn // (succ_of_nat nN).
+ exact:(sjn _ snN).
+ apply: extension_fs=> //;fct_tac.
+ move => x; rewrite (ssn _ snN) => xi.
  rewrite /H restriction1_V //. 
  move: xi;rewrite (succ_of_nat nN)  => /setU1_P; case => xn.
    have xs: inc x (source (H n)) by rewrite (ssn _ nN).
    rewrite /ph1  extension_Vf_in // /H restriction1_V //. 
  by rewrite /ph1 xn extension_Vf_out // (q5 _ nN).  
Qed.


Lemma EPfun_aux_M i j (h:= EPfun_aux): natp i -> natp j ->
  (glt r1 (Vf f i) (Vf f j) <->
   glt r2 (Vf g (Vf h i)) (Vf g (Vf h j))).
Proof.
move => iN jN.
move: (cmax_p1 (CS_nat iN) (CS_nat jN)).
set n0 := cmax i j; move => [le1 le2].
have n0N: natp n0 by  apply:Gmax_E.
set n := csucc n0.
have nN: natp n by apply/(NS_succ n0N).
move: (cltS n0N); rewrite -/n => lnn.
have lt1:= (cle_ltT le1 lnn).
have lt2:=(cle_ltT le2 lnn).
move:(EPfun_aux_pr2 nN) => [_ _ _ pd].
move: EPfun_aux_pr1  => [[qa _] qb qc _].
have i1: inc i n by apply /(NltP nN).
have j1: inc j  n by apply /(NltP nN).
have qd: sub  n (source EPfun_aux) by rewrite qb; apply: NS_inc_nat.
by move: (pd i j lt1 lt2); rewrite restriction1_V // restriction1_V //.
Qed.


Definition EPperm_2pos m k1 q n
   (s :=  EPperm_rec m)   (f1 := fun i => Vf f (Vf s i))
   (h:= fun i => Vf g (Vf EPfun_aux (Vf s i)))
   (P1 := fun i => EPperm_compat0 r1 f1 m q (Vf f i)) :=
   (P1 k1 /\ (forall i, natp i -> P1 i -> k1 <=c i))
  /\ EPperm_compat0 r2 h m q (Vf g n).


Lemma EPpermi_extension2 m k0 k1 n
  (k2 := EPperm_next_index m (EPperm_rec m))
  (k0' := Yo (k0 <c k2) k0 (csucc k0)):
  natp m -> m <> \0c -> k2 <> k0 -> 
  EPperm_2pos m k1 k0 n ->
  EPperm_2pos (csucc m) k1 k0' n.
Proof.
move => mN mz ne1 [[q1 q2] q3]; hnf.
move: (EPperm_next_indexP mN mz (EPperm_recs_mon mN)); rewrite -/k2 => pra.
move: pra => [k2m _ _ _ ].
have axs:=proj1 (EPperm_extend_perm mN k2m (proj1 (EPperm_recs_mon mN))).
move:(EPperm_recs mN mz).
set s := (EPperm_rec m); set s' := (EPperm_rec (csucc m)).
rewrite -/k2 => s'v.
have wa: forall i, i <=c m -> (Vf s' i) = EPperm_extend_aux m k2 s i.
  move => i /(NleP mN) lim;  rewrite s'v  /EPperm_extend LfV//.
have lt3: \0c <=c m by apply:cle0n.
have lt0: \0c <=c csucc m by exact (proj1 (succ_positive m)).
split.
  have [k0m rb rc rd] := q1.
  have k0N := NS_le_nat k0m mN.
  have k0'm: k0' <=c csucc m.
    move: (cleS mN) => hh; rewrite /k0'; Ytac hw; last by apply:cleSS.
    exact: (cleT (proj1 hw)(cleT k2m hh)).
  have lt2: cpred (csucc m) <=c m by rewrite cpred_pr2; fprops.
  rewrite /EPperm_compat0 (wa _ lt3) (wa _ lt2).
  case: (equal_or_not k0 \0c) => kz.
    have wb: \0c <c k2.
      apply:card_ne0_pos; [ exact: (proj31 k2m)| rewrite - kz; fprops].
    rewrite /k0' kz; Ytac0; split.
      by split => // _; rewrite /EPperm_extend_aux; Ytac0; apply: rb. 
    move => k kn [_ W _ _]; apply: (q2 _ kn); split => // _. 
    by move: (W (erefl \0c)); rewrite /EPperm_extend_aux Y_true.
  case: (equal_or_not k0' \0c); last move => k0'nz.
    by rewrite /k0'; Ytac wc => tz; [ case: kz | case:(succ_nz tz) ].
  rewrite (cpred_pr2 mN).
  case: (equal_or_not k0 m) => ekm. 
    have eq1: k0' = csucc m by rewrite /k0' ekm (Y_false (cleNgt k2m)).
    have hh := cleNgt k2m.
    have lta: ~(k0 <c m) by case.
    have ltb: ~(k0' <c csucc m) by case.
    have ltc: ~ (m = k2) by rewrite - ekm; apply: nesym.
    rewrite /EPperm_extend_aux; Ytac0; Ytac0.
    split; first by split => // _ _;  move: (rc ekm kz).
    by move => k kn [_ _ W _]; apply: (q2 _ kn);split => //;move:(W eq1 k0'nz).
  have lk0m: k0 <c m by split.
  have lt4: k0' <c csucc m.
     rewrite /k0'; Ytac wb; first by apply /(cltSleP mN).
     by apply /cltSS. 
  have lt5 := (proj2 lt4).
  have k'0N:= NS_le_nat k0'm (NS_succ mN).
  have [ta tb] :=(cpred_pr k'0N k0'nz).
  have lt6: k0' <=c  m by apply /(cltSleP mN).
  have lt7:cpred k0' <=c m.  
     by move:(cleS ta);rewrite - tb => h; apply:(cleT h lt6).
  rewrite (wa _ lt7)(wa _ lt6) /EPperm_extend_aux.
  have re := (rd lk0m kz).
  case: (p_or_not_p (k0 <c k2)) => le1.
     have lt8:= (clt_ltT (cpred_lt k0N kz) le1).
     move: k0'm lt5; rewrite /k0'; Ytac0; Ytac0; Ytac0.
    split; [by split | move => k kn  [_ _ _ W]; apply: (q2 _ kn)].
    split => // _ _; exact:(W (conj k0'm lt5) kz).
  case: (cleT_ell (proj31 k2m)  (proj31 k0m)) => // lk2k0.
  move:(clt_leT lk2k0 (cleS k0N)) => [/cleNgt lt8 lt9].
  move: k0'm lt5; rewrite /k0'. 
  have lt10:=(@succ_nz k0).
  Ytac0; rewrite (cpred_pr2 k0N); Ytac0; Ytac0; Ytac0; Ytac0.
  split; [ by split| move => k kn  [_ _ _ W]; apply: (q2 _ kn) ].  
  split => // _ _ ; exact: (W(conj k0'm lt5) lt10).
move: q3 =>  [k0m rb rc rd].
have k0N:= (NS_le_nat k0m mN).
hnf; rewrite /k0' (cpred_pr2 mN) (wa _ lt3) (wa _ (cleR (CS_nat mN))).
case: (equal_or_not k0 \0c) => kz.
  have wb: \0c <c k2 by apply:(card_ne0_pos (proj31 k2m));rewrite - kz; fprops.
  rewrite /k0' kz; Ytac0; split => // _.
  by rewrite /EPperm_extend_aux; Ytac0; apply: rb. 
case: (equal_or_not k0' \0c); last move => k0'nz.
  by rewrite /k0'; Ytac wc => tz; [ case: kz | case:(succ_nz tz) ].
case: (equal_or_not k0 m) => ekm. 
  have hh := cleNgt k2m.
  have ltb: ~(k0 <c k2) by rewrite ekm.
  rewrite /EPperm_extend_aux (Y_false ltb)  (Y_false hh) - ekm; split.
  + rewrite ekm; fprops.
  + by move=> ba;case: (@succ_nz k0).
  + move => _ _; Ytac0; rewrite ekm; exact: (rc ekm kz).
  + by case.
have res :=(rd (conj k0m ekm) kz).
have [ua uv]:=(cpred_pr k0N kz).
have lta: cpred k0 <c k0 by move: (cltS ua); rewrite - uv.
have cp1: cpred (Yo (k0 <c k2) k0 (csucc k0)) <=c m.
  Ytac hh; [ exact:(cleT (proj1 lta) k0m)|  by rewrite cpred_pr2].
have cp2: (Yo (k0 <c k2) k0 (csucc k0)) <=c m.
  by Ytac hh => //; apply /(cleSltP k0N).
have [ltc ntc] := (cle_ltT k0m (cltS mN)).
rewrite (wa _ cp1) (wa _ cp2).
case: (p_or_not_p (k0 <c k2)) => le1; Ytac0. 
  have lt4:= (clt_ltT lta le1).
  by split => // _ _;  rewrite /EPperm_extend_aux; Ytac0; Ytac0.
have lt4:= (cleSS k0m).
have lt5 := (@succ_nz k0).
have lt6: csucc k0 <> csucc m.
  by move /(csucc_inj (proj31 k0m) (proj32 k0m)).
case: (cleT_ell (proj31 k2m) (proj31 k0m)) => // k2k0.
move: (clt_leT k2k0 (cleS k0N)) => [/cleNgt lt7 lt8].
split => // _ _; rewrite /EPperm_extend_aux (cpred_pr2 k0N).
by Ytac0; Ytac0; Ytac0; Ytac0. 
Qed.


Lemma EPfun_aux_bij : bijection_prop EPfun_aux Nat Nat.
Proof.
have pa :=EPfun_aux_M.
have [pb pc pd pe hv] := EPfun_aux_pr1.
move: (proj1 pb) => gh.
move:eta_like_r1 => [[[or1 tor1] _ ppa ppb ppc] _ ].
move: bij_f => [bf sf tf]; move: (proj1 (proj1 bf)) => ff.
have ih: injection EPfun_aux.
  split => // i j; rewrite pc => iN jN sv.
  have ra: inc (Vf f i) (substrate r1) by Wtac.
  have rb: inc (Vf f j) (substrate r1) by Wtac.
  case: (equal_or_not  (Vf f i) (Vf f j)) => sv2.
    move: (proj2 (proj1 bf));rewrite sf => h; exact:(h _ _ iN jN sv2).
  case: (tor1 _ _ ra rb) => rc.
      by move/(pa i j iN jN): (conj rc sv2) => [_]; rewrite sv.
    by move/(pa j i jN iN): (conj rc (nesym sv2)) => [_]; rewrite sv.
have bh: bijection EPfun_aux by split.
split => //; apply: extensionality => //. 
set E :=  Nat -s target EPfun_aux.
case: (emptyset_dichot E); [ by move/empty_setC | move => nE].
have EN: sub E Nat by apply: sub_setC. 
move:(inf_Nat EN nE); set x := intersection E.
move => [/setC_P [xN xi]] ha.
have hu: forall i, i <c x-> inc i (target EPfun_aux).
  move => i lix; ex_middle bad.
  have ie: inc i E by apply/setC_P; split => //; apply: (NS_lt_nat lix xN).
  case: (cltNge lix (ha _ ie)).
clear ha;case: xi; move: x xN hu; clear E nE EN.
move => n nN Hrec.
case (equal_or_not n \0c) => nz.
  rewrite  nz - pe;Wtac; rewrite pc; exact NS0.
set hi := Vf (inverse_fun EPfun_aux).
have bih:= (inverse_bij_fb bh).
have fih:= (proj1 (proj1 bih)).
have tih: target (inverse_fun EPfun_aux) = Nat by rewrite /inverse_fun; aw.
have sih: source (inverse_fun EPfun_aux) = target EPfun_aux
    by rewrite /inverse_fun; aw.
have hr1: forall i, i<c n -> natp (hi i) /\ Vf EPfun_aux (hi i) = i.
  move => i lin; move:(Hrec _ lin) => ra.
  split; [by rewrite /natp/hi; Wtac|  exact: (inverse_V bh ra) ].
set F := fun_image n hi.
have fsF: finite_set F by apply:finite_fun_image; apply: finite_set_nat.
have fN: sub F Nat. 
   move => t /funI_P [z /(NltP nN) zz ->].
   by rewrite - tih /hi; Wtac; rewrite sih; apply: Hrec.
have nef: nonempty F. 
  exists \0c; apply/funI_P; exists \0c. 
      apply/(NltP nN); split; first apply:cle0x; fprops. 
  rewrite - {2} pe /hi inverse_V2 // pc; apply: NS0.
move:(finite_subset_Nat fN fsF nef) => [m' /fN m'N H0].
set m := csucc m'.
have mN: natp m by apply: NS_succ.
have mz:m <> \0c by apply: succ_nz.
have mm: m' <c m by apply: cltS.
have cpm: cpred m = m' by apply: cpred_pr2.
have zm: \0c <c m by apply: succ_positive.
have mm1: inc m' m by apply/(NltP mN).
case: (p_or_not_p (exists i, i<c m /\  Vf EPfun_aux i = n)).
  move => [i [  im <-]];Wtac;rewrite pc; apply:(NS_lt_nat im  mN).
move => h.
have H: forall i, i <c m -> Vf EPfun_aux i <> n.
  by move => i im eq; case h; exists i.
have H1: forall i, natp i -> Vf EPfun_aux i <c n -> i <c m.
  move => i iN ha;apply /(cltSleP m'N);apply: H0.
  apply /funI_P; exists (Vf EPfun_aux i);first by apply /(NltP nN).
  by rewrite /hi inverse_V2 // pc.
clear F fsF fN nef H0 h.
move:(EPfun_aux_pr2 mN).
rewrite /EPpermi_prop; set hr := restriction1 _ _.
move => [fhr shr thr hrm].
move: (EPperm_recs_mon mN); set s := EPperm_rec m => sprop.
move: (sprop) => [sa sb].
move /permutationsP: (sa) => [bs sc ts]; move:(proj1 (proj1 bs)) => fs.
pose h i := Vf g (Vf EPfun_aux (Vf s i)).
have [or2 tor2]:total_order r2 by move: (eta_like_r2) =>[[]].
move: bij_g => [bg sg tg]; move: (proj1 (proj1 bg)) => fg.
have [k0 k0p]: exists k, EPperm_compat0 r2 h m k (Vf g n).
  have nsg:inc n (source g) by rewrite sg.
  have ra w: w <c m -> inc  (Vf s w)  m by move => /(NltP mN) wi;Wtac.
  have rc w: w <c m -> inc (Vf EPfun_aux (Vf s w)) (source g).
    move => / ra / NS_inc_nat wa; rewrite sg; apply: pd; Wtac.
    by rewrite pc;apply: wa.
  apply:EPperm_compat0_exists => //.
  + rewrite - tg; Wtac; rewrite sg.
  + move => w / rc wa; rewrite /h; Wtac.
    move => w wm p; move:(proj2 (proj1 bg)  _ _ (rc _ wm) nsg p).
    by apply: H; apply/(NltP  mN); apply: ra.
have k0m: k0 <=c m by move: k0p => [].
have k0N:= (NS_le_nat k0m mN).
pose f1 i := (Vf f (Vf s i)).
have qa: forall i, i <c m -> inc (f1 i) (substrate r1).
  move => i /(NltP mN) im;rewrite /f1; Wtac; rewrite sf;
  apply: (NS_inc_nat mN); Wtac.
have cpE: exists2 i, inc i Nat & EPperm_compat0 r1 f1 m k0 (Vf f i).
  by apply: EPpermi_compat0_exists.
set E := Zo Nat (fun i => EPperm_compat0 r1 f1 m k0 (Vf f i)).
have nE: nonempty E by move:cpE => [i ia ib]; exists i; apply: Zo_i.
have EN: sub E Nat by move => t /Zo_S. 
move: (inf_Nat EN nE); set k1 := intersection E.
move => [/Zo_P [k1N k1p] Ht].
have: forall k, natp k -> EPperm_compat0 r1 f1 m k0 (Vf f k) -> k1 <=c k.
  by move => k ka kb; apply: Ht; apply: Zo_i.
clear Ht; move: k1 k1N k1p; clear E cpE nE EN => k1 k1N k1p k2p.
case: (NleT_el mN k1N)=> lk1m; last first.
  have Hf1: forall i j, i <c m -> j <c m -> glt r1 (f1 i) (f1 j) -> i <c j.
    move => i j im jm gt.
    case (cleT_ell (proj31_1 im) (proj31_1 jm)) => // ha.
      by case: (proj2 gt); rewrite ha.
    move: (sb _ _ ha im) => hb; order_tac.
  move/(NltP mN):lk1m;  rewrite - ts =>  / (proj2 (proj2 bs)) [ i ia ib].
  have lim: i <c m by apply /(NltP mN); rewrite - sc.
  move: k1p;rewrite /EPperm_compat0 ib -/(f1 i); move => [_ ua ub uc].
  case: (equal_or_not k0 \0c) => kz. 
    case:(clt0 (Hf1 _ _ lim zm (ua kz))). 
  case (equal_or_not k0 m) => ekm.
    move:(ub ekm kz); rewrite cpm => ha.
    by move: (Hf1 _ _ mm lim ha) => /(cleSltP m'N) /(cltNge lim).
  move:(conj k0m ekm) => lkm; move:(uc lkm kz) => [pa1 pb1].
  have kim :=(Hf1 _ _ lim lkm pb1).
  have [q1 q2] := (cpred_pr k0N kz).
  have lpkm: cpred k0 <c m by apply/(cleSltP q1); rewrite - q2.
  by move: (Hf1 _ _ lpkm lim pa1) =>/(cleSltP q1); rewrite - q2=> /(cltNge kim).
suff: (Vf EPfun_aux k1) = n by move <-; Wtac.
pose r i := exists k, EPperm_2pos i k1 k n.
have rm: r m by exists k0;  split.
have rec: (forall i, m <=c i -> i <c k1 -> r i -> r (csucc i)).
   move => i lmi lik1 [k hk].
   have iN := (NS_lt_nat lik1 k1N).
   have inz:= (nesym (proj2 (clt_leT zm lmi))).
   case: (equal_or_not (EPperm_next_index i (EPperm_rec i)) k) => k1i.
     move:(EPperm_next_indexP iN inz (EPperm_recs_mon iN)).
     rewrite k1i => pra.
     by move: hk => [[_ tt] _]; move: (tt _ iN pra) =>/(cltNge lik1).
   move:(@ EPpermi_extension2 i k k1 n iN inz k1i hk).
   by set k2 := Yo _ _ _ => hn; exists k2.
   move:(Nat_induction3 mN k1N rm rec lk1m (cleR (proj32 lk1m))).
move => [k3 [[q1 q2] q3]].
have k1pos:= (clt_leT zm lk1m).
have k1nz:= (nesym (proj2 k1pos)).
have k0k1:= cleT k0m lk1m.
have k3v: k3 = (EPperm_next_index k1 (EPperm_rec k1)).
   move: (EPperm_next_indexP k1N k1nz (EPperm_recs_mon k1N)).
   set k4 := (EPperm_next_index k1 (EPperm_rec k1)) => praa.
  exact:(EPperm_compat_uniq  k1N (EPperm_recs_mon k1N) q1 praa).
have H1':(forall i, natp i -> Vf EPfun_aux i <c n -> i <c k1).
  by move => i iN lin; move:(clt_leT (H1 _ iN lin) lk1m).
clear sprop sa sb bs sc ts fs s h k0p f1 qa k1p k2p.
clear m mN mz mm cpm zm mm1 H H1 hr fhr shr thr hrm k0m lk1m r rm rec.
clear k0 k0N k0k1.
have fh:= (proj1 pb).
set s:= EPperm_rec k1.
pose f1 i := Vf f (Vf s i).
pose h i := Vf g (Vf EPfun_aux (Vf s i)).
move: (EPperm_recs_mon k1N) => [sa sb]; rewrite -/s in sa sb.
move /permutationsP: sa => [bs sc ts]; move:(proj1 (proj1 bs)) => fs.
have hsr: (forall i, i <c k1 -> inc (h i) (substrate r2)).
  move => i /(NltP k1N) im;rewrite /h; Wtac; rewrite sg; apply: pd; Wtac.
  rewrite pc; apply: (NS_inc_nat k1N); Wtac.
have h_M: forall i j, i <c j -> j <c k1 -> glt r2 (h i) (h j).
  move => i j lij ljm. 
  have its: inc i (source s). 
     by rewrite sc; apply/(NltP k1N); exact: (clt_ltT lij ljm).
  have jts: inc j (source s) by rewrite sc; apply/(NltP k1N).
  have fiN: inc (Vf s i) Nat by apply: (NS_inc_nat k1N); Wtac. 
  have fjN: inc (Vf s j) Nat by apply: (NS_inc_nat k1N); Wtac. 
  by apply/(pa _ _ fiN fjN); apply: sb.
have hM1: forall i j, i<c k1 -> j <c k1 ->  glt r2 (h i) (h j) -> i <c j.
  move =>  i j lim ljm [lt1 lt2].
  case: (cleT_ell (proj31_1 lim)(proj31_1 ljm)) => // cp.
    by case: lt2; rewrite cp.
   move:(h_M _ _ cp lim) => hh; order_tac.
move:(q3) => [k3m _ _ _].
have ->: Vf EPfun_aux k1 = EPpermi_fct h k1 k3.
  rewrite k3v (hv _ k1N) /EPpermi_next; Ytac0; apply:EPpermi_exten => //.
  move => i /(NltP k1N) lim;rewrite restriction1_V //.
    by rewrite pc; apply:(NS_inc_nat k1N).
  rewrite -/s; Wtac.
move: (@EPpermi_pr h k1 k3 h_M hsr k1N k3m k1nz).
set k := (EPpermi_fct h k1 k3); move => [h1 h2 h3].
ex_middle nk2n.
have lkn: k<c n by exact:(conj (h3 _  nN q3) nk2n).
move:(hr1 _ lkn) => []; set i := (hi k) => [iN iv].
have: i <c k1 by apply: H1' => //; rewrite iv.
move/(NltP k1N);rewrite -ts; move /(proj2 (proj2 bs)) =>[j js jv].
have ljm: j <c k1 by apply / (NltP k1N); rewrite - sc.
move: h2 => [_]; rewrite - iv  jv -/(h j) => ta tb tc.
case: (equal_or_not k3 \0c) =>k0z.
  by case: (clt0 (hM1 _ _ ljm k1pos (ta k0z))).
have mm:cpred k1 <c k1 by apply: cpred_lt.
have [pmN pmv]:= (cpred_pr k1N k1nz).
case: (equal_or_not k3 k1) => ekm.
    move: (hM1 _ _ mm ljm (tb ekm k0z)) => /(cleSltP pmN).
    by rewrite - pmv => /(cltNge ljm).
have lkm:=(conj k3m ekm). 
have [td te] :=(tc lkm k0z).
have jk0 :=(hM1 _ _ ljm lkm te).
have  [ka kb]:=(cpred_pr (NS_le_nat k3m k1N) k0z).
have ckm : (cpred k3) <c k1. 
   apply: cle_ltT _ lkm; rewrite {2} kb; exact(cleS ka). 
move /(cleSltP ka): (hM1 _ _ ckm ljm td). 
by rewrite - kb; move/(cltNge jk0).
Qed.

Definition EP_fun := g \co (EPfun_aux) \co  (inverse_fun f).

Lemma EP_fun_pr: order_isomorphism EP_fun r1 r2.
Proof.
have [bf sf tf] := bij_f.
have [bg sg tg] := bij_g.
have tor1: total_order r1 by move:eta_like_r1 => [[]].
have or2: order r2 by move:eta_like_r2 => [[[]]].
have sra: substrate r1 = source EP_fun by rewrite /EP_fun; aw.
have srb: substrate r2 = target EP_fun by rewrite /EP_fun; aw.
have ifb:=(inverse_bij_fb bf).
have [bh sh th] := EPfun_aux_bij.
have aa: g \coP EPfun_aux by split; try fct_tac; rewrite th.
have b1: bijection (g \co EPfun_aux) by apply:compose_fb => //.
have co1: (g \co EPfun_aux) \coP inverse_fun f.
  by split ; try fct_tac; aw; rewrite sh.
have bH:bijection EP_fun by apply: compose_fb.
apply: total_order_isomorphism => //.
rewrite - sra - tf => x y xsr ysr lexy.
have tif: target (inverse_fun f) = (source EPfun_aux) by rewrite sh; aw.
have ff:=(proj1 (proj1 ifb)).
have xsf: inc (Vf (inverse_fun f) x) (source EPfun_aux) by Wtac; aw.
have ysf: inc (Vf (inverse_fun f) y) (source EPfun_aux) by Wtac; aw.
have nx: natp (Vf (inverse_fun f) x) by rewrite /natp - sh.
have ny: natp (Vf (inverse_fun f) y) by rewrite /natp - sh.
case: (equal_or_not x y) => exy.
  by rewrite exy; order_tac; Wtac; [ fct_tac |rewrite - sra -tf].
have [//]: glt r2 (Vf EP_fun x) (Vf EP_fun y).
rewrite /EP_fun !compfV //; aw; trivial; apply /EPfun_aux_M => //.
by rewrite inverse_V // inverse_V.
Qed.

End EtaProp.

Lemma Cantor_eta_pr r1 r2: 
  eta_like r1 -> eta_like r2 -> r1 \Is r2.
Proof.
move => h1 h2.
move: (esym(proj2 h1)); rewrite aleph0_pr1 => /card_eqP  [f fp].
move: (esym(proj2 h2)); rewrite aleph0_pr1 => /card_eqP  [g gp].
move: ( EP_fun_pr fp gp h1 h2) => h.
by exists (EP_fun r1 r2 f g).
Qed.

Lemma BQ_moebius_props1  x
  (f := fun z=> z /q (\1q +q z))
  (g := fun z => z /q (\1q -q z)):
  ratp x -> 
  ((x <> \1mq -> g (f x) = x) /\ (x <> \1q -> f (g x) = x)).
Proof.
move => xq.
have pa: inc (\1q +q x) BQ by apply:(QSs QS1 xq).
split => xn1; rewrite /f/g.
  have qa: \1q +q x <> \0q.
    move => h; move: (f_equal (fun z => z +q \1mq) h).
   rewrite (BQsumC \1q) - (BQsumA xq QS1 QSm1) - {1} BQopp_1.
   by rewrite -/(_ -q _) (BQdiff_xx QS1) (BQsum_0r xq)  (BQsum_0l QSm1). 
  rewrite (BQdiff_div QS1 xq pa qa) (BQprod_1l pa).
  rewrite {2} (BQsumC \1q) (BQdiff_sum xq QS1).
  by rewrite (BQdiv_div_simp xq pa QS1 qa) BQdiv_x1.
have ha:= (QS_diff QS1 xq).
have hb: \1q -q x <> \0q.
  move /(f_equal (fun z => x +q z)).
  rewrite (BQsum_diff xq QS1) (BQsum_0r xq); fprops.
rewrite (BQsum_div QS1 xq ha hb)  (BQprod_1l ha)(BQsumC _ x). 
by rewrite (BQsum_diff xq QS1) (BQdiv_div_simp xq ha QS1 hb) BQdiv_x1.
Qed.


Lemma BQ_moebius_props2  x
  (f := fun z=> \1q /q (\1q -q z))
  (g := fun z => \1q -q  (\1q /q z)):
  ratp x -> 
  ((x <> \1q -> g (f x) = x) /\ (x <> \0q -> f (g x) = x)).
Proof.
move => xq.
have pa: ratp (\1q -q x) by apply:(QS_diff QS1 xq).
have pb: forall x, ratp x -> \1q /q x = BQinv x.
  by move => y yq; rewrite /BQdiv BQprod_1l //; apply:QS_inv.
split => xn1; rewrite /f/g.
  have hb: \1q -q x <> \0q.
    move => h; move: (f_equal (fun z => x +q z) h).
    rewrite (BQsum_diff xq QS1) BQsum_0r; fprops.
  have hc:=(QS_diff QS1 xq).
  have hd:=(QS_inv hc).
  rewrite (pb _ hc) (pb _ hd) (BQinv_K hc);apply:(BQdiff_diff_simp QS1 xq).
have pc:= (QS_div QS1 xq).
by rewrite (BQdiff_diff_simp QS1 pc) (pb _ pc) (pb _ xq) (BQinv_K xq).
Qed.

Lemma BQ_iso1: order_isomorphism 
   (Lf (fun z => z /q (\1q +q z)) BQps BQ_int01)
    BQps_order  BQ_int01_order.  
Proof.
move: BQps_or_osr BQ_int01_or_osr => [sa sb] [sc sd].
move: eta_likeQps => [[tor _ _ _ _] _].
set f := (fun z => z /q (\1q +q z)).
set g := fun z => z /q (\1q -q z).
have ha: forall u, inc u BQps -> inc (\1q +q u) BQps.
  move => u up; exact: (QpsS_sum_rl QpsS1 up).
have hb: forall u, inc u BQps -> inc (f u) BQps.
  move => u up; apply:(QpsS_div up (ha _ up)).
have hc: forall u, inc u BQps -> inc (f u)  BQ_int01.
  move => u up; move:(hb _ up) => iup. 
  apply: Zo_i; [ by apply:BQps_sBQ | split; first by apply/  qlt0xP ].
  apply /(BQprod_Mlt1 (BQps_sBQ up) (ha _ up)). 
  by rewrite BQsumC;apply:qlt_succ; apply:BQps_sBQ.
have hd: bijection (Lf f BQps BQ_int01).
  apply:lf_bijective. 
  + by move => z zp /=; apply: hc.
  + move => x y xq yq sf.
    have aux: forall z, inc z BQps -> z <> \1mq.
      move => z zp h; rewrite h in zp;exact: (BQ_di_neg_spos QmsSm1 zp).
    move: (aux _ xq)(aux _ yq) => ax ay.
    rewrite - (proj1 (BQ_moebius_props1 (BQps_sBQ xq)) ax).
    rewrite - (proj1 (BQ_moebius_props1 (BQps_sBQ yq)) ay).
    by rewrite -/(f x) -/(f y) sf. 
  + move => y /Zo_P[yq [/ qlt0xP yp yl1]];  exists (g y); last first.
      by move: (proj2 (BQ_moebius_props1 yq) (proj2 yl1)).
   by apply /QpsS_div => //; apply/  qlt0xP; apply/(qlt_diffP1 yq QS1).
apply: total_order_isomorphism; aw; trivial.
move => x y xp yp /iorder_gleP [/hc fx /hc fy /BQle_P xy]; rewrite !LfV//.
apply/iorder_gleP; split => //; apply/BQle_P.
move: (BQps_sBQ xp)(BQps_sBQ yp) => xq yq.
apply/(BQdiv_Mlelege0 xq (ha _ xp) yq (ha _ yp)).
rewrite (BQprodDl yq QS1 xq) (BQprodDr xq QS1 yq).
rewrite (BQprod_1l yq) (BQprod_1r xq). 
by apply /(BQsum_le2r xq yq (QSp xq yq)).
Qed.

Lemma BQ_iso2: order_isomorphism 
   (Lf (fun z => Yo (z <q \0q) (\1q /q (\1q -q z)) (z +q \1q)) BQ BQps)
    BQ_order BQps_order.
Proof.
move: BQor_sr BQor_tor BQps_or_osr => pa pb  [sc sd].
set f :=(fun z => Yo (z <q \0q) (\1q /q (\1q -q z)) (z +q \1q)).
have ha: forall x, ratp x -> \1q /q x = BQinv x.
    move => y yq; rewrite /BQdiv (BQprod_1l (QS_inv yq))//.
have hb: lf_axiom f BQ BQps.
  move =>x xq; rewrite /f; Ytac hc.
    have qa: inc x BQms by apply/ qgt0xP. 
    have qb :=(QpsS_sum_rl QpsS1 (BQopp_negative1 qa)).
    apply /(QpsS_div QpsS1 qb).
  case: (qleT_el QS0 xq) => // / qle0xP hd; exact: (QpsS_sum_r hd QpsS1).
have mon: forall x y, x <q y ->  f x <q f y.
  move => x y lexy; move: (lexy) => [[xq yq _] _].
  rewrite /f; Ytac hc; Ytac hd.
  + have qa: inc x BQms by apply/ qgt0xP. 
    have qb :=(QpsS_sum_rl QpsS1 (BQopp_negative1 qa)).
    have qa': inc y BQms by apply/ qgt0xP. 
    have qb' :=(QpsS_sum_rl QpsS1 (BQopp_negative1 qa')).
    have qc:= (BQps_sBQ qb').
    have qc':= (BQps_sBQ qb).
    apply /(BQdiv_Mltltge0 QS1 qb QS1 qb'); rewrite BQprod_1l// BQprod_1r //.
    by apply/(BQsum_lt2l (QSo yq) (QSo xq) QS1) / (qlt_oppP xq yq).
  + case: (qleT_el QS0 yq) => // / qle0xP  yp.
    move:(BQsum_Mp QS1 yp); rewrite BQsumC; apply:qlt_leT.
    have qa: inc x BQms by apply/ qgt0xP. 
    have qb:= (BQsum_Mps QS1 (BQopp_negative1 qa)).
    have qc:= (QpsS_sum_rl QpsS1 (BQopp_negative1 qa)).
    have qd :=(QpsS_inv qc).
    move/ BQps_iP: (qc) => [/BQp_sBQ dq dnz].
    by move: (BQprod_Mltgt0 qd qb); rewrite BQprod_inv1. 
  + by case hc; BQo_tac. 
  + by apply/(BQsum_lt2r xq yq QS1).
apply: total_order_isomorphism; aw; trivial.
  apply: lf_bijective => //.
    by move => u v uq vq lxy;case:(qleT_ell uq vq) => // /mon [_] [].
  move => y yp.
  move/ BQps_iP: (yp) => [/BQp_sBQ yq ynz].
  case: (qleT_el QS1 yq). 
     have hc: y = (y -q \1q) +q \1q by rewrite BQsumC (BQsum_diff QS1 yq).
     exists (y -q \1q); [  exact (QS_diff yq QS1) | rewrite /f; Ytac h => //].
     move /(qgt_diffP yq QS1): h => h1; BQo_tac.
   move:(proj2 (BQ_moebius_props2 yq) ynz) => hc hd.
   have he:= (QS_div QS1 yq).
   have hf:= (QS_diff QS1 he).  
   have hg: \1q -q \1q /q y <q \0q.
     apply/(qgt_diffP QS1 he).
     move:(BQprod_Mltgt0 (QpsS_inv yp) hd);rewrite BQprod_inv1 //.
   by exists (\1q -q \1q /q y) => //; rewrite /f; Ytac0.
move => x y xq yq /=; rewrite !LfV//; move/BQle_P => lxy; apply/iorder_gleP.
move: (hb _ xq) (hb _ yq) =>sa sb; split => //;apply /BQle_P. 
case: (equal_or_not x y) => eq;first by rewrite eq; apply: qleR; apply:BQps_sBQ.
by move: (mon _ _ (conj lxy eq)) => [].
Qed.

Lemma BQ_iso3 a b: inc a BQps -> ratp b -> 
    order_isomorphism (Lf (fun z => a*q z +q b) BQ BQ)
      BQ_order  BQ_order. 
Proof.
move => aps bq.
move: BQor_sr BQor_tor => pa pb; move: (proj1 pb) => pc.
move/ BQps_iP: (aps) => [ap1 anz]; move:(BQp_sBQ  ap1) => aq.
have pd: lf_axiom (fun z : Set => a *q z +q b) BQ BQ.
 by move => x xq /=; apply:QSs => //; apply:QSp.
apply: total_order_isomorphism; aw; trivial.
  apply: lf_bijective => //.
    move => u v uq vq /(BQsum_eq2r (QSp aq uq)  (QSp aq vq) bq). 
    by apply/BQprod_eq2l.
  move => y yq; move:(QS_diff yq bq)=> ybq.
  exists ((y -q b) /q a); first by apply:QS_div. 
  by rewrite BQprod_div // BQsumC BQsum_diff.
move => x y xq yq /BQle_P lexy; rewrite ! LfV//; apply/BQle_P.
apply /(BQsum_le2r (QSp aq xq) (QSp aq yq) bq).
by rewrite (BQprodC a) (BQprodC a); apply BQprod_Mlege0.
Qed.


Definition simple_interpolation n u v :=
   fun x => (v -q u) *q (x -q n) +q u.

Lemma interpolation_prop1 n u v (f := simple_interpolation n u v):
  inc n BQ -> u <q v ->
  [/\ f n = u, f (n +q \1q) = v, 
      (forall x, n <=q x -> x <=q (n +q \1q) -> 
        (u <=q f x /\ f x <=q v)),
      (forall y,  u <=q y -> y <=q v -> exists x,
       [/\ n <=q x,  x <=q (n +q \1q) & y = f x]) &
   (forall x y, x <q y -> f x <q f y)].
Proof.
move => nq lt1.
move:(lt1) => [[uq vq le1] ne1].
have qa: inc (v -q u) BQps by apply/ qlt0xP; apply/ (qlt_diffP1 uq vq).
move/BQps_iP: (qa) => [qb nuv].
move:(BQp_sBQ qb) => qc.
split.
+ rewrite /f /simple_interpolation (BQdiff_xx nq).
  by rewrite (BQprod_0r qc) (BQsum_0l).
+ rewrite /f /simple_interpolation (BQdiff_sum nq QS1).
  by rewrite (BQprod_1r qc) BQsumC BQsum_diff. 
+ move => x sa sb.
  rewrite /f /simple_interpolation.
  set y := (v -q u) *q (x -q n).
  have yp: inc y BQp.  
     by apply: QpS_prod => //; apply/ (qle_diffP nq (proj32 sa)).
  split; first by rewrite BQsumC; apply:BQsum_Mp.
  move/(BQsum_le2r (proj31 sb) (proj32 sb) (QSo nq)): sb.
  rewrite -/(_ -q _) -/(_ -q _)  (BQdiff_sum nq QS1) => ha.
  move/(BQprod_ple2r (proj31 ha) QS1 qa): ha.
  rewrite BQprodC  -/y (BQprod_1l qc) => hb.
  move/(BQsum_le2r (proj31 hb) (proj32 hb) uq): hb.
  by rewrite (BQsumC  (v -q u)) BQsum_diff.
+ move => y uy yv.
  move:(proj32 uy) => yq.
  rewrite /f /simple_interpolation.
  move /(BQsum_le2r uq yq (QSo uq)): uy. 
  rewrite -/(_ -q _) -/(_ -q _) (BQdiff_xx uq) => l2.
  move /(BQsum_le2r yq vq (QSo uq)): yv; rewrite -/(_ -q _) -/(_ -q _) => l3.
  move:(QpsS_inv qa) => /BQps_sBQp => l4.
  move: (BQprod_Mlege0 l4 l2) (BQprod_Mlege0 l4 l3). 
  rewrite (BQprod_0l (BQp_sBQ l4)) BQprod_inv1 // -/(_ /q _).
  set z := (y -q u) /q (v -q u); move => l5 l6.
  move:(proj31 l6) => zq.
  move /(BQsum_le2r (proj31 l6) (proj32 l6) nq): l6. 
  move /(BQsum_le2r QS0 (proj32 l5) nq): l5. 
  rewrite (BQsum_0l nq)(BQsumC \1q n) => l7 l8.
  exists (z +q n); split => //.
  have qd:= (proj32 l2).
  have qe: inc (BQinv (v -q u)) BQ by apply:QS_inv.
  rewrite (BQsumC z) (BQdiff_sum nq zq) /z BQprodA // -/(_ /q _).
  rewrite (BQdiv_prod qc qd nuv) BQsumC (BQsum_diff) //.
+ move => x y lxy; rewrite /f /simple_interpolation.
  move: (lxy) => [[xq yq _] _].
  move/ (BQsum_lt2r xq yq (QSo nq)): lxy => ha.
  move: (BQprod_Mltgt0 qa ha); rewrite (BQprodC)  (BQprodC _ (v -q u) ) => hd.
  by move/(BQsum_lt2r (proj31_1 hd) (proj32_1 hd) uq): hd.
Qed.

Lemma interpolation_prop2 n u v (f := simple_interpolation n u v):
  ratp n -> u <q v ->
      (forall x, n <=q x -> x <q (n +q \1q) -> 
        (u <=q f x /\ f x <q v)) /\
      (forall y,  u <=q y -> y <q v -> exists x,
       [/\ n <=q x,  x <q (n +q \1q) & y = f x]).
Proof.
move => pa pb; move:(interpolation_prop1 pa pb).
rewrite -/f; move => [qa qb qc qd qe].
split.
  move => x xa xb; move: (qc _ xa (proj1 xb)) => [sa sb]; split => //.
  by rewrite - qb; apply: qe.
move => y ya [yb yc]; move:(qd _ ya yb) => [x [xa xn yv]].
by exists x; split => //; split => //; dneg eq1; rewrite yv eq1.
Qed.


Lemma BQfloor_pos2 x (y := BQ_of_nat (P (BQfloor x))):
   inc x BQp -> y <=q x /\  x <q y +q \1q. 
Proof.
move => xp; move:(BQfloor_pos xp) => [sa sb].
by move:(BQ_floorp (BQp_sBQ xp)); rewrite sa.
Qed.

Definition multiple_interpolation f x:=
   let y :=(BQfloor x) in 
     simple_interpolation (BQ_of_Z y) (f (P y)) (f (csucc (P y))) x.

Lemma  multiple_interpolation_prop f 
   (g := multiple_interpolation  (fun z => (BQ_of_nat (f z)))):
  (forall n, natp n -> natp (f n)) ->
  (forall n, natp n -> f n <c f(csucc n)) ->
  (f \0c) = \0c ->
  [/\ forall x, inc x BQp -> inc (g x) BQp,
      (forall y, inc y BQp -> exists2 x, inc x BQp & g x = y),
      (forall n, natp n -> g (BQ_of_nat  n) = BQ_of_nat  (f n)) &
      forall x y, inc x BQp -> x <q y -> g x <q g y].
Proof.  
move => h1 h2 h3.
pose F n := (BQ_of_nat (f n)).
have pa: forall n, natp n -> 
   forall x,  (BQ_of_nat n) <=q x -> x <q ((BQ_of_nat n) +q \1q) -> 
     g x = simple_interpolation (BQ_of_nat n) (F n) (F (csucc n)) x.
  move => n nN x pa pb.
  move:(proj32 pa) => xq.
  move: (BQ_floorp2 xq (BZ_of_nat_i nN) (conj pa pb)) => e1.
  by rewrite /g /multiple_interpolation - e1 BZ_of_nat_val.
have pc: forall x, inc x BQp -> let m := (BQfloor x) in
  g x = simple_interpolation (BQ_of_nat (P m)) (F (P m)) (F (csucc (P m))) x. 
   move => x xp m.
   move: (BQfloor_pos xp) => [sa sb].
   move: (BQ_floorp (BQp_sBQ xp)); rewrite sa; move => [ma mb].
   exact:(pa _ sb _ ma mb).
have pd: forall n, natp n -> F n <q F (csucc n).
  by move => n nN; move/(qlt_cN (h1 _ nN) (h1 _ (NS_succ nN))): (h2 _ nN).
have rc:forall n, natp n -> g (BQ_of_nat n) = F n.
  move => n nN; move:(QpS_of_nat nN) => xp; move: (BQp_sBQ xp) => xq.
  have sb: P (BQfloor (BQ_of_nat n)) = n.
    by rewrite /BQ_of_nat (BQfloor_Z (BZ_of_nat_i nN))/BZ_of_nat; aw.
  move:(pc _ xp) => /=; rewrite sb; rewrite /simple_interpolation.
  have sc: ratp (F n) by apply:QS_of_nat; apply: h1.
  have sd: ratp (F (csucc n)) by apply:QS_of_nat; apply: h1; fprops.
  by rewrite (BQdiff_xx xq) (BQprod_0r (QS_diff sd sc)) (BQsum_0l).
have pf: forall x, let m := BQfloor x in inc x BQp ->
     F (P m) <=q g x /\ g x <q F (csucc (P m)).
  move => x m xp. 
  move:(BQfloor_pos  xp) (pc _ xp)=>  [sa sb] gv.
  move:(pd _ sb) (BQfloor_pos2 xp)  => sd [se sf].
  move: (interpolation_prop2 (QS_of_nat sb) sd) => [ hc _  ].
  by move: (hc _ se sf); rewrite - gv.
have ra: forall x, inc x BQp -> inc (g x) BQp.
   move => x xq; move:(proj1 (pf _ xq)); move: (proj2 (BQfloor_pos xq)) => sa.
   have: inc (F (P (BQfloor x))) BQp by  apply: QpS_of_nat;apply: h1.
  move / qle0xP => su sv; apply/ qle0xP; BQo_tac.
have pg: forall k, natp k -> 
   exists n, [/\ natp n, f n <=c k & k <c f (csucc n)].
   apply: Nat_induction. 
     exists \0c; move: (h2 _ NS0); rewrite h3 => sa; split => //; fprops.
   move => k kN [m [ma mb mc]].
   move /(cleSltP kN): mc; case: (equal_or_not (csucc k) (f (csucc m))).
     move => eq1; exists (csucc m); rewrite eq1; split => //; fprops.
   by move => sa sb; exists m; split => //; move: (cleS kN) => /(cleT mb). 
have rb: forall y, inc y BQp -> exists2 x, inc x BQp & g x = y.
   move => y yq.
   move: (BQfloor_pos2 yq) (BQfloor_pos yq) => /=; set k:= (P (BQfloor y)).
   move => [sa sb] [sc sd].
   move:(pg _ sd) => [m [mN ma mb]].
   have mc: (F m) <=q BQ_of_nat k  by apply/ qle_cN; fprops.
   have se: inc (BZ_of_nat k) BZp by apply:BZ_of_natp_i.
   have md: BQ_of_nat k +q \1q <=q BQ_of_nat (f (csucc m)).  
     by rewrite (BQ_of_nat_succ sd); apply/ qle_cN; fprops; apply/cleSltP.
   move:(qleT mc sa) (qlt_leT sb md) =>la lb.
   move: (pd _ mN) (QS_of_nat mN) => ub ua.
   move: (proj2 (interpolation_prop2 ua ub) _ la lb) => [x [xa xb yv]].
   have / qle0xP cp: inc (BQ_of_nat m) BQp by apply:QpS_of_nat.
   have xp: inc x BQp by apply/ qle0xP; BQo_tac.
   have sse: inc (BZ_of_nat m) BZ by apply:BZ_of_nat_i.
   move: (BQ_floorp2 (BQp_sBQ xp) sse (conj xa xb)) => h.
   by ex_tac; rewrite (pc _ xp) yv - h /BZ_of_nat pr1_pair.
split => //.
move => x y xp lxy; move: (proj1 lxy) => lexy.
have yp: inc y BQp by move/ qle0xP: xp => sa;apply/ qle0xP; BQo_tac.
move: (BQfloor_M lexy) =>ha.
move:(pc _ xp) (pc _ yp) (BQfloor_pos xp) => gx gy  [sa sb].
move:(pd _ sb) (BQfloor_pos2 xp)  => sd [se sf].
move: (interpolation_prop1 (QS_of_nat sb) sd) => [_ hc _ _  hd].
case: (equal_or_not (BQfloor x) (BQfloor y)) => sff.
  by move: (hd x y lxy); rewrite - gx sff - gy.
move: (hd _ _ sf);  rewrite hc - gx => eq1.
move:(BQfloor_pos yp) => [sa' sb'].
move:(pd _ sb') (BQfloor_pos2  yp) =>  sd' [se' sf'].
move: (interpolation_prop1 (QS_of_nat sb') sd') => [hb' hc' _ _  hd'].
have fmon: forall a b, natp a -> natp b ->  a <c b -> f (csucc a) <=c f b.
  move => a b aN bN lab.
  move /(cleSltP aN): lab => h; rewrite -(cdiff_pr h).
  move:(NS_diff (csucc a) bN); move:(b -c csucc a); apply: Nat_induction.
   rewrite (csum0r (CS_succ a)); fprops.
  move => n nN Hrec; apply (cleT Hrec).
  rewrite (csum_nS _ nN); exact (proj1(h2 _ (NS_sum (NS_succ aN) nN))).
have la: F (csucc (P (BQfloor x))) <=q  F (P (BQfloor y)).
  have h: BQfloor x <z BQfloor y by split.
  have qqa: natp (P (BQfloor x)) by [].
  have qqb: natp (P (BQfloor y)) by [].
  move / (qlt_cZ (proj31_1 h) (proj32_1 h)) : h.
  rewrite sa sa' => /(qlt_cN  qqa qqb) qge0x.
  apply/ qle_cN; [by  apply: h1; fprops | by apply: h1 | by  apply: fmon].
move:(qlt_leT eq1 la) => lb.
case: (equal_or_not (BQ_of_nat (P (BQfloor y))) y) => hh.
  by rewrite  gy - {4} hh hb'.
move:(hd' _ _ (conj se' hh)); rewrite hb' - gy => lc; BQo_tac.
Qed.

Lemma BQ_iso4 (E := Zo (permutations BQ) 
       (fun f => order_isomorphism f BQ_order  BQ_order)):
   cardinal E = \2c ^c aleph0.
Proof.
have cq:= cardinal_Q.
apply: cleA.
  have ibq: infinite_set BQ. 
    apply /infinite_setP; rewrite cq; apply: CIS_aleph0.
  have /sub_smaller sa: sub E  (permutations BQ) by apply: Zo_S.
  move: (cleT sa (Exercise6_5c ibq)).
  by rewrite card_setP - cpowcr cq.
move:constants_v => [c0 [c1 c2]].
have ->: \2c ^c aleph0  = cardinal (functions Nat C2).
  rewrite c2 cpow_pr1 aleph0_pr1 cpowcl //.
pose f_to_g f := induction_defined0 (fun n v  => csucc ((Vf f n) +c v)) \0c.
have ftN: forall f, inc f (functions Nat C2) -> forall n, natp n ->
     natp (Vf f n).
    move => f /functionsP [ff sf tf] n nN.
    suff: sub (target f) Nat by apply; Wtac; ue.
    rewrite tf => t /set2_P;case => ->; rewrite ? c0 ? c1 -/(natp _); fprops.
have pa: forall f, let g := (f_to_g f) in inc f (functions Nat C2) ->
    [/\ function g, Vf g \0c = \0c,
     forall n, natp n -> Vf g (csucc n) = csucc (Vf f n +c Vf g n),
     forall n, natp n -> natp  (Vf g n) & 
     forall n, natp n -> (Vf g n) <c (Vf g (csucc n))].
  move => f g H ;move:(ftN _ H) => fn.
  move:(induction_defined_pr0 (fun n v : Set => csucc (Vf f n +c v)) \0c).
  rewrite -/(f_to_g f) -/g; move => [sg [fg _] g0 gs].
   have gn: forall n, natp n -> natp (Vf g n).
     apply: Nat_induction; first by rewrite g0; fprops.
    move => n nn h; rewrite (gs _ nn);apply:NS_succ; apply:NS_sum; fprops.
  have gi //:forall n, natp n -> Vf g n <c Vf g (csucc n).
    move => n nn; rewrite (gs _ nn).
    have aux:  Vf g n <=c  (Vf f n +c Vf g n). 
      apply:csum_Mle0;exact: (CS_nat (gn _ nn)).
    apply: (cle_ltT aux); apply: cltS; apply:NS_sum; fprops.
have inj1: forall f1 f2,
   inc f1 (functions Nat C2) -> inc f2 (functions Nat C2) ->
    (forall n, natp n -> Vf (f_to_g f1) n =  Vf (f_to_g f2) n)
    -> f1 = f2.
  move => f1 f2 f1a f2a sg1g2.
  move:(pa _ f1a) (pa _ f2a)=> [qa qb qc qd qe] [ra rb rc rd re].
  move: (ftN _ f1a) (ftN _ f2a) => Ha Hb.
  move/functionsP : f1a => [ff1 sf1 tf1].
  move/functionsP : f2a => [ff2 sf2 tf2].
  apply: function_exten => //; try ue; move => n; rewrite sf1 => nN.
  move:(rc _ nN) (qc _ nN); rewrite (sg1g2 _ (NS_succ nN))  (sg1g2 _ nN).
  have sa: cardinalp (Vf f2 n +c Vf (f_to_g f2) n)by fprops.
  have sb: cardinalp (Vf f1 n +c Vf (f_to_g f2) n)by fprops.
  move: (Ha _ nN)(Hb _ nN) => na nb.
  move => -> /(csucc_inj sa sb). 
  by move/(csum_eq2r (rd _ nN) nb na).
pose mif f :=  multiple_interpolation 
   (fun z => (BQ_of_nat (Vf (f_to_g f) z))).
have pb: forall f, let g := (mif f) in  inc f (functions Nat C2) -> 
   [/\ forall x, inc x BQp -> inc (g x) BQp,
        forall y, inc y BQp -> exists2 x : Set, inc x BQp & g x = y,
        forall n, natp n -> g (BQ_of_nat n) = BQ_of_nat (Vf (f_to_g f)  n)
      & forall x y, inc x BQp -> x <q y -> g x <q g y].
  move => f g ff; move:(pa _ ff) => [qa qb qc qd qe].
  by apply:multiple_interpolation_prop.
move: BQor_sr BQor_tor => sr tor; move: (proj1 tor) => orc.
have pc: forall f, order_isomorphism f BQ_order BQ_order -> inc f E.
   move => f h; apply/Zo_P; split => //.
   move: h => [_ _ ]; rewrite sr; move => [ha hb hc] _.
   apply/Zo_P; split => //; apply/functionsP; split => //; fct_tac.
pose f_to_A f z := Yo (inc z BQp) (mif f z) z.
pose f_to_B f := Lf ( f_to_A f) BQ BQ.
have pd:forall f, inc f (functions Nat C2) -> lf_axiom (f_to_A f) BQ BQ.
  move => f ff x xQ; rewrite /f_to_A; Ytac h => //.
  by move:(pb _ ff) => [ ha _ _ _]; move: (BQp_sBQ (ha _ h)).
have pe: forall f, inc f  (functions Nat C2) ->
  forall x y, ratp x -> ratp y -> x <q y ->  f_to_A f x <q f_to_A f y.
  move => f fa x y xq yp lxy; rewrite /f_to_A.
  move:(pb _ fa) => [sa _ _ sb].
  Ytac h1; Ytac h2.
  + by apply: sb.
  + case h2; apply/ qle0xP; move/ qle0xP: h1 => xp; move:(proj1 lxy) => lxy'.
    BQo_tac.
  + move / qle0xP:(sa _ h2) => ha; case/BQ_i0P:xq  => // / qgt0xP hb; BQo_tac.
  + done.
have pf: forall f, inc f  (functions Nat C2)  ->  bijection (f_to_B f).
  move => f ff; move: (pd _ ff)(pe _ ff) => sa sb.
  move:(pb _ ff) => [_  sc _ _].
  apply:lf_bijective => //.
    move => u v uq vq eq; case: (qleT_ell uq vq) => // cp.
       by case:(proj2 (sb _ _ uq vq cp)).
       by case:(proj2 (sb _ _ vq uq cp)).
  move => y yq; case:(inc_or_not y BQp) => yp.
    move:(sc _ yp) => [x xp h]; move: (BQp_sBQ xp) => xq; exists x => //. 
    by rewrite /f_to_A; Ytac0.
  by exists y => //; rewrite /f_to_A; Ytac0.
have ax: forall f, inc f (functions Nat C2) -> (inc (f_to_B f) E).
   rewrite /f_to_B;move => f fa; move: (pf _ fa) (pd _ fa) => pea pda.
   apply: pc;apply: total_order_isomorphism; aw; trivial.
   move => x y xq yq /=; rewrite !LfV//.
   move /BQle_P => lxy; apply/BQle_P; case: (equal_or_not x y) => eqxy.
     by rewrite eqxy; apply: qleR; apply:pda.
   exact: (proj1 (pe _ fa _ _ xq yq (conj lxy eqxy))).
suff: injection (Lf f_to_B (functions Nat C2) E). 
  by move/ inj_source_smaller; aw.
apply: (lf_injective ax) => f1 f2 f1a f2a sf; apply: (inj1 _ _ f1a f2a).
move:(pb _ f1a) (pb _ f2a)  => [_ _ sa _] [_ _ sb _].
move => n nN.
have cnp: inc (BQ_of_nat n) BQp  by apply: QpS_of_nat.
move:(BQp_sBQ cnp) => cnq.
move: (pd _ f1a) (pd _ f2a) => ax1 ax2.
move: (f_equal (fun z => (Vf z (BQ_of_nat n))) sf). 
rewrite /f_to_B {1} (LfV ax1 cnq)(LfV ax2 cnq) /f_to_A {1} (Y_true cnp).
rewrite (Y_true cnp) (sa _ nN) (sb _ nN); apply: BQ_of_nat_injective.
Qed.



Definition simple_interpolation2  i u v :=
   fun z => u -q (BQ_of_nat (csucc i) *q z -q \1q) 
   *q (BQ_of_nat i) *q ( u -q v).


Lemma simple_interpolation2_pa i u v
  (yk := fun k => (BQinv (BQ_of_nat (csucc k)))) 
  (ya := yk i) (yb := yk (csucc i))
  (f := simple_interpolation2  (csucc i) u v):
  natp i -> u <q v ->
  [/\ f yb = u, f ya = v,forall z1 z2, z1 <q z2 -> f z1 <q f z2 & 
     forall a,  (f yb) <q a /\ a <q (f ya) -> 
     exists z, [/\ yb <q z, z <q ya  & a = f z]].
Proof.
move => iN lt1; move: (lt1) => [[uq vq _] _].
move/(qlt_diffP2 uq vq):lt1 => uvn.
move: (NS_succ iN) => siN; move: (NS_succ siN) => ssiN.
move:(QS_diff uq vq) => uvq.
have Ta :BQ_of_nat (csucc (csucc i)) <> \0q.
  move => /BQ_of_nat_injective; apply: succ_nz.
have Tb :BQ_of_nat (csucc i) <> \0q.
  move => /BQ_of_nat_injective; apply: succ_nz.
have Tc: ratp (BQ_of_nat (csucc i)) by apply:QS_of_nat.
have Td: ratp (BQ_of_nat (csucc (csucc i))) by apply:QS_of_nat.
have ra: f yb = u.
  rewrite /f/simple_interpolation2 /yb /yk.
  rewrite (BQprod_inv1 Td Ta)  (BQdiff_xx QS1)(BQprod_0l (QS_of_nat siN)).
  rewrite (BQprod_0l uvq); apply: (BQdiff_0r uq).
have rb: f ya = v.
 rewrite /f/simple_interpolation2 /ya /yk.
 rewrite {2} /BQdiff BQsumC (BQsum_div (QSo QS1) Td Tc Tb). 
  rewrite - (BQ_of_nat_succ (NS_succ iN)) BQopp_1 (BQprod_m1l Tc).
  rewrite BQsumC -/(_ -q _) (BQdiff_sum Tc QS1) (BQdiv_1x Tc).
  rewrite (BQprodC (BQinv _)) (BQprod_inv1 Tc Tb) (BQprod_1l uvq).
  by rewrite (BQdiff_diff  uq uq vq) (BQdiff_xx uq) (BQsum_0l vq).
have rc: forall z1 z2, z1 <q z2 -> f z1 <q f z2.
  move => z1 z2 lt1; rewrite /f /simple_interpolation2.
  move: (lt1) => [[z1q z2q _] _].
  move: (QS_diff (QSp Td z1q) QS1) (QS_diff (QSp Td z2q) QS1) => za zb.
  move: (QSp (QSp za Tc) uvq) (QSp (QSp zb Tc) uvq) => zc zd.
  apply /(BQsum_lt2l (QSo zc) (QSo zd) uq); apply :qlt_opp. 
  apply: (BQprod_Mltlt0 uvn); apply:(BQprod_Mltgt0 (BQpsS_fromN iN)).
  apply/ (BQsum_lt2r (QSp Td z1q) (QSp Td z2q) (QSo QS1)).
  rewrite BQprodC (BQprodC _ z2); apply:(BQprod_Mltgt0 (BQpsS_fromN siN) lt1).
have re: forall a,  (f yb) <q a /\ a <q (f ya) -> 
  exists z, [/\ yb <q z, z <q ya  & a = f z].
  move => a [ha hb]; move:(proj32_1 ha) => aq.
  move: ha hb; rewrite /f/simple_interpolation2.
  have sa1:= (QS_diff uq aq); have sa:= QSo sa1.
  have sb: inc (yk (csucc i)) BQ by apply: QS_inv.
  have sb': inc (yk i) BQ by apply: QS_inv.
  move: (QSp Td sb) (QSp Td sb') => sf sf'.
  move:(QS_diff sf  QS1) (QS_diff sf'  QS1) => sc sc'.
  move: (QSp sc Tc) (QSp sc' Tc) => sc1 sc1'.
  move: (QSp  sc1 uvq) (QSp sc1' uvq) => sd sd'.
  move: (QS_div sa1 uvq) => se; move:(QS_div se Tc) => se'.
  have Te:= (BQpsS_fromN iN). 
  have Tf:= (BQpsS_fromN siN). 
  have eq1 : a = u -q (u -q a) by  symmetry; apply: BQdiff_diff_simp.
  move: (BQprod_div uvq sa1 (BQms_nz uvn)); rewrite BQprodC => eq2.
  move:(BQprod_div Tc se Tb); rewrite BQprodC => eq3.
  rewrite eq1; move /(BQsum_lt2l (QSo sd) sa uq) => /(qlt_oppP sa1 sd) => lt1.
  move /(BQsum_lt2l sa (QSo sd') uq) => /(qlt_oppP sd' sa1); move: lt1.
  rewrite - eq2 - eq3; rewrite - eq3 in se.
  move/(BQprod_mlt2r sc1 se uvn) => lt1 /(BQprod_mlt2r se sc1' uvn); move: lt1.
  move/(BQprod_plt2r sc se' Te) => lt1 /(BQprod_plt2r se' sc' Te); move: lt1.
  move /(qlt_diffP4 se' sf  QS1) => lt1 /(qlt_diffP3 se' sf'  QS1); move: lt1.
  rewrite - {3} (BQdiff_sum1 QS1 se') -(BQprod_div Td (QSs se' QS1) Ta).
  rewrite ! (BQprodC (BQ_of_nat (csucc (csucc i)))).
  move/(BQprod_plt2r sb (QS_div (QSs se' QS1) Td) Tf) => lt1.
  move/(BQprod_plt2r  (QS_div (QSs se' QS1) Td) sb' Tf).
  set x3 := _ /q _; move => lt3; exists x3; rewrite (BQprodC x3); done.
done.
Qed.


Definition multiple_interpolation2 f x :=
  let n := (BZ_val (BQfloor (BQinv x))) in
  Yo (n = \0c) (x +q (f \0c) -q \1q)
    (simple_interpolation2 n (f n) (f (cpred n))  x).


Lemma multiple_interpolation_prop2 f 
   (g := multiple_interpolation2 f) 
   (Z := Zo BQ (fun z => exists2 n, natp n & f n <q z)):
  (forall n, natp n -> f (csucc n) <q f n) ->
  order_isomorphism (Lf g BQps Z)
    (induced_order BQ_order BQps) (induced_order BQ_order Z).
Proof.
move => finc.
have Ha: forall i, natp i -> inc (f i) BQ by move => i /finc/proj32_1.
have Hb: forall x, \1q <q x -> g x = (x +q (f \0c) -q \1q).
  move => x lt1;rewrite /g /multiple_interpolation2.
  have xp: inc x BQps by move/ qlt0xP: QpsS1 => h;apply / qlt0xP; BQo_tac.
  move/(BQinv_mon2 xp QpsS1): lt1 => sa.
  move: (QpsS_inv xp) => / qlt0xP [ip _]. 
  have <-: \0z = (BQfloor (BQinv x)).
    by apply: (BQ_floorp2 (proj31_1 sa) ZS0);rewrite (BQsum_0l QS1) -BQinv_1.
  by rewrite / BZ_zero /BZ_of_nat; aw; Ytac0.
have Hc: forall x, \1q <q x -> f \0c <q g x.
  have ha := (Ha _ NS0).
  move => x h; move:(proj32_1 h) => xq.
  rewrite (Hb _ h) /BQdiff (BQsum_AC xq ha (QSo QS1)).
  by rewrite BQsumC; apply/ (BQsum_Mps ha)/ qlt0xP /(qlt_diffP1 QS1 xq).
have Hd: forall a, f \0c <q a -> exists2 x, \1q <q x & a = g x.
  move => a ap;move: (ap) => [[f0q aq _] _].
  have ha: \1q <q (a +q \1q) -q f \0c.
    rewrite /BQdiff (BQsum_AC aq QS1 (QSo f0q)) BQsumC; apply/ (BQsum_Mps QS1).
    by apply / qlt0xP / qlt_diffP1.
  exists ( (a +q \1q) -q (f \0c)) => //.
  by rewrite (Hb _ ha) (BQsum_diff1 f0q (QSs aq QS1))(BQdiff_sum1 QS1 aq).
have He: forall x, \1q <q x -> inc (g x) Z.
  move => x /Hc h; apply/Zo_P;split; [ exact:(proj32_1 h) | exists \0c; fprops].
have Hf: forall x, \0q <q x -> x <=q \1q -> \1q <=q BQinv x.
  by move => x / qlt0xP ha hb; move/(BQinv_mon1 QpsS1 ha): hb; rewrite BQinv_1.
have Hg: forall x, \0q <q x -> x <=q \1q -> \1z <=z BQfloor (BQinv x).
  move => x ha hb; move:(Hf _ ha hb) => hc. 
  by rewrite - (BQfloor_Z ZS1); apply: BQfloor_M.
pose xn x := (cpred (BZ_val (BQfloor (BQinv x)))).
have xnp1: forall x, ratp x -> natp (xn x).
  by move => x xq; apply /NS_pred /BZ_valN/ZS_floor /QS_inv.
have xnp2: forall x, \0q <q x -> x <=q \1q ->
   BQfloor (BQinv x) = BZ_of_nat(csucc (xn x)).
   move => x ha hb.
   move/zlt0xP: ZpsS1 => sb; move:(zlt_leT sb (Hg x ha hb)) =>/zlt0xP. 
   rewrite /xn; set y := BQfloor (BQinv x) => sc.
   rewrite -(proj2 (cpred_pr (BZ_valN (BZps_sBZ sc)) (BZps_valnz sc))).
   by rewrite(BZp_hi_pr (BZps_sBZp sc)).
have xnp3: forall x, \0q <q x -> x <=q \1q ->
   P (BQfloor (BQinv x)) = csucc (xn x).
   by move => x ha hb; rewrite (xnp2 x ha hb) BZ_of_nat_val.
pose yk k :=  (BQinv (BQ_of_nat (csucc k))).
have ykp0: forall k, natp k -> \0q <q  (yk k).
  by move => k kN; apply / qlt0xP; apply: QpsS_inv; apply: BQpsS_fromN.
have ykp1: forall n, natp n -> yk n <=q \1q.
  move => n nN.
  rewrite - BQinv_1; apply/(BQinv_mon1(BQpsS_fromN nN) QpsS1).
  apply /(qle_cN NS1 (NS_succ nN)).
  by rewrite - succ_zero;apply:cleSS; apply:cle0n.
have ykp2: forall x, \0q <q x -> x <=q \1q -> 
   yk (csucc (xn x)) <q x /\ x <=q yk (xn x).
  move => x pa pb; move: (proj32_1 pa)=> xq;move: (xnp1 _ xq) => nN.
  move: (xnp2 x pa pb) (QS_inv xq) => pc iq.
  move/ qlt0xP: (pa) => xp.
  move:(NS_succ nN) => snN.
  have ha:= (QpsS_inv (BQpsS_fromN nN)).
  have hb:= (QpsS_inv (BQpsS_fromN snN)).
  move:(BQ_floorp iq) => []; rewrite (BQsum_cZ (ZS_floor iq) ZS1) pc.
  rewrite (BZsum_cN snN NS1) - (Nsucc_rw snN) -/(BQ_of_nat _).  
  rewrite - (BQinv_K (QS_of_nat snN)); move/(BQinv_mon1 ha xp) => le1.
  rewrite -/(BQ_of_nat _) - (BQinv_K (QS_of_nat (NS_succ snN))).
  by move/(BQinv_mon2 xp hb) => le2.
have ykp4':forall a b, natp a -> natp b -> a <c b -> yk b <q yk a.
  move => a b aN bN lab. 
  move:(BQpsS_fromN aN)(BQpsS_fromN bN) => ap bp.
  by apply/(BQinv_mon2 bp ap) /(qlt_cN (NS_succ aN) (NS_succ bN)) /cltSS.
have ykp4:forall a b, natp a -> natp b -> a <=c b -> yk b <=q yk a.
  move => a b aN bN lab.
  move:(BQpsS_fromN aN)(BQpsS_fromN bN) => ap bp.
  by apply/(BQinv_mon1 bp ap)/(qle_cN (NS_succ aN) (NS_succ bN)) /cleSS.
have ykp5: forall n x, natp n -> yk (csucc n) <q x /\ x <=q yk n ->
  [/\ \0q <q x, x <=q \1q & n = xn x].
  move => n x nN [sa sb].
  move / qlt0xP:(QpsS_inv (BQpsS_fromN (NS_succ nN))) => sc.
  move: (qlt_ltT sc sa) => sd; move:(qleT sb (ykp1 _ nN)) => se.
  split => //; move:(ykp2 _ sd se) => [sa' sb'].
  move:(qlt_leT sa sb') (qlt_leT sa' sb)(xnp1 _ (proj31 sb)) => lt1 lt2 xN.
  case:(NleT_ell nN xN) => //.
    move /(cleSltP nN) => /(ykp4 _ _ (NS_succ nN) xN) => h; BQo_tac.
  move /(cleSltP xN) => /(ykp4 _ _ (NS_succ xN) nN) => h; BQo_tac.
have ykp6: forall n, natp n -> n = xn (yk n).
  move => n nN;move: (ykp4' _ _ nN (NS_succ nN) (cltS nN)) => ha.
  exact: (proj33 (ykp5 n (yk n) nN (conj ha (qleR (proj32_1 ha))))).
have Hi: forall x, \0q <q x -> x <=q \1q ->
  g x = (simple_interpolation2 (csucc (xn x)) (f (csucc (xn x))) (f (xn x)) x).
  move => x ha hb; move: (xnp3 _ ha hb) => hc.
  rewrite /g/multiple_interpolation2 hc (Y_false (@succ_nz _)).
  by rewrite (cpred_pr1 (CS_nat (xnp1 _ (proj32_1 ha)))).
have Hj: forall n, natp n -> g (yk n) = f n.
  move => n nN; rewrite (Hi _ (ykp0 _ nN) (ykp1 _ nN))  - (ykp6 _ nN).
  by move: (simple_interpolation2_pa nN (finc _ nN)) => [_ sa  _ _].
have Hk: forall x, \0q <q x -> x <=q \1q ->
   (f (csucc (xn x)) <q g x /\ g x <=q f (xn x)).
  move => x pa pb; rewrite (Hi x pa pb).
  move: (xnp1 _ (proj32_1 pa)) => nN.
  move: (ykp2 x pa pb) => [lt1 lt2].
  move:(simple_interpolation2_pa nN (finc _ nN)).
  set A := simple_interpolation2  _ _ _; rewrite -/(yk _ ) -/(yk _ ).
  move => [r1 r2 r3 _];rewrite - r1 - r2; split; first by exact:(r3 _ _ lt1).
  case: (equal_or_not x (yk (xn x))) => eq1. 
    rewrite {1} eq1 r2; apply: (qleR (proj32_1(finc _ nN))).
  exact: (proj1 (r3 _ _ (conj lt2 eq1))).
have ra: forall x, inc x BQps -> inc (g x) Z.
  move => x xp;move / qlt0xP: (xp) => ha; move:(BQps_sBQ xp) => xq.
  case: (qleT_el xq QS1) => hb; last by apply: He.
  move: (Hk _ ha hb) => [hc _]; apply: Zo_i; first exact:(proj32_1 hc).
  exists (csucc (xn x)) => //; apply: (NS_succ (xnp1 _ xq)).
have lt01: \0q <q \1q by apply/ qlt0xP; exact:QpsS1.
have rb: forall y, inc y Z -> exists2 x, inc x BQps & y = (g x).
  move => y /Zo_P [yq [m mN hm]]. 
  case: (least_int_prop2 mN hm (p := fun t => f t <q y)).
    move/Hd => [x sa sb]; exists x => //; apply / qlt0xP; BQo_tac.
  set n := (cpred _); move => [nN l1 l2].
  case: (qleT_el yq (proj32_1 (finc _ nN))) => l3 //.
  move:( simple_interpolation2_pa nN (finc _ nN)).
  set A := simple_interpolation2 _ _ _; move => [qa qb qc qd].
  case: (equal_or_not y (f n)) => eq1.
    by rewrite eq1 - (Hj _ nN); exists (yk n) => //; apply/ qlt0xP/ykp0.
  rewrite qa qb in qd;move: (qd _ (conj l1 (conj l3 eq1))) => [z [ za zb ->]].
  move: (ykp5 _ _ nN (conj za (proj1 zb))) => [ua ub uc].
  by move:(Hi _ ua ub); rewrite - uc -/A => <-; exists z => //; apply / qlt0xP.
have fs: forall i j, i <c j -> natp j -> f j <q f i.
  move => i j h1 h2; rewrite - (cdiff_pr (proj1 h1)).
  move: (cpred_pr  (NS_diff i h2) (cdiff_nz h1)) => [sa ->].
  move:(NS_lt_nat h1 h2) => iN; move: (cpred (j -c i)) sa; clear h1 h2.
  apply:Nat_induction;first by rewrite (csum_nS _ NS0) (Nsum0r iN); apply:finc.
  move => n nN Hrec; apply:(qlt_ltT _ Hrec).
  by rewrite(csum_nS _ (NS_succ nN)); apply: (finc _ (NS_sum iN (NS_succ nN))).
have fs': forall i j, i <=c j -> natp j -> f j <=q f i.
  move => i j lt1 nj; case: (equal_or_not i j) => eq.
   rewrite eq; apply: (qleR (Ha _ nj)).
  exact: (proj1 (fs _ _ (conj lt1 eq) nj)).
have Hl: forall x, \0q <q x -> x <=q \1q -> g x <=q f \0c.
  move=> x ha hb; move:(proj2 (Hk _  ha hb)) => le1.
  move:(xnp1 _ (proj32_1 ha)) => iN.
  exact: (qleT le1 (fs' _ _ (cle0n iN) iN)).
have rc: forall x y, inc x BQps -> inc y BQps -> x <q y -> g x <q g y.
  move => x y xp yp lxy;move: (lxy) => [[xq yq _] _].
  move/ qlt0xP: (xp) => xp1; move/ qlt0xP: (yp) => yp1.
  case:(qleT_el xq QS1);case:(qleT_el yq QS1) => h1 h2.
  + have ilxy: BQinv y <q BQinv x by apply/BQinv_mon2.
    move:(xnp1 _ xq) (xnp1 _ yq) => ixN iyN.
    move:(BQfloor_M (proj1 ilxy)); rewrite (xnp2 _ yp1 h1) (xnp2 _ xp1 h2).
    move/(zle_cN (NS_succ iyN) (NS_succ ixN)).
    move /(cleSSP (CS_nat iyN) (CS_nat ixN)) => lixy.
    case: (equal_or_not (xn y) (xn x)) => eq1.
      rewrite(Hi _ xp1 h2) (Hi _ yp1 h1) eq1.
      move:(simple_interpolation2_pa ixN (finc _ ixN)) => [_ _ sa _].
      by apply: sa.
   move: (proj2 (Hk _ xp1 h2)) (proj1 (Hk _ yp1 h1)) => sa sb.
   move/(cleSltP iyN):  (conj  lixy eq1) => sc. 
   exact:(qle_ltT (qleT sa (fs' _ _ sc ixN)) sb).
  + exact:(qle_ltT (Hl _ xp1 h2) (Hc _ h1)).
  + by case: (proj2 (qlt_ltT lxy (qle_ltT h1 h2))).
  + move:(Ha _ NS0) (QSo QS1) => ha hb.
   rewrite (Hb _ h1) (Hb _ h2) /BQdiff - (BQsumA xq ha hb) - (BQsumA yq ha hb).
   by apply/(BQsum_lt2r xq yq (QSs ha hb)).
have bg: bijection (Lf g BQps Z).
  apply: lf_bijective => // u v up vp sg.
  case:(qleT_ell (BQps_sBQ up) (BQps_sBQ vp)) => // h.
    by move: (proj2 (rc _ _ up vp h)).
  by move: (nesym (proj2 (rc _ _ vp up h))).
move:BQor_or BQor_sr => or sr.
move:(BQps_sBQ); rewrite - sr => sa.
have to1:= (total_order_sub BQor_tor sa).
move: (iorder_osr or  sa) => [or1 sr1] {sa}.
have: sub Z BQ by apply:Zo_S. 
rewrite - sr => sa;move: (iorder_osr or  sa) => [or2 sr2] {sa}.
apply:total_order_isomorphism => //; [by rewrite sr1; aw | by rewrite sr2; aw | ].
aw; move => x y xp yp /=; rewrite !LfV// => /iorder_gle1 /BQle_P lxy.
apply/iorder_gle0P; [by apply: ra | by apply: ra | apply/BQle_P].
case: (equal_or_not x y) => eq1. 
  rewrite eq1; exact: (qleR (Zo_S (ra _ yp))).
exact: (proj1 (rc _ _ xp yp (conj lxy eq1))).
Qed. 

Lemma multiple_interpolation_prop3 f1 f2 
   (Zb := Zo BQ (fun z => exists2 n, natp n & f1 n <q z))
   (Za := Zo BQ (fun z => exists2 n, natp n & z <q f2 n)):
  (forall n, natp n -> f1 (csucc n) <q f1 n) ->
  (forall n, natp n -> f2 n <q f2 (csucc n)) ->
  (disjoint Za Zb) -> (Za \cup Zb = BQ) -> 
  exists2 g, order_isomorphism g
    (induced_order BQ_order (BQ -s1 \0q)) BQ_order &
   Vfs g BQps = Zb.
Proof.
move => f1d f2i  zdi zun.
move:BQor_or BQor_sr=> or sr.
have ha: sub BQps (substrate BQ_order) by rewrite sr; apply:BQps_sBQ.
move:(multiple_interpolation_prop2 f1d). 
rewrite -/Zb; set  g2 := Lf _ _ _; move => g2iso.
pose f2' n := BQopp (f2 n).
have pa':forall n, natp n -> f2' (csucc n) <q f2' n.
  by move => n nN; apply/ qlt_opp; apply: f2i.
move:(multiple_interpolation_prop2 pa') => pa; clear pa'.
move:(order_isomorphism_sincr pa); move:pa => [].
set Zb' := Zo _ _; set g1 := Lf _ _ _.
have hb': sub Zb' (substrate BQ_order) by rewrite sr; apply: Zo_S.
rewrite (iorder_sr or ha) (iorder_sr or hb') =>  or1 or2 [bijg1 sg1 tg1] _ aux.
pose g3 x := (BQopp (Vf g1 (BQopp x))).
have g3i: forall x y,  inc x BQms -> inc y BQms -> x <q y -> g3 x <q g3 y.
  move => x y /BQopp_negative1 xm /BQopp_negative1 ym lxy.
  have: glt (induced_order BQ_order BQps) (BQopp y) (BQopp x).
   by apply /iorder_gltP; split => //; apply/BQlt_P; apply/ qlt_opp. 
  by move/aux =>/iorder_gltP [_ _] /BQlt_P => h; apply/ qlt_opp. 
have fg1 :=(proj1 (proj1 bijg1)).
pose f x := Yo (x <q \0q)  (g3 x)  (Vf g2 x).
have ra: forall x, inc x BQms -> inc (g3 x) Za.
  move => x /BQopp_negative1 ;rewrite - sg1 => /(Vf_target fg1). 
  rewrite tg1 => /Zo_P [vq [n na nb]]; apply/Zo_P; split; first by apply: QSo.
  by exists n => //; move/ qlt_opp: nb; rewrite (BQopp_K (proj31_1(f2i _ na))). 
have rb: forall x, inc x BQms -> inc (f x) Za.
  by move => x xp;move / qgt0xP:(xp) => xq; rewrite /f; Ytac0; apply: ra.
move:(order_isomorphism_sincr g2iso); move:g2iso => [].
have hc: sub Zb (substrate BQ_order) by rewrite sr; apply: Zo_S.
rewrite (iorder_sr or ha) (iorder_sr or hc) => _ or3 [bijg2 sg2 tg2] _ aux2.
have fg2:=(proj1 (proj1 bijg2)).
have g2i: forall x y,  inc x BQps -> inc y BQps -> x <q y -> 
  Vf g2 x <q Vf g2 y.
  move => x y xs ys lxy.
  have: glt (induced_order BQ_order BQps) x y.
   by apply /iorder_gltP; split => //; apply/BQlt_P.
  by move/aux2 =>/iorder_gltP [_ _] /BQlt_P => h. 
clear aux aux2.
have xpnz: forall x, inc x BQps -> ~ (x <q \0q). 
  move => x xp / qgt0xP xn; case:(BQ_di_neg_spos xn xp).
have rc: forall x, inc x BQps -> inc (f x) Zb.
  move=> x xp; rewrite - tg2 /f (Y_false (xpnz _ xp));  Wtac.
have s1: sub BQps (BQ -s1 \0q).
  by move => t /BQps_iP [/BQp_sBQ tq tnz]; apply/setC1_P.
have rd: forall x, inc x  (BQ -s1 \0q) -> inc (f x) BQ.
  move => x /setC1_P [/BQ_i1P xq xnz]. 
  case: xq => //; [move/ rc | move/rb]; apply:Zo_S.
have re1:forall y, inc y Zb -> exists2 x, inc x BQps & y = f x.
  move => y; rewrite - tg2  => /(proj2 (proj2 bijg2)). 
  rewrite sg2; move => [x xi ->]; exists x => //; rewrite /f; Ytac h3 => //.
  move / qgt0xP:  h3 => h4; case: (BQ_di_neg_spos h4 xi).
have re:forall y,ratp y -> exists2 x, inc x (BQ -s1 \0q) & y = f x.
  rewrite /ratp - {1} zun => y /setU2_P; case;last first.
    by move/re1 => [x xa ->]; exists x => //;apply: s1.
  move /Zo_P => [yb [n na nb]].     
  have: inc (BQopp y) Zb'. 
    apply/Zo_i; [ by apply: QSo | by exists n => //; move/ qlt_opp: nb].
  rewrite - tg1 => /(proj2 (proj2 bijg1)); rewrite sg1;move => [x xa xb].
  move:(BQopp_positive1 xa) => xn; move/ qgt0xP: (xn) => xn1.
  move:(xn1) (BQps_sBQ xa) => [/proj31 aa oxnz] xq.
  exists  (BQopp x); first by apply/setC1_P.
  by rewrite /f (Y_true xn1) /g3 (BQopp_K xq) - xb (BQopp_K yb).
have dip: forall x y, inc x Za -> inc y Zb ->x <q y.
  move => x y /Zo_P [xq [n na nb]] yb; move:(Zo_S yb) => yq.
  case: (qleT_el yq xq) => // lxy; move: (qle_ltT lxy nb) => l1.
  rewrite /disjoint in zdi; empty_tac1 y; apply/setI2_P; split => //.
  by apply /Zo_P; split => //; exists n.
have finc: forall x y, inc x (BQ -s1 \0q) -> inc y (BQ -s1 \0q) -> x <q y ->
  f x <q f y. 
  move => x y /setC1_P [/BQ_i1P  xq xnz] /setC1_P [/BQ_i1P yq ynz] lxy.
  case: xq => // xp; case: yq => // yp.
  + by rewrite /f (Y_false (xpnz _ xp))  (Y_false (xpnz _ yp)); apply: g2i.
  + move/ qlt0xP: xp => h1;move/ qgt0xP: yp => h2.
    by case: (proj2 (qlt_ltT h2 (qlt_ltT h1 lxy))).
  + exact: (dip _ _ (rb _ xp) (rc _ yp)).
  + move/ qgt0xP: (xp) => h1;move/ qgt0xP: (yp) => h2. 
    by rewrite /f; Ytac0; Ytac0; apply: g3i.
set g := Lf f (BQ -s1 \0q) BQ.
have bg: bijection g. 
  apply: lf_bijective => // x y xp yp sf. 
  move /setC1_P:(xp) => [xq _]; move /setC1_P:(yp) => [yq _].
  case: (qleT_ell xq yq) => //; first by case/(finc _ _ xp yp).
  move/(finc _ _ yp xp) => [_ /nesym] //.
have img: Vfs g BQps = Zb.
  have fg := (proj1 (proj1 bg)).
  have sg: sub BQps (source g). 
   rewrite /g;aw;trivial => t /BQps_iP [ta tb];apply/setC1_P.
  set_extens x. 
     move/(Vf_image_P fg sg) => [u up ->]; rewrite /g LfV//; first by apply: rc.
     by move: sg; rewrite /g; aw; apply.
  move/re1=> [y ya ->]; apply/(Vf_image_P fg sg);ex_tac;rewrite /g LfV//;fprops.
exists g => //.
have s2: sub  (BQ -s1 \0q) (substrate BQ_order).
  by rewrite sr => t /setC1_P [].
have to1:= (total_order_sub BQor_tor s2).
have [or4 sr4]:= (iorder_osr or s2).
apply:total_order_isomorphism => //; rewrite /g; aw; try ue.
move => x y xs ys; rewrite !LfV// =>/iorder_gleP [_ _ /BQle_P lxy];apply/BQle_P.
case: (equal_or_not x y) => eq; first by rewrite - eq; exact:(qleR(rd _ xs)).
exact: (proj1 (finc _ _ xs ys (conj lxy eq))).
Qed.


(** * Stern Brocot sequences *)


Definition fusc_prop f:= 
  [/\ f \0c = \0c, f \1c = \1c, 
   (forall n, natp n -> f (cdouble n) =  f n) &
   (forall n, natp n -> f (csucc (cdouble n)) =  f n +c f (csucc n)) ].

Definition fusc_next F n:= 
  Yo (n = \0c) \0c (Yo (n = \1c) \1c (Yo (evenp n) (Vf F (chalf n))
   ((Vf F (chalf n)) +c (Vf F (csucc (chalf n)))))).

Definition fusc :=
  Vf (transfinite_defined Nat_order (fun u => (fusc_next u (source u)))).

Lemma fusc_pr: fusc_prop fusc.
Proof.
move:Nat_order_wor => [pa pb].
move:(transfinite_defined_pr (fun u => (fusc_next u (source u))) pa).
set F := transfinite_defined _ _;move => [[ff _] hb hc].
rewrite pb in hc hb.
have hi: forall x, natp x -> source (restriction1 F (segment Nat_order x)) = x.
  move => x xN; rewrite / restriction1; aw.
  by rewrite (segment_Nat_order1 xN).
have hc1: forall x, inc x Nat ->
       Vf F x =  fusc_next (restriction1 F (segment Nat_order x)) x.
  by move => x xn; move:(hc _ xn); rewrite (hi _ xn).
have hd: forall n, fusc n = Vf F n by done.
have he: fusc \0c = \0c by rewrite hd (hc1 _ NS0) /fusc_next; Ytac0.
have hf: fusc \1c = \1c. 
   by rewrite hd (hc1 _ NS1) /fusc_next(Y_false card1_nz); Ytac0.
have hg: forall n, natp n -> sub (segment Nat_order n) (source F).
  by move => n nN; rewrite hb => t /Zo_S; rewrite pb.
have hh: forall n m, n <c m -> natp m -> inc n (segment Nat_order m).
  move => n m lnm mN; rewrite (segment_Nat_order1 mN).
  apply/oltP;[ by move/NatP:mN => [] | by apply: oclt].
have hj:forall n, natp n -> fusc (\2c *c n) = fusc n. 
  move => n nN; move:(NS_double nN) => n2N.
  case: (equal_or_not n \0c) => nz; first by rewrite nz cprod0r.
  have [qa qc]:=(double_nz nN nz).
  have qb:= (even_double nN).
  have qe:= even_half nN.
  rewrite !hd (hc1 _ n2N) /fusc_next qe; Ytac0; Ytac0; Ytac0.
  have qf := (hh _ _  (clt_n_doublen nN nz) n2N).
  by rewrite (restriction1_V ff (hg _ n2N) qf).
split => //.
move => n nN; move:(NS_double nN) => n2N; move:(NS_succ n2N) => n3N.
case: (equal_or_not n \0c) => nz. 
  by rewrite nz cdouble0 succ_zero he hf (csum0l CS1).
have [qa qb]:=(doubleS_nz nN nz).
have qc:= (proj2 (succ_of_even (even_double nN))).
have qg: csucc n <c (csucc (\2c *c n)) by apply cltSS; apply: clt_n_doublen.
rewrite !hd (hc1 _ n3N) /fusc_next (odd_half nN); Ytac0; Ytac0; Ytac0.
rewrite  (restriction1_V ff (hg _ n3N) (hh _ _  qg n3N)).
by rewrite (restriction1_V ff (hg _ n3N) (hh _ _ (cle_ltT (cleS nN) qg) n3N)).
Qed.


Lemma fusc_unique f g: fusc_prop f -> fusc_prop g ->
   {inc Nat, f =1 g}.
Proof.
move=> [Hf1 Hf2 Hf3 Hf4][Hg1 Hg2 Hg3 Hg4].
apply: fusc_induction.
+ by rewrite Hf1 Hg1.
+ by rewrite Hf2 Hg2.
+ by move => k kN eq; rewrite (Hf3 _ kN) (Hg3 _ kN) eq.
+ by move => k kN eq1 eq2; rewrite (Hf4 _ kN) (Hg4 _ kN) eq1 eq2.
Qed.

Lemma NS_fusc n: natp n -> natp (fusc n).
Proof.
move:fusc_pr => [Ha Hb Hc Hd]; move: n.
apply: fusc_induction.
+ by rewrite Ha; fprops.
+ by rewrite Hb; fprops.
+ by move => k /Hc ->.
+ move => k /Hd ->; apply:NS_sum.
Qed.

Lemma fusc_even n: natp n -> fusc (cdouble n) = fusc n.
Proof. by move:fusc_pr => [_ _ Hc _]; apply: Hc. Qed.

Lemma fusc_odd n: natp n -> 
   fusc (csucc (cdouble n)) = fusc n +c fusc (csucc n).
Proof. by move:fusc_pr => [_ _ _]; apply. Qed.


Lemma fusc0: fusc \0c = \0c.
Proof. by move:fusc_pr => []. Qed.

Lemma fusc1: fusc \1c = \1c.
Proof. by move:fusc_pr => []. Qed.

Lemma fusc2: fusc \2c = \1c.
Proof. 
have ->: \2c = cdouble \1c by rewrite /cdouble (cprod1r CS2).
by rewrite (fusc_even NS1) fusc1.
Qed.

Lemma fusc3: fusc \3c = \2c.
Proof.
have ->: \3c = csucc (cdouble \1c) by rewrite /cdouble (cprod1r CS2).
by rewrite (fusc_odd NS1) fusc1 succ_one fusc2 csum_11.
Qed.

Lemma fusc_nz n: natp n -> n <> \0c -> (fusc n) <> \0c.
Proof.
move:fusc_pr => [Ha Hb Hc Hd]; move: n.
apply: fusc_induction. 
+ by case.
+ by rewrite Hb.
+ move => k /Hc -> pa pb.
  by apply: pa => kz; case: pb; rewrite kz cdouble0.
+ move => k /Hd ->  _ pa _ /csum_nz [_]; apply/pa; apply:succ_nz.
Qed.

Lemma fusc_nz' n: natp n -> fusc (csucc n) <> \0c.
Proof. by move => /NS_succ nn; apply: fusc_nz => //; apply: succ_nz. Qed.

Lemma fusc_pow2 n: natp n -> fusc (\2c ^c n) = \1c.
Proof.
move: n; apply: Nat_induction; first by rewrite cpowx0 fusc1.
move => n nN Hred; rewrite -(cdouble_pow2 nN).
by rewrite (fusc_even (NS_pow NS2 nN)).
Qed.

Lemma fusc_pred_pow2 n: natp n ->  fusc (\2c ^c n -c \1c) = n.
Proof.
move: n;apply: Nat_induction; first by rewrite cpowx0 cdiff_nn fusc0.
move => n nN Hr.
have pN: natp  (\2c ^c n) by fprops.
have pnz:  (\2c ^c n) <> \0c by apply: (cpow_nz card2_nz).
have [sa sb]:=(cpred_pr pN pnz).
have sc := (cpred_pr4 (CS_nat pN)).
have ->: (\2c ^c csucc n -c \1c) = csucc (cdouble (\2c ^c n -c \1c)).
  rewrite -(cdouble_pow2 nN) {1} sb - sc -/(cdouble _) (double_succ sa).
  rewrite - cpred_pr4; [rewrite cpred_pr1 //; apply: CS_succ | apply: CS_succ].
by rewrite (fusc_odd(NS_diff _ pN)) Hr - sc - sb (fusc_pow2 nN) (Nsucc_rw nN).
Qed.

Lemma fusc_succ_pow2 n: natp n -> fusc (\2c ^c n +c \1c) = csucc n.
Proof.
move: n;apply: Nat_induction. 
   by rewrite cpowx0 csum_11 fusc2 succ_zero.
move => n nN Hr.
have pN: natp  (\2c ^c n) by fprops.
rewrite -(cdouble_pow2 nN) - (Nsucc_rw (NS_double pN)) (fusc_odd pN).
by rewrite (fusc_pow2 nN)  (Nsucc_rw pN) Hr csumC - (Nsucc_rw (NS_succ nN)).
Qed.


Definition fusc_quo n:= BQ_of_nat (fusc n) /q  BQ_of_nat (fusc (csucc n)).

Lemma QpS_fusc_quo n: natp n -> inc (fusc_quo n) BQp.
Proof.
move => nN; apply:QpS_div; apply:QpS_of_nat; apply:NS_fusc; fprops.
Qed.

Lemma QS_fusc_quo n: natp n -> inc (fusc_quo n) BQ.
Proof. by move => / QpS_fusc_quo /BQp_sBQ. Qed.

Lemma QpsS_fusc_quo n: natp n -> n <> \0c -> inc (fusc_quo n) BQps. 
Proof.
move => nN nz.
move:(NS_fusc nN)(NS_fusc (NS_succ nN))(fusc_nz nN nz)(fusc_nz' nN).
by move => sa sb sc sd; apply:QpsS_div;apply:QpsS_of_nat. 
Qed.

Lemma fusc_quo_0: fusc_quo \0c = \0q.
Proof.
by rewrite /fusc_quo succ_zero fusc0 fusc1 (BQdiv_0x QS1).
Qed.

Lemma fusc_quo_1: fusc_quo \1c = \1q.
Proof.
by rewrite /fusc_quo succ_one fusc1 fusc2 (BQdiv_x1 QS1).
Qed.

Lemma fusc_quo_2: fusc_quo \2c = \2hq.
Proof.
by rewrite /fusc_quo fusc2 fusc3 - BQinv_2 (BQdiv_1x QS2).
Qed.

Lemma fusc_quo_pow2p n: natp n ->  fusc_quo (\2c ^c n -c \1c) = BQ_of_nat n.
Proof.
move => nN; rewrite /fusc_quo.
have pN: natp  (\2c ^c n) by fprops.
have pnz: (\2c ^c n) <> \0c by apply: (cpow_nz card2_nz).
rewrite (fusc_pred_pow2 nN) - (cpred_pr4 (CS_nat pN)).
by rewrite -(proj2 (cpred_pr pN pnz))(fusc_pow2 nN) (BQdiv_x1 (QS_of_nat nN)). 
Qed.

Lemma fusc_quo_pow2 n: natp n -> 
   fusc_quo (\2c ^c n) = BQinv (BQ_of_nat (csucc n)).
Proof.
move => nN; rewrite /fusc_quo.
have pN: natp  (\2c ^c n) by fprops.
rewrite (Nsucc_rw pN) (fusc_succ_pow2 nN) (fusc_pow2 nN).
by rewrite (BQdiv_1x (QS_of_nat (NS_succ nN))).
Qed.

Lemma fusc_quo_even n: natp n -> n <> \0c ->
  fusc_quo (cdouble n)  = BQinv(\1q +q BQinv (fusc_quo n)).
Proof.
move => nN nz; rewrite /fusc_quo.
rewrite (fusc_odd nN) (fusc_even nN).
move: (NS_fusc nN) (NS_fusc (NS_succ nN)) => ha hb.
move:(QS_of_nat ha) (QS_of_nat hb) => ha1 hb1.
have dnz: BQ_of_nat (fusc n) <> \0q. 
  move/(BQ_of_nat_injective); exact (fusc_nz nN nz).
rewrite (BQinv_div ha1 hb1) (BQsum_div QS1 hb1 ha1 dnz) (BQprod_1l ha1).
by rewrite (BQinv_div (QSs ha1 hb1) ha1) (BQsum_cN ha hb).
Qed.

Lemma fusc_quo_odd n: natp n ->
  fusc_quo (csucc (cdouble n)) = \1q +q (fusc_quo n).
Proof.
move => nN; rewrite /fusc_quo.
move: (NS_fusc nN) (NS_fusc (NS_succ nN)) => ha hb.
move:(QS_of_nat ha) (QS_of_nat hb) => ha1 hb1.
have dnz: BQ_of_nat (fusc (csucc n)) <> \0q. 
  move/(BQ_of_nat_injective); exact (fusc_nz' nN).
rewrite - (double_succ nN) (fusc_even (NS_succ nN)) (fusc_odd nN).
by rewrite (BQsum_div QS1 ha1 hb1 dnz) (BQprod_1l hb1) (BQsum_cN hb ha) csumC.
Qed.


Definition fusc_quo_inv x:=
   Yo (\1q <=q x) (x -q \1q)
   (Yo (\0q <q x) (BQinv (BQinv x -q \1q)) \0q).

Lemma fusc_quo_inv_props (F := fusc_quo_inv):
  [/\ (forall q, ratp q -> inc (F q) BQp),
      (forall x, inc x BQps -> x <> \1q -> inc (F x) BQps),
      (forall n, natp n -> F(fusc_quo (csucc (cdouble n))) = (fusc_quo n))
        &  (forall n, natp n -> n <> \0c ->
        F(fusc_quo (cdouble n)) = (fusc_quo n))].
Proof.
have Ha: forall x, \1q <=q x -> F x = (x -q \1q).
  by move => x sa; rewrite /F/fusc_quo_inv; Ytac0.
have Hb: forall x, \0q <q x -> x <q \1q -> F x = (BQinv (BQinv x -q \1q)).
  move => x ha hb; rewrite /F/fusc_quo_inv; Ytac0; Ytac h => //;BQo_tac.
have Hc: forall q, q <q \1q -> \0q <q q -> inc (F q) BQps.
  move => q qa qb; rewrite (Hb _ qb qa); apply:QpsS_inv.
  have qp: inc q BQps by apply / qlt0xP.
  apply/(qlt_diffP QS1 (QS_inv (proj31_1 qa))); rewrite -BQinv_1.
  by apply/(BQinv_mon2 QpsS1 qp).
split.
+ move=> q qQ; case: (qleT_el QS1 qQ) => h.
    by rewrite (Ha _ h); apply/(qle_diffP QS1 qQ).
  case: (qleT_el qQ QS0) => h1. 
    rewrite /F/fusc_quo_inv; Ytac ha; [ |Ytac hb; last apply:QpS0]; BQo_tac.
  by apply:BQps_sBQp; apply:Hc.
+ move => x / qlt0xP xp /nesym xnz; move: (proj32_1 xp) => xq.
  case: (qleT_el QS1 xq) => h; last by apply: Hc.
  by rewrite (Ha _ h); apply/(qlt_diffP QS1 xq).
+ move => n nN; move:(QpS_fusc_quo nN) => ha.
  rewrite(fusc_quo_odd nN) (Ha _ (BQsum_Mp QS1 ha)).
  by rewrite (BQdiff_sum QS1 (BQp_sBQ ha)).
+ move => n nN nz; rewrite(fusc_quo_even nN nz).
  move:(QpsS_fusc_quo nN nz) => he; move:(BQps_sBQ he)=> hf.
  have ha := (QpsS_inv he).
  have hb :=(BQsum_Mps QS1 ha).
  have hb' := (QpsS_sum_rl QpsS1 ha).  
  move/ qlt0xP: (QpsS_inv hb') => hc.
  have hd: BQinv (\1q +q BQinv (fusc_quo n)) <q \1q.
     rewrite -{2} BQinv_1; apply /(BQinv_mon2 hb' QpsS1).
     apply:(BQsum_Mps QS1 ha).
  rewrite (Hb _ hc hd) (BQinv_K (proj32_1 hb)). 
  by rewrite (BQdiff_sum QS1 (BQps_sBQ ha)) (BQinv_K hf).
Qed.

Definition fuscz n := BZ_of_nat (fusc n).

Lemma fusc_coprime n: natp n -> BZcoprime (fuscz n) (fuscz (csucc n)).
Proof.
move:fusc_pr => [Ha Hb Hc Hd]; move: n; rewrite /fuscz.
apply: fusc_induction.
+ rewrite Ha succ_zero Hb;apply:(BZ_coprime1r ZS0).
+ rewrite Hb; apply: BZ_coprime1l;apply:BZ_of_nat_i; apply:NS_fusc; fprops.
+ move => n nN.
  move:(NS_fusc nN) (NS_fusc (NS_succ nN)) => ha hb.
  move: (BZ_of_nat_i ha) (BZ_of_nat_i hb) => ha' hb'.
  rewrite (Hc _ nN) (Hd _ nN) - (BZsum_cN ha hb).
  by apply:(BZcoprime_add ha' hb').
+ move => n nN sa _.
  rewrite - (double_succ nN).
  move: (NS_fusc nN)(NS_fusc (NS_succ nN)) => ha hb.
  move: (BZ_of_nat_i ha) (BZ_of_nat_i hb) => ha' hb'.
  rewrite  (Hd _ nN)  (Hc _ (NS_succ nN)) - (BZsum_cN ha hb).
  apply:BZcoprime_sym; rewrite BZsumC; apply: (BZcoprime_add hb' ha').
  by apply:BZcoprime_sym.
Qed.

Lemma fusc_quo_numden n (q :=  fusc_quo n): natp n ->
   Qnum q = (fuscz n) /\ Qden q = (fuscz (csucc n)).
Proof.
move => nN.
move:(fusc_coprime nN).
have: inc (fuscz (csucc n)) BZps.
  apply/BZps_iP; split; first exact:(BZ_of_natp_i (NS_fusc (NS_succ nN))). 
  by move => /pr1_def; apply:fusc_nz'. 
apply: (BQdiv_numden1 (BZ_of_nat_i (NS_fusc nN))).
Qed.

Lemma fusc2_injective n m: natp n -> natp m ->
  fusc n = fusc m -> fusc (csucc n) = fusc (csucc m) -> n = m.
Proof.
wlog H: n m / n <=c m.
   move => Hrec nN mN sa sb.
   case: (NleT_ee nN mN) => h //; first by apply: Hrec.
   symmetry; apply: Hrec => //.
move:fusc_pr => [Ha Hb Hc Hd].
move => na nb; move: m nb n na H; apply: fusc_induction.
+ by move => n nN /cle0.
+ move => n nN nle1;case: (equal_or_not n \1c) => // h.
  have /cle0 mz: (n <=c \0c) by apply /(cltSleP NS0); rewrite succ_zero; split.
  by rewrite mz Ha Hb.
+ move => n nN Hrec m mN le1.
  move: (NS_half mN)(NS_half (NS_succ nN)) => hN hnN.
  move: (NS_succ hN) => shN.
  move: (NS_fusc hN)(NS_fusc shN) (NS_fusc (NS_succ nN)) => fa fb fc.
  case: (cdouble_halfV mN) => em.
    have sb:chalf m <=c n by apply /(double_monotone hN nN); rewrite - em.
    rewrite em  (Hc _ hN) (Hc _ nN) (Hd _ hN) (Hd _ nN).
    move => eq3 eq4; congr cdouble; apply: (Hrec _ hN sb eq3). 
    by apply:(csum_eq2l fa fb fc); rewrite eq4 eq3.
  rewrite em  - (double_succ hN) (Hc _ nN) (Hc _ shN) (Hd _ hN) (Hd _ nN).
  move => <-; rewrite csumC csumA  -{1} (Nsum0l fb) => eq4.
  move:(csum_eq2r fb NS0 (NS_sum fc fa) eq4) => eq5.
  by move:(proj1 (csum_nz (esym eq5))) => eq6;case: (fusc_nz' nN). 
+ move => n nN Hrec1 Hrec2 m mN le1.
  have hN:=(NS_half mN).
  rewrite - (double_succ nN) (Hd _ nN) (Hc _ (NS_succ nN)). 
  move: (NS_fusc (NS_succ hN))(NS_fusc (NS_succ nN)) (NS_fusc nN)=> fb fc fd.
  case: (cdouble_halfV mN) => em.
    rewrite em (Hc _ hN) (Hd _ hN) => ->; rewrite csumC csumA - {2} (Nsum0l fc).
      move/(csum_eq2r fc (NS_sum fb fd) NS0) => /csum_nz [ha _].
      by case: (fusc_nz' hN). 
  rewrite em - (double_succ hN) (Hc _ (NS_succ hN)) (Hd _ hN).
  move=> eq1 eq2; rewrite eq2 in eq1.
  move:(csum_eq2r fc (NS_fusc hN) fd eq1) => eq3.
  have sb: chalf m <=c n.
    have wa: cardinalp (cdouble (chalf m)) by rewrite /cdouble; fprops.
    have wb: cardinalp (cdouble n) by rewrite /cdouble; fprops.
    by apply/(double_monotone hN nN); apply/(cleSSP wa wb); rewrite - em. 
  congr (csucc (cdouble _)); apply:(Hrec1 _ hN sb eq3 eq2).
Qed.

Lemma fusc2_surjective a b: 
  natp a -> natp b -> b <> \0c -> BZcoprime (BZ_of_nat a) (BZ_of_nat b) ->
 exists n, [/\ natp n, fusc n = a & fusc (csucc n) = b].
Proof.
move => na nb.
move: fusc_pr => [Ha Hb Hc Hd].
move:(NS_sum na nb) => h; move:(cleR (CS_nat h)); move: h.
move: {1 3} (a +c b) => n nN; move: n nN a b na nb; apply:Nat_induction.
  move => a b aN bN /cle0 /csum_nz [az bz] _.
  rewrite az bz /BZcoprime (BZgcd_zero ZS0) BZabs_0 => /pr1_def h. 
  by case: card1_nz.
move => n nN Hrec a b aN bN lea bnz gcd.
move:(BZ_of_nat_i aN)(BZ_of_nat_i bN) => az bz.
case: (NleT_ell bN aN) => le1.
+  move: gcd; rewrite le1 /BZcoprime (BZgcd_id az) => h. 
   move: (f_equal P h); rewrite BZabs_val /BZ_one /BZ_of_nat; aw => a1.
   by exists \1c;rewrite succ_one fusc2 Hb; split; fprops.
+  have sa:=(cdiff_pr (proj1 le1)).
   have baN:=(NS_diff b aN).
   have le2: (a -c b) +c b <=c n. 
      rewrite csumC sa; apply/(cltSleP nN). 
      apply:(clt_leT (csum_M0lt aN bnz) lea).
   have gcd1 :BZcoprime (BZ_of_nat (a -c b)) (BZ_of_nat b).
     move:(f_equal BZ_of_nat sa); rewrite - (BZsum_cN bN baN) => /esym.
     move/(BZsum_diff_ea bz (BZ_of_nat_i baN)) => ->; apply: BZcoprime_sym.
     by apply:BZcoprime_diff => //; apply:BZcoprime_sym .
   move: (Hrec _ _  baN bN le2 bnz gcd1) => [k [kN e1 e2]].
   exists (csucc (cdouble k)); rewrite (Hd _ kN) - (double_succ kN).
   rewrite (Hc _ (NS_succ kN)) e1 e2 csumC sa; split => //.
   apply: (NS_succ (NS_double kN)).    
+ have sa := (cdiff_pr (proj1 le1)).
  case: (equal_or_not a \0c) => anz.
    move:gcd; rewrite anz /BZcoprime BZgcd_C (BZgcd_zero bz)=> h.
    move: (f_equal P h); rewrite BZabs_val /BZ_one /BZ_of_nat; aw => a1.
    exists \0c; rewrite succ_zero Ha Hb a1; split => //; apply:NS0.
  have b'nz:=(cdiff_nz le1).
  have baN:=(NS_diff a bN).
  have le2: a +c (b -c a) <=c n. 
     rewrite sa; apply/(cltSleP nN); apply:(clt_leT _ lea). 
     by rewrite csumC; apply:csum_M0lt.
  have gcd1 :BZcoprime (BZ_of_nat a) (BZ_of_nat (b -c a)).
    move:(f_equal BZ_of_nat sa); rewrite - (BZsum_cN aN baN) => /esym.
    by move/(BZsum_diff_ea az (BZ_of_nat_i baN)) => ->; apply: BZcoprime_diff.
  move: (Hrec _ _  aN baN le2 b'nz gcd1) => [k [kN e1 e2]].
  exists (cdouble k); rewrite (Hc _ kN) (Hd _ kN) e1 e2 sa; split => //.
  exact (NS_double kN).
Qed.

Lemma fusc_quo_bijection:
   bijection_prop (Lf fusc_quo Nat BQp) Nat BQp. 
Proof.
hnf; aw; split => //; apply: lf_bijective.
+ apply:QpS_fusc_quo.
+ move => u v uN vN eq.
  move: (f_equal Qnum eq)(f_equal Qden eq).
  move: (fusc_quo_numden uN) (fusc_quo_numden vN) => [-> ->] [-> ->].
  by move /pr1_def => e1 /pr1_def e2; apply:fusc2_injective.
+ move => y yp.
  move/BQ_P: (BQp_sBQ yp) => [sa sb sc sd].
  move: (BQdiv_numden (BQp_sBQ yp)) => eq0.
  move /Zo_P: yp =>[_ aap].
  set a := P (P y); set b := P (Q y).
  have aN: natp a by apply:(BZ_valN sb).
  have bN: natp b by apply:(BZ_valN (BZps_sBZ sc)).
  have bv1: (BZ_of_nat b) = (Q y) by apply:(BZp_hi_pr (BZps_sBZp sc)).
  have bnz : b <> \0c by move => h; move:(BZps_nz sc); rewrite - bv1 h.
  have av1: (BZ_of_nat a) = (P y) by apply:(BZp_hi_pr).
  rewrite - av1 - bv1 in sd eq0.
  move:(fusc2_surjective aN bN bnz sd) => [n [nN na nb]];exists n => //.
  by rewrite /fusc_quo na nb - eq0.
Qed.

Definition Fusci n a b := a *c (fusc n) +c b*c (fusc (csucc n)).  

Lemma fusci_zero a b: natp b -> Fusci \0c a b = b.
Proof.
move: fusc_pr => [Ha Hb Hc Hd] /CS_nat bN.
by rewrite  /Fusci succ_zero Ha Hb cprod0r (cprod1r bN) (csum0l bN).
Qed.

Lemma fusci_even n a b: natp n -> natp a -> natp b -> 
   Fusci (cdouble n) a b = Fusci n (a +c b) b.
Proof.
move: fusc_pr => [Ha Hb Hc Hd] nN aN bN.
by rewrite /Fusci (Hc _ nN) (Hd _ nN) cprodDl cprodDr - csumA.
Qed.

Lemma fusci_odd n a b: natp n -> natp a -> natp b -> 
   Fusci (csucc (cdouble n)) a b = Fusci n a (a +c b).
Proof.
move: fusc_pr => [Ha Hb Hc Hd] nN aN bN.
rewrite /Fusci (Hd _ nN) - (double_succ nN) (Hc _ (NS_succ nN)).
by rewrite cprodDl cprodDr - csumA.
Qed.

Lemma fusci_val n: natp n -> Fusci n \1c \0c = fusc n.
Proof.
move => nN; move:(CS_nat (NS_fusc nN)) => h.
by rewrite /Fusci cprod0l (cprod1l h) (csum0r h).
Qed.


(** Other properties *)

Lemma fusc_is_even n: natp n -> (evenp (fusc n) <-> n %%c \3c = \0c).
Proof.
move:fusc_pr => [Ha Hb Hc Hd]; move: n.
move: div3_props => [pa pb pc].
apply:fusc_induction.
+  rewrite Ha; split;[ exact | move => _; exact: even_zero].
+ rewrite Hb;split => h;first by case:(proj2 odd_one).
  by case: (card1_nz); rewrite - h pb.
+ move => k kN; rewrite (Hc _ kN) => h; apply: (iff_trans h (double_mod3 kN)).
+ move => k kN; rewrite (Hd _ kN); move: (NS_succ kN) => skN. 
  have ->: csucc (cdouble k) = k +c csucc k.
    by rewrite (csum_nS _ kN) /cdouble - csum_nn.
  move: (crem_sum NS3 card3_nz kN skN); rewrite /eqmod => ->.  
  move:(NS_fusc kN)(NS_fusc skN) => fa fb.
  case: (p_or_not_p (evenp (fusc k))) => eu sa sb.
    apply: (iff_trans (csum_of_evenP eu fb)).
    by move/sa:eu ->; rewrite (Nsum0l (NS_rem \3c skN)) (cmodmod3 skN).
  apply:(iff_trans (csum_of_oddP (conj fa eu) fb)); split; last first.
     move => ha; split; [ done | move/sb => hb;  move: ha].
     by rewrite hb (Nsum0r (NS_rem \3c kN)) (cmodmod3 kN) => /sa.
  move: (crem_sum NS3 card3_nz kN NS1); rewrite  pb - (Nsucc_rw kN) => eq1 ev.
  have H3: (\2c +c \1c) %%c \3c = \0c. 
     by rewrite -(Nsucc_rw NS2) (proj1 div3_props2).
  move:(div3_vals kN);  case => sd.
  + by case: eu; apply/sa.
  + by move: eq1; rewrite sd /eqmod => ->; rewrite csum_11 pc csumC.
  + by case: (proj2 ev); apply/sb; move:eq1; rewrite sd /eqmod H3.
Qed.

Lemma even_odd_factor b: natp b -> b <> \0c -> exists n p,
  [/\ natp n, natp p &  b = (\2c ^c n) *c csucc (cdouble p)].
Proof.
move => bN. move:(cleR (CS_nat bN)); move: b bN {- 2} b; apply: Nat_induction.
  by move => b /cle0.
move => n nN Hrec b blen bnz; case:(equal_or_not b (csucc n)) => eq; last first.
  by apply: Hrec => //; apply /(cltSleP nN).
move:(NS_succ nN) => bN; move:(NS_half bN) => hN.
case: (cdouble_halfV bN) => eq2; rewrite eq; last first.
  exists \0c, (chalf (csucc n)); split; fprops; try apply:NS_quo.
  by rewrite - eq2 cpowx0 (Nprod1l bN).
case: (equal_or_not (chalf (csucc n)) \0c) => ne1.
  by move: eq2; rewrite ne1 cdouble0 => /succ_nz.
have le1: (chalf (csucc n)) <=c n.
  apply /(cltSleP nN);rewrite {2} eq2; apply: (clt_n_doublen (NS_quo _ bN) ne1).
move: (Hrec _ le1 ne1) => [m [p [mN pN eq3]]].
exists (csucc m), p; split; fprops.
by rewrite eq2 eq3 cprodC - double_prod (cdouble_pow2 mN) cprodC.
Qed.

Lemma even_odd_factor_uniq n p n' p':
  natp n -> natp p -> natp n' -> natp p' ->
  (\2c ^c n) *c csucc (cdouble p) = (\2c ^c n') *c csucc (cdouble p') ->
  (n = n' /\ p = p').
Proof.
wlog: n p n' p'/ n <=c n'.
  move => H nN pN n'N p'N eq; case: (NleT_ee nN n'N) => h;first by apply: H.
  by symmetry in eq; move:(H _ _ _ _ h n'N p'N nN pN eq) => [sa sb].
move => nn nN pN n'N p'N.
have dN:=(NS_diff n n'N).
move:(NS_pow NS2 nN) (NS_pow NS2 dN) (NS_succ (NS_double pN))  => ha hb hc.
have hd:=(NS_succ (NS_double p'N)).
rewrite -(cdiff_pr nn) cpow_sum2 - cprodA.
move /(cprod_eq2l ha hc (NS_prod hb hd) (@cpow2_nz n)).
case: (equal_or_not (n' -c n) \0c) => eq.
  rewrite eq cpowx0 (Nprod1l hd)(Nsum0r nN).
  move/(csucc_inj (CS_nat (NS_double pN)) (CS_nat (NS_double p'N))).
  by move/(double_inj pN p'N) => ->.
move=> eq2; move:(odd_succ_double pN); rewrite eq2; move => [_]; case.
move: (cpred_pr dN eq) => [sa ->].
rewrite - (cdouble_pow2 sa) cprodC double_prod; apply: even_double; fprops.
Qed.


Lemma fusc_mean_div n p (b := (\2c ^c n) *c csucc (cdouble p))
   (a := cpred b) (c := csucc b):
   natp n -> natp p -> 
   fusc a +c fusc c = (fusc b) *c  csucc (cdouble n).
Proof.
rewrite /a /c /b => nN pN; move: n nN  {a b c}; apply: Nat_induction.
  move: (NS_double pN) => dN; move:(NS_succ dN) => sdN.
  rewrite cpowx0 (Nprod1l sdN) (cpred_pr1 (CS_nat dN)) (fusc_even pN).
  rewrite - (double_succ pN) (fusc_even (NS_succ pN))- (fusc_odd pN).
  by rewrite cdouble0 succ_zero (Nprod1r (NS_fusc sdN)).
move => n nN.
rewrite - (cdouble_pow2 nN) cprodC (cprodC (cdouble (\2c ^c n))).
rewrite double_prod; set q:= _ *c _; move => Hrec.
have dpN:= (NS_succ (NS_double pN)).
have n2N:=(NS_pow NS2 nN).
have qN:=(NS_prod dpN n2N).
have qnz: q <> \0c by apply: cprod2_nz; [ apply: succ_nz | apply:cpow2_nz].
move: (cpred_pr qN qnz); rewrite -/ q; move => [sa sb].
have sc:cardinalp (csucc (cdouble (cpred q))) by apply: CS_succ.
rewrite {1} sb (double_succ sa) (cpred_pr1 sc) (fusc_odd sa) - sb.
rewrite (fusc_even qN) (fusc_odd qN) csumA  -(csumA _ _ (fusc q)). 
rewrite csum_nn csumC csumA (csumC _ (fusc (cpred q))) Hrec. 
rewrite -(cprodC _ \2c) - cprodDr (csum_Sn _ (NS_double nN)) (Nsucc_rw nN). 
by rewrite - double_sum {4}/cdouble (Nprod1r NS2).
Qed.

Lemma fusc_mean_div1 b (a := cpred b) (c := csucc b):
  natp b -> b <> \0c ->
  exists2 n, natp n &fusc a +c fusc c = (fusc b) *c  csucc (cdouble n).
Proof.
move => pa pb.
move:(even_odd_factor pa pb) => [n [p [nN pN eq]]].
by move:(fusc_mean_div nN pN); rewrite - eq => h; exists n.
Qed.

Lemma fusc_mean_div2 b (a := cpred b) (c := csucc b):
  natp b -> b <> \0c ->
  fusc a +c fusc c = fusc b -> BZcoprime (fuscz a) (fuscz c).
Proof.
move => pa pb eq.
move:(even_odd_factor pa pb) => [n [p [nN pN eq2]]].
move:(fusc_mean_div nN pN); rewrite - eq2 eq.  
have fN:=(NS_fusc pa).
rewrite -{1} (Nprod1r fN). 
move /(cprod_eq2l fN NS1 (NS_succ (NS_double nN)) (fusc_nz pa pb)).
rewrite - succ_zero => /(csucc_inj CS0 (CS_prod2 _ _)).
rewrite - cdouble0 => /(double_inj NS0 nN) => eq3.
rewrite /a /c /fuscz eq2 - eq3 cpowx0 (Nprod1l (NS_succ (NS_double pN))).
rewrite (cpred_pr1 (CS_prod2 _ _)) (fusc_even pN) - (double_succ pN).
rewrite  (fusc_even (NS_succ pN)); apply:(fusc_coprime pN).
Qed.


(* palindrome *)

Lemma fusc_palindrome n a b (p := \2c ^c n): natp n ->
   p <=c a -> a <=c cdouble p -> p <=c b -> b <=c cdouble p ->
   a +c b = \3c *c p -> fusc a = fusc b.
Proof.
move: fusc_pr => [Ha Hb Hc Hd].
rewrite /p; clear p;move => nN; move: n nN a b; apply: Nat_induction.
  move => a b; rewrite cpowx0 /cdouble (cprod1r CS2) (cprod1r (CS_nat NS3)).
  move => ha hb hc hd he.
  have ->: fusc a =  \1c.
    case: (equal_or_not a \2c) => ca2; first by rewrite ca2 fusc2.
    case/clt2: (conj hb ca2); last by move => ->.
    by move => az; case: card1_nz; apply:cle0; rewrite - az.
  have -> //: fusc b = \1c.
    case: (equal_or_not b \2c) => cb2; first by rewrite cb2 fusc2.
    case/clt2: (conj hd cb2); last by move => ->.
    by move => bz; case: card1_nz; apply:cle0; rewrite - bz.
move => n nN Hrec a b.
rewrite -(cdouble_pow2 nN); set p := (\2c ^c n); rewrite -/p in Hrec.
rewrite -/(cdouble _) => pa pb pc pd pe.
have pN: natp p by apply:(NS_pow NS2 nN).
have p2N := (NS_double pN).
have p4N :=(NS_double p2N).
have aN:= (NS_le_nat pb p4N).
have bN:= (NS_le_nat pd p4N).
move: (NS_half aN)(NS_half bN) => haN hbN.
rewrite double_prod in pe.
case: (cdouble_halfV aN) => ea.
  case: (cdouble_halfV bN) => eb.
    rewrite ea eb; rewrite (Hc _ haN) (Hc _ hbN); apply: Hrec.
    + by apply/(double_monotone pN haN); rewrite - ea.
    + by apply/(double_monotone haN p2N); rewrite - ea.
    + by apply/(double_monotone pN hbN); rewrite - eb.
    + by apply/(double_monotone hbN p2N); rewrite - eb.
      move: pe; rewrite {1} ea {1} eb double_sum.
      apply/(double_inj (NS_sum haN hbN) (NS_prod NS3 pN)).
  have ha: natp (cdouble (chalf b)) by apply: NS_double.
  move:pe; rewrite {1} ea {1} eb (csum_nS _ ha) double_sum => h.
  move:(even_double (NS_sum haN hbN)) (even_double(NS_prod NS3 pN)) => sa sb.
  by move: (succ_of_even sa); rewrite h; case => [_].
case: (cdouble_halfV bN) => eb.
  have ha: natp (cdouble (chalf a)) by apply: NS_double.
  move:pe; rewrite {1} ea {1} eb (csum_Sn _ ha) double_sum => h.
  move:(even_double (NS_sum haN hbN)) (even_double(NS_prod NS3 pN)) => sa sb.
  by move:(succ_of_even sa); rewrite h; case => [_].
rewrite ea eb (Hd _ haN) (Hd _ hbN).
rewrite ea in pa pb.
rewrite eb in pc pd.
have h1:=(double_le_odd1 haN pN pa).
have h2:=(double_le_odd1 hbN pN pc).
have h3:=(double_le_odd2 haN p2N pb).
have h4:=(double_le_odd2 hbN p2N pd).
have bN': natp (csucc (cdouble (chalf b))) by ue.
have aN':= (NS_double haN).
have e1: chalf a +c csucc (chalf b) = \3c *c p.
  apply:( double_inj (NS_sum haN (NS_succ hbN)) (NS_prod NS3 pN)).
  rewrite - double_sum (double_succ hbN) (csum_nS _ bN') - eb.
  by rewrite - (csum_Sn _ aN') - ea pe.
rewrite - (Hrec _ _ h1 (cleT (cleS haN) h3) (cleT h2 (cleS hbN)) h4 e1).
move: e1; rewrite (csum_nS _ hbN) - (csum_Sn _ haN) => e1.
by rewrite(Hrec _ _ (cleT h1 (cleS haN)) h3 h2 (cleT (cleS hbN) h4) e1) csumC.
Qed.

Lemma fusc_kpow2n k n : natp n -> natp k -> fusc (\2c ^c n *c k) = fusc k.
Proof.
move => nN kN; move: n nN; apply: Nat_induction.
  by rewrite cpowx0 (cprod1l (CS_nat kN)).
move => n nN Hrec. 
rewrite (cpow_succ _ nN) (cprodC _ \2c) - cprodA fusc_even;fprops.
Qed.

Lemma fusc_col_progression i j: natp i -> natp j -> j <=c \2c ^c i ->
  fusc(\2c ^c (csucc i) +c j) = fusc(\2c ^c i +c j) +c fusc j.
Proof.
move: fusc_pr => [Ha Hb Hc Hd].
move => iN; move: i iN j; apply: Nat_induction.
  move => j jN; rewrite succ_zero cpowx0 (cpowx1 CS2).
  move/(cltSleP NS1); rewrite succ_one => /clt2; case => ->.
    by rewrite  (csum0r CS2)(csum0r CS1) fusc2 Ha Hb (csum0r CS1).
  by rewrite - (Nsucc_rw NS2) - (cprod1r CS2) (Hd _ NS1) csumC (Nsucc_rw NS1).
move => n nN Hrec j jN le1.
have hjN:=(NS_half jN).
have snN:=(NS_succ nN).
move: le1; rewrite -(cdouble_pow2 nN) - (cdouble_pow2 snN).
case: (cdouble_halfV jN) => eq1; rewrite eq1 => le1.
  have na: natp (\2c ^c csucc n +c chalf j) by fprops.
  have nb: natp (\2c ^c n +c chalf j) by fprops.
  rewrite (Hc _ hjN) double_sum double_sum {1} (Hc _ na) (Hc _ nb).
  apply: (Hrec _ hjN (cprod_le2l NS2 hjN (NS_pow NS2 nN) card2_nz le1)).
have ha:=(NS_double hjN).
have hb:natp (\2c ^c csucc n +c chalf j) by fprops.
have hc: natp (\2c ^c n +c chalf j) by fprops.
rewrite !(csum_nS _ ha) !double_sum.
rewrite {1} (Hd _ hb) (Hd _ hc) (Hd _ hjN) - ! (csum_nS _ hjN).
have lt1:csucc (chalf j) <=c \2c ^c n.
  apply /(cleSltP hjN); move/(cleSltP ha): le1.
  apply:(cprod_lt2l NS2 hjN (NS_pow NS2 nN)).
have lt2:chalf j <=c \2c ^c n by move:(cleT (cleS hjN) lt1).
rewrite (Hrec _ hjN lt2) (Hrec _ (NS_succ hjN) lt1);rewrite - 2! csumA. 
by apply: f_equal; rewrite csumA csumA (csumC (fusc (chalf j))).
Qed.

Lemma fusc_bound1 n k: natp n -> k <=c \2c ^c n -> fusc k <=c Fib (csucc n). 
Proof.
move: n k.
suff: forall n, natp n -> 
   (forall k,  k <=c \2c ^c n -> fusc k <=c Fib (csucc n))
   /\ (forall k, k <=c \2c ^c (csucc n) -> fusc k <=c Fib (csucc (csucc n))).
  move => H n k ha hb; exact:(proj1 (H n ha) k hb).
apply: Nat_induction.
  have H:forall k, k <c \2c -> fusc k <=c \1c.
    move => k /clt2; case => ->; rewrite ?fusc0 ?fusc1; fprops; apply: cle_01.
  rewrite succ_zero succ_one cpowx0 (cpowx1 CS2) Fib1 Fib2; split.
    by move => k /(cltSleP NS1); rewrite  succ_one; apply:H.
  move => k ke; case: (equal_or_not k \2c) => k2;last by apply:H.
  by rewrite k2 fusc2; fprops.
move => n nN [Hr1 Hr2]; split => // k ka. 
move:(NS_succ nN) => snN;move:(NS_succ snN) => ssnN.
move:(NS_pow NS2 ssnN) (NS_pow NS2 snN)=> pN p1N.
have kN:=(NS_le_nat ka pN).
have hN:=(NS_half kN).
rewrite (Fib_rec snN).
case: (cdouble_halfV kN) => sa.
  move: ka; rewrite sa - (cdouble_pow2 snN) (fusc_even hN).
  move/(double_monotone hN p1N) /Hr2 => h; apply: (cleT h). 
  apply:(Nsum_Mle0 _ (NS_Fib ssnN)).
move: ka; rewrite {2} sa (fusc_odd hN)  - (cdouble_pow2 snN) {1} sa.
move/(double_le_odd2 hN p1N) => sb; move:(cleT (cleS hN) sb) => sc.
move: (Hr2 _ sb) (Hr2 _ sc) => le1 le2.
have hhN:=(NS_half hN).
case: (cdouble_halfV hN) => ww.
  move: sc; rewrite {1 2} ww (fusc_even hhN) - (cdouble_pow2 nN).
  move/(double_monotone hhN (NS_pow NS2 nN)) /Hr1 => sd.
  exact: (csum_Mlele sd le1).
move: sc; rewrite {1 3} ww - (double_succ hhN) - (cdouble_pow2 nN).
move/(double_le_odd2  hhN (NS_pow NS2 nN)) /Hr1 => sd.
rewrite csumC (fusc_even (NS_succ hhN)); exact: (csum_Mlele sd le2).
Qed.

Definition Fib_fusc_rec :=
 induction_term  (fun _ v => (J (csucc (cdouble (Q v))) (P v +c Q v)))
   (J \0c \0c).

Definition Fib_fusc n := P ( Fib_fusc_rec n).

Lemma Fib_fusc_rec0: Fib_fusc_rec \0c = (J \0c \0c).
Proof. apply:induction_term0. Qed.

Lemma Fib_fusc_recS n (v := Fib_fusc_rec n) (a := P v) (b := Q v) :
   natp n ->  Fib_fusc_rec (csucc n) = J (csucc (cdouble b)) (a +c b).
Proof. apply:induction_terms. Qed.

Lemma Fib_fusc_rec1: Fib_fusc_rec (csucc \0c) = (J \1c \0c).
Proof. 
rewrite (Fib_fusc_recS NS0) Fib_fusc_rec0 pr2_pair cdouble0 succ_zero.
by rewrite pr1_pair (csum0r CS0).
Qed.

Lemma NS_Fib_fusc_rec n (v := Fib_fusc_rec n) (a := P v) (b := Q v): natp n ->
  [/\ (pairp v), natp a & natp b].
Proof.
rewrite /a /b/v; move: n {a b v}; apply:Nat_induction. 
   rewrite Fib_fusc_rec0; aw; split; fprops.
move => n nN [_ pa pb]; rewrite (Fib_fusc_recS nN) pr1_pair pr2_pair.
by split; fprops; apply:NS_succ;apply: NS_double.
Qed.

Lemma Fib_fusc_rec_eo n
  (a := P (Fib_fusc_rec n)) (b := Q (Fib_fusc_rec n)) 
  (a' := P (Fib_fusc_rec (csucc n))) (b' := Q (Fib_fusc_rec (csucc n))):
  natp n ->
  ((evenp n -> b' = cdouble a /\ (csucc b') = a')
  /\ (oddp n -> b' = a'/\  (csucc b') = cdouble a)).
Proof.
rewrite /a /b/a'/b'; move: n {a b a' b'}; apply:Nat_induction. 
  rewrite Fib_fusc_rec0  Fib_fusc_rec1; aw; split. 
    by rewrite /cdouble succ_zero cprod0r.
  by move => [_];move: even_zero.
move => n nN.
rewrite(Fib_fusc_recS (NS_succ nN)); move: (NS_Fib_fusc_rec (NS_succ nN)).
set a := (P (Fib_fusc_rec n)); set a' := (P (Fib_fusc_rec(csucc n))).
set b := (Q (Fib_fusc_rec n)); set b' := (Q (Fib_fusc_rec(csucc n))).
rewrite !pr1_pair !pr2_pair; move => [_ a'N b'N].
case: (p_or_not_p (evenp n)) => eon.
  move => [Ha _]; move:(Ha eon)(succ_of_even eon) => [e1 e2] seon.
  rewrite - e2  (csum_Sn _ b'N) csum_nn (double_succ b'N).
  by split => //; move:(proj2 seon).
move: (conj nN eon) => on.
move => [_ Hb]; move:(Hb on)(succ_of_odd on) => [sa sb] esn.
by rewrite sa csum_nn; split => //; case.
Qed.

Lemma Fib_fusc_rec_frec n (F := fun k => (fusc (Fib_fusc k))) : natp n ->
  F (csucc (csucc n)) = F (csucc n) +c  F n.
Proof.
move => nN; rewrite /F /Fib_fusc.
rewrite (Fib_fusc_recS (NS_succ nN)); aw.
move:(Fib_fusc_rec_eo nN)(NS_Fib_fusc_rec (NS_succ nN)) (NS_Fib_fusc_rec nN).
set b :=  Q _; set a := P _; set a' := P _.
move => [ce co] [_ a'N bN][_ aN _].
rewrite (fusc_odd bN); case: (p_or_not_p (evenp n)) => en.
   by move:(ce en) => [{2} -> ->]; rewrite (fusc_even aN) csumC.
by move:(co (conj nN en)) => [{2} -> ->]; rewrite (fusc_even aN).
Qed.


Lemma Fib_fusc_val n: natp n -> (fusc (Fib_fusc n)) = Fib n.
Proof.
move: n.
suff: forall n, natp n -> (fusc (Fib_fusc n)) = Fib n /\
   (fusc (Fib_fusc (csucc n))) = Fib (csucc n).
  by move => H n nN; move:(H _ nN) => [].
apply: Nat_induction.
  rewrite /Fib_fusc Fib_fusc_rec0 Fib_fusc_rec1; aw. 
  by rewrite succ_zero Fib0 Fib1 fusc0 fusc1.
by move => n nN [sa sb]; rewrite(Fib_fusc_rec_frec nN) sb sa (Fib_rec nN) csumC.
Qed.

Lemma Fib_fusc_bound n (p := \2c ^c n) (v := Fib_fusc (csucc (csucc n))):
   natp n -> (p <=c v /\ v <=c (cdouble p)).
Proof.
rewrite /p/v;move: n {p v}.
suff: forall n, natp n -> let v := Fib_fusc_rec (csucc(csucc n)) in
    let p := \2c ^c n in
      [/\ p <=c (P v), p <=c (Q v) , P v <=c (cdouble p) & Q v <c (cdouble p)].
  by move => H n nN; move: (H n nN) => [pa pb pc pd].
apply: Nat_induction.
   move:clt_12 cle_12 => ha hb.
   have cs11:= CS1.
   rewrite /= (Fib_fusc_recS (NS_succ NS0)) Fib_fusc_rec1; aw.
   rewrite (csum0r CS1).
   rewrite cdouble0 cpowx0 succ_zero /cdouble (cprod1r CS2);split; fprops.
move => n nN /=.
have ssN:= (NS_succ (NS_succ nN)).
rewrite (Fib_fusc_recS ssN).
set a := P (Fib_fusc_rec (csucc (csucc n))).
set b := Q (Fib_fusc_rec (csucc (csucc n))).
rewrite pr1_pair pr2_pair; move => [ha hb hc hd]. 
have cN:= (NS_pow NS2 nN); have c2N:= NS_double cN.
have bN:=(NS_lt_nat hd c2N).
move: (csum_Mlele ha hb); rewrite csum_nn - (cdouble_pow2 nN) => r2.
move /(double_monotone cN bN): (hb) => le1.
have r1:=(cleT le1 (cleS (NS_double bN))).
move:(csum_Mlelt c2N hc hd);rewrite csum_nn => r4.
by move/(double_monotone2 bN c2N): hd; move /(cleSltP (NS_double bN)) => r3.
Qed.

(* sum of 1/si.si+1: *)


Lemma fusc_rec_spec n i (q := \2c ^c  n)(p := cdouble q) : 
  natp n -> i <c q ->
   fusc i *c fusc(csucc p +c i) +c \1c = 
    fusc (csucc i) *c fusc(p +c i).
Proof.
rewrite /p / q => nN lip {p q}.
have iN:= (NS_lt_nat lip (NS_pow NS2 nN)).
move: n nN i iN lip; apply: Nat_induction. 
  rewrite cpowx0 => i _ /clt1 ->. 
  rewrite fusc0 cprod0l (csum0l CS1) /cdouble (Nprod1r NS2).
  by rewrite  (csum0r CS2)  (succ_zero) fusc1 fusc2 (cprod1r CS1).
move => n nN Hrec i iN.
move: (NS_half iN);set k := (chalf i) => kN.
have ha: natp (\2c ^c csucc n +c k) by fprops.
have hb: natp (cdouble (\2c ^c csucc n)) by rewrite/cdouble;fprops.
have hc: natp (cdouble (\2c ^c n)) by rewrite /cdouble;fprops.
case: (cdouble_halfV iN) => ->  lkn; rewrite -/k.
  rewrite (fusc_even kN) (fusc_odd kN) double_sum (fusc_even ha).
  rewrite (csum_Sn _ hb) double_sum (fusc_odd ha) cprodDl cprodDr - csumA.
  congr (_ +c _); rewrite - (cdouble_pow2 nN) - (csum_Sn _ hc).
  apply: (Hrec _ kN); apply /(double_monotone2 kN (NS_pow NS2 nN)).
  by rewrite (cdouble_pow2 nN). 
rewrite (fusc_odd kN) - (double_succ kN) (fusc_even (NS_succ kN)).
rewrite (csum_Sn _ hb) (csum_nS _ (NS_double kN)) double_sum -(double_succ ha).
rewrite (fusc_even (NS_succ ha)) (fusc_odd ha).
rewrite  cprodDl cprodDr (csumC  _ \1c) csumA; apply:f_equal2; last exact.
rewrite csumC.
move: lkn; rewrite - (cdouble_pow2 nN) - (csum_Sn _ hc) => lkn.
apply: (Hrec k kN); apply /double_monotone3; fprops.
Qed.

Definition fsimpl_sum p i := 
  qsum (fun j => BQinv (BQ_of_nat (fusc (p +c j) *c fusc (p +c (csucc j))))) i.

Lemma fusc_rec_spec1 n i (q := \2c ^c  n)(p := cdouble q) : 
  natp n -> i <=c q ->
  fsimpl_sum p i = BQdiv (BQ_of_nat (fusc i)) (BQ_of_nat (fusc (p +c i))).
Proof.
move => nN lin; rewrite /fsimpl_sum.
have qN: natp q by exact:(NS_pow NS2 nN).
have pN: natp p by exact:(NS_double qN).
have iN:=(NS_le_nat lin qN).
move: i iN lin; apply: Nat_induction.
  move => _; rewrite qsum0 fusc0 BQdiv_0x //; apply: QS_of_nat.
  exact:(NS_fusc (NS_sum pN NS0)).
move => i iN Hrec lt1.
have piN := (NS_sum pN iN).
rewrite (qsum_rec _ iN) (Hrec (cleT (cleS iN) lt1)).
move/(cleSltP iN): lt1 => lt1.
move: (NS_fusc piN) (NS_fusc (NS_sum pN (NS_succ iN))).
set a := fusc _; set b := fusc _ => aN bN.
move: (QS_of_nat aN)(QS_of_nat bN);set a' := BQ_of_nat a; set b' :=BQ_of_nat b.
move: (NS_fusc iN) => siN; move:(QS_of_nat siN) => cq aq bq.
move: (NS_fusc (NS_succ iN)) => kiN;  move:(QS_of_nat kiN) => kiq.
have anz: a' <> \0q.
  move/(BQ_of_nat_injective); apply: (fusc_nz (NS_sum pN iN)) => /csum_nz.
  by move: (double_nz qN (@cpow2_nz n)) => [ha _] [].
have bnz: b' <> \0q.
  by move/(BQ_of_nat_injective); rewrite /b (csum_nS _ iN); apply: (fusc_nz'). 
move:(QS_inv aq) (QS_inv bq) => iaq ibq.
rewrite (BQprod_cN aN bN).
rewrite (BQsum_div (QS_inv (QSp aq bq)) cq aq anz) (BQprod_inv aq bq).
rewrite BQprodC (BQprodA aq iaq ibq) (BQprod_inv1 aq anz).
rewrite BQsumC (BQsum_div cq QS1 bq bnz) - (BQprod_cN siN bN).
rewrite (BQsum_cN (NS_prod siN bN) NS1). 
rewrite /b  (csum_nS _ iN) - (csum_Sn _ pN) (fusc_rec_spec nN lt1).
rewrite (BQprod_cN kiN aN) /BQdiv;rewrite - (BQprodA(QSp kiq aq) ibq iaq).
rewrite (BQprod_ACA kiq aq ibq iaq) (BQprod_inv1 aq anz).
by rewrite (BQprod_1r (QSp kiq ibq)).
Qed.

Lemma fusc_rec_spec2 n (q := \2c ^c  n)(p := cdouble q) : 
  natp n ->fsimpl_sum p q =  \2hq.
Proof.
move => nN.
rewrite (fusc_rec_spec1 nN (cleR (CS_pow \2c n))).
rewrite (fusc_pow2 nN) /cdouble cprodC - (cprod_via_sum _ CS2).
by rewrite (fusc_kpow2n nN NS3) fusc3 - BQinv_2 (BQdiv_1x QS2).
Qed.


Lemma fusc_sum_simpl n (p := \2c ^c  n):
  natp n -> fsimpl_sum p p = \1q.
Proof.
move => nN; case: (equal_or_not n \0c) => nz.
  set a := (BQ_of_nat (fusc (\1c +c \0c) *c fusc (\1c +c csucc \0c))).
  have aux: BQinv a = \1q.
    rewrite /a succ_zero (Nsum0r NS1) csum_11 fusc1 fusc2.
    by rewrite (cprod1r  CS1) BQinv_1.
   rewrite /p nz cpowx0 /fsimpl_sum qsum1 aux //; apply: QS1.
move: (cpred_pr nN nz) => [sa sb].
rewrite /p sb - (cdouble_pow2 sa); set q:= (\2c ^c cpred n).
have qN: natp q by apply: (NS_pow NS2 sa).
have pv: p = cdouble q by rewrite /p sb cdouble_pow2.
have qq: q +c q = p by rewrite csum_nn -/(cdouble q) - pv. 
have pN: natp p by apply: (NS_pow NS2 nN).
have ha: forall i, i <c q +c q -> inc
   (BQinv (BQ_of_nat (fusc (p +c i) *c fusc (p +c csucc i)))) BQ.
  rewrite qq => i lin; move:(NS_lt_nat lin pN) => h.
  apply:QS_inv; apply: QS_of_nat; apply: NS_prod; apply:NS_fusc; fprops.
have hb: forall i, i <c q -> inc  (BQinv (BQ_of_nat
         (fusc (p +c (q +c i)) *c fusc (p +c csucc (q +c i))))) BQ.
  move => i iq; move: (NS_lt_nat iq qN) => iN;  apply:QS_inv; apply: QS_of_nat.
  apply: NS_prod; apply:NS_fusc; fprops.
rewrite - pv - {2} qq /fsimpl_sum (qsum_An qN qN ha).
rewrite -{1} /(fsimpl_sum _ _) {1} pv (fusc_rec_spec2 sa) (qsum_rev qN hb).
set w := qsum _ _.
suff: w = \2hq by  move => ->; exact BQdouble_half2.
rewrite -  (fusc_rec_spec2 sa); apply: (qsum_exten qN) => i iq.
have sd: q <=c p by rewrite - qq; apply:(Nsum_M0le _ qN).
have leip := (cleT (proj1 iq) sd).
have iN:=(NS_lt_nat iq qN);move/(cleSltP iN): iq => iq.
have se := (cleT iq sd).
rewrite (csumC q) -(cdiffA2 qN qN iq) qq cprodC. 
rewrite (csum_nS p (NS_diff (csucc i) pN)) -/ q - pv.
have sc: natp (p +c (p -c csucc i)) by apply:(NS_sum); fprops.
have rf: p <=c  (p +c (p -c csucc i)).
  apply: (Nsum_M0le (p -c csucc i) pN).
have ra: p <=c csucc (p +c (p -c csucc i)) by apply: (cleT rf (cleS sc)).
have rb: csucc (p +c (p -c csucc i)) <=c cdouble p.
  apply /(cleSltP sc);rewrite /cdouble - csum_nn; apply:(csum_Meqlt pN).
  apply:(cdiff_Mlt pN pN se (csum_M0lt pN (@succ_nz i))).
have rc: \2c ^c n <=c p +c i by apply:csum_M0le; fprops.
have rd:  p +c i <=c cdouble p.
  rewrite  /cdouble - csum_nn; apply:(csum_Meqle _ leip).
have rj: (p +c (p -c csucc i)) +c (p +c (csucc i)) = \3c *c p.
  rewrite (csumC _ (csucc i)) csumA - (csumA p) (csumC _ (csucc i)) cdiff_pr //.
  by rewrite/  card_three csum_nn cprodC - (cprod_nS _ NS2) cprodC.
have re: csucc (p +c (p -c csucc i)) +c (p +c i) = \3c *c p.
  rewrite (csum_Sn _ sc) - (csum_nS _ (NS_sum pN iN)) - (csum_nS _ iN) rj //.
have rg: (p +c (p -c csucc i)) <=c cdouble p by apply: (cleT (cleS sc) rb).
have rh: \2c ^c n <=c p +c (csucc i) by apply:csum_M0le; fprops.
have ri:  p +c (csucc i) <=c cdouble p.
  rewrite  /cdouble - csum_nn; apply:(csum_Meqle) => //.
rewrite (fusc_palindrome nN ra rb rc rd re).
by rewrite (fusc_palindrome nN rf rg rh ri rj).
Qed.


Lemma qsum_fusc1 n (p := \2c ^c  n) : natp n ->
 qsum (fun i => fusc_quo ( (cdouble p)  +c (cdouble i))) p =
  BQhalf (BQ_of_nat p).
Proof.
move => nN; case: (equal_or_not n \0c) => nz.
  have eq: (fusc_quo (cdouble \1c +c cdouble \0c)) = \2hq.
    by rewrite cdouble0 /cdouble (cprod1r CS2) (csum0r CS2) fusc_quo_2.
  by rewrite /p nz cpowx0 /BQhalf (BQprod_1l QSh2) qsum1 eq //; apply: QSh2.
move:(cpred_pr nN nz) => [sa sb].
set q := \2c ^c (cpred n).
have pv: p = cdouble q by rewrite /p sb cdouble_pow2.
have pN: natp p by apply: (NS_pow NS2 nN).
have qN: natp q by apply: (NS_pow NS2 sa).
have tnz: BQ_of_nat \2c <> \0q by move /BQ_of_nat_injective; fprops.
have ha:forall i, i <c q +c q -> inc (fusc_quo (cdouble (p +c i))) BQ.
  move => i iq; move:(NS_double(NS_sum pN (NS_lt_nat iq (NS_sum qN qN)))) => h.
  exact (QS_fusc_quo h).
have hb: forall i, i <c q -> inc (fusc_quo (cdouble (p +c (q +c i)))) BQ.
  move => i iq; move:(NS_double(NS_sum pN (NS_sum qN(NS_lt_nat iq qN)))) => h.
  exact (QS_fusc_quo h).
transitivity (qsum (fun i => fusc_quo (cdouble (p +c i))) p).
  by apply:(qsum_exten pN) => i lip; rewrite double_sum.
have hc: forall i, i <c q -> inc (fusc_quo (cdouble (p +c i))) BQ.
  by move => i iq; apply: ha; apply: (clt_leT iq); apply: csum_M0le; fprops.
have hd: forall i, i<c q ->
   inc (fusc_quo (cdouble (p +c (q +c (q -c csucc i))))) BQ.
  move => i iq;move: (NS_sum pN (NS_sum qN (NS_diff (csucc i) qN))) => h.
  exact (QS_fusc_quo (NS_double h)).
rewrite {2 3} pv BQhalf_prop (BQprod_cN NS2 qN) {2} /cdouble - csum_nn.
rewrite (BQdiv_prod (QS_of_nat NS2)  (QS_of_nat qN) tnz) (qsum_An qN qN ha).
rewrite [X in _ +q X] (qsum_rev qN hb) (qsum_sum qN hc hd); apply:(qsum_one qN).
move => i liq.
have iN:=(NS_lt_nat liq qN).
have pa:= (NS_sum pN iN).
have qq: q +c q = p by rewrite csum_nn -/(cdouble q) - pv. 
have ra: p <=c p +c i by apply: csum_M0le; fprops.
have ra' :=(cleT ra (cleS pa)).
have sd: q <=c p by rewrite - qq; apply:(csum_M0le _ (CS_nat qN)).
have leip := (cleT (proj1 liq) sd).
move/(cleSltP iN): liq => iq.
have se := (cleT iq sd).
rewrite (csumC q) -(cdiffA2 qN qN iq) qq.
have sc: natp (p +c (p -c csucc i)) by apply:(NS_sum); fprops.
have rb': csucc (p +c i) <=c cdouble p.
  by rewrite  /cdouble - csum_nn - (csum_nS _ iN); apply:(csum_Meqle). 
have rb:= (cleT (cleS pa) rb').
have rc: p <=c csucc (p +c (p -c csucc i)).
   by apply: cleT (cleS sc);apply: csum_M0le; fprops.
have rc': p <=c  (p +c (p -c csucc i))  by apply: csum_M0le; fprops.
have rd: csucc (p +c (p -c csucc i)) <=c cdouble p.
  apply /(cleSltP sc);rewrite /cdouble - csum_nn; apply:(csum_Meqlt pN).
  apply:(cdiff_Mlt pN pN se (csum_M0lt pN (@succ_nz i))).
have rd':= cleT (cleS sc) rd.
have rj: (p +c (p -c csucc i)) +c (p +c (csucc i)) = \3c *c p.
  rewrite (csumC _ (csucc i)) csumA - (csumA p) (csumC _ (csucc i)) cdiff_pr //.
  by rewrite/  card_three csum_nn cprodC - (cprod_nS _ NS2) cprodC.
have re: (p +c i) +c csucc (p +c (p -c csucc i)) = \3c *c p.
  by rewrite csumC(csum_Sn _ sc) -(csum_nS _ (NS_sum pN iN)) -(csum_nS _ iN) rj.
have re': csucc (p +c i) +c (p +c (p -c csucc i)) = \3c *c \2c ^c n.
  by rewrite csumC - (csum_nS _ iN).
rewrite /fusc_quo (fusc_even pa)(fusc_odd pa)(fusc_even sc)(fusc_odd sc).
rewrite -(fusc_palindrome nN ra rb rc rd re).
rewrite -(fusc_palindrome nN ra' rb' rc' rd' re') (csumC _ (fusc (p +c i))).
have ua: natp (fusc (p +c i)) by apply:NS_fusc.
have ub: natp (fusc (csucc (p +c i))) by apply:NS_fusc; apply: NS_succ.
rewrite - (BQsum_cN ua ub).
set a := BQ_of_nat _; set b := BQ_of_nat _.
have aq: ratp a by apply:QS_of_nat.
have bq: ratp b by apply:QS_of_nat.
rewrite /BQdiv - (BQprodDl (QS_inv (QSs aq bq)) aq bq).
apply: (BQdiv_xx (QSs aq bq)); rewrite /a/b (BQsum_cN ua ub)  - (fusc_odd pa).
move/BQ_of_nat_injective; apply: (fusc_nz' (NS_double pa)).
Qed.

Lemma qsum_fusc n (p := \2c ^c  n) : natp n ->
 qsum (fun i => fusc_quo (p +c i)) p = 
   BQhalf (BQ_of_nat (cpred (\3c *c p))).
Proof.
rewrite /p; clear p; move:n; apply: Nat_induction.
  have eq: (fusc_quo (\1c +c \0c))  = \1q by rewrite (csum0r CS1) fusc_quo_1.
  rewrite cpowx0 qsum1 eq; last by apply:QS1.
  symmetry;rewrite (Nprod1r NS3) (cpred_pr1 CS2) /BQhalf - BQinv_2.
  apply: (BQprod_inv1 QS2 BQ2_nz).
move => n nN Hrec.
have pa :=  (NS_pow NS2 nN).
have pb := NS_double pa.
rewrite - (cdouble_pow2 nN) (qsum_even_odd pa); last first.
  move => i iN; exact:(QS_fusc_quo (NS_sum pb (NS_lt_nat iN pb))).
rewrite {1} (qsum_fusc1 nN).
set a := qsum _ _.
have pN:= NS_pow NS2 nN.
set b := (BQ_of_nat (\2c ^c n)).
have bq: ratp b by apply:(QS_of_nat pN).
set d :=  \3c *c \2c ^c n.
have dN: natp d by apply: (NS_prod NS3 pN).
have dnz: d <> \0c by apply: cprod2_nz; [ apply: succ_nz | apply: cpow2_nz].
have [cN pdv]:=(cpred_pr dN dnz).
have cq:=(QS_of_nat cN).
suff: a = b +q BQhalf(BQ_of_nat (cpred (\3c *c \2c ^c n))).
  have ha: BQhalf (\2q *q b) = b by apply: BQhalf_double.
  move => ->; rewrite - {2} ha /BQhalf - (BQprodDl QSh2 (QSp QS2 bq) cq).
  rewrite - (BQprodDl QSh2 bq (QSs (QSp QS2 bq) cq)); f_equal.
  rewrite (BQsumA bq (QSp QS2 bq) cq) /b -(BQprod_cN NS2 pN). 
  rewrite (BQsum_cN pN (NS_double pN)) csumC /cdouble cprodC.
  rewrite - (cprod_via_sum _ CS2) cprodC (BQsum_cN (NS_prod NS3 pN) cN) cprodA.
  rewrite (cprodC _ \2c) - csum_nn -/d {4} pdv (csum_nS d cN). 
  rewrite cpred_pr1; fprops.
pose c1 (x:Set) := \1q. 
have c1p: (forall i, i <c (\2c ^c n) -> c1 i = \1q) by [].
have c1r: rat_below c1 (\2c ^c n) by move => i _; apply: QS1.
have cs: rat_below (fun i => fusc_quo (\2c ^c n +c i)) (\2c ^c n).
  move => i lin /=;move:(NS_sum pN (NS_lt_nat lin pN)) => h.
  exact:(QS_fusc_quo h).
rewrite - Hrec /b -(qsum_one pN c1p) (qsum_sum pN c1r cs).
apply: (qsum_exten pN) => i lin.
have iN:=NS_lt_nat lin pN.
have siN:= (NS_sum pN iN).
have ssiN:= (NS_succ siN).
have ha:=(QS_of_nat (NS_fusc siN)).
have hb:=(QS_of_nat (NS_fusc (NS_succ siN))).
have hc: BQ_of_nat (fusc (csucc (\2c ^c n +c i))) <> \0q.
  by move/BQ_of_nat_injective; apply: fusc_nz'.
rewrite (csum_nS _ (NS_double iN)) double_sum /fusc_quo /c1. 
rewrite (fusc_odd siN) -(double_succ siN) (fusc_even ssiN) csumC.
by rewrite (BQsum_div QS1 ha hb hc) (BQprod_1l hb) BQsum_cN //;apply:NS_fusc.
Qed.

(* -- *)

Definition expansion_ext f k:= expansion f \3c k.
Definition expansion_ext_of f k a :=
  expansion_ext f k /\ expansion_value f \2c = a.
Definition expansion_ext_normal_of f k a :=
  expansion_ext_of f k a /\ exp_boundary f k.
Definition expansion_ext_of_a f a := 
  expansion_ext_normal_of f (cardinal (domain f)) a.
Definition expansions_ext_of n := 
   Zo (sub_fgraphs Nat \3c) (fun z => (expansion_ext_of_a z n)).
Definition Nbexp n := cardinal (expansions_ext_of n).

Lemma expe_p1 f k: expansion_ext f k -> inc f (sub_fgraphs Nat \3c).
Proof.
move => [ pa pb pc [pd pe pf]].
apply /sub_fgraphsP; exists k; first by apply:NS_inc_nat.
apply/gfunctions_P2; split => // t /(range_gP pd) [x xdf ->].
by apply/(NltP NS3); apply: pf.
Qed.

Lemma expe_p2 f n: (expansion_ext_of_a f n) -> inc f (sub_fgraphs Nat \3c).
Proof. by move => [[h _] _]; apply: (expe_p1 h). Qed.

Lemma expe_p3 f n: expansion_ext_of_a f n -> inc f (expansions_ext_of n).
Proof. move => ha;apply/Zo_P; split => //; apply: (expe_p2 ha). Qed.

Lemma expe_bounded1 f k a: 
  natp k -> expansion_ext_normal_of f (csucc k) a ->
   (\2c ^c k) <=c a.
Proof.
move => kN [[[ pa pb pc [pd pe pf]] pg] ph].
case: ph; [ by move:(@succ_nz k) | rewrite (cpred_pr2 kN) => ph ].
have kdf: inc k (domain f) by rewrite pe; apply: Nsucc_i.
have aux:= (NS_lt_nat (pf _ kdf) NS3).
pose h i := (Vg f i) *c (\2c ^c i).
have le1: \2c ^c k <=c h k.
  rewrite /h cprodC; apply:(Nprod_M1le (NS_pow NS2 kN) (proj2 ph)).
rewrite - pg  /expansion_value pe  (induction_on_sum h kN).
apply:(cleT le1);apply /csum_Mle0; exact (proj32 le1).
Qed.

Lemma expe_bounded2 n f: natp n -> inc f (expansions_ext_of n)  ->
  cardinal (domain f) <=c n.
Proof.
move => nN /Zo_hi. 
rewrite / expansion_ext_of_a; set k:=  (cardinal (domain f)); move => ha.
move:(ha) => [[e1 e2] _].
move:e1 => [pa pb pc [pd pe pf]].
case: (equal_or_not k \0c) => knz; first by rewrite knz; exact(cle0n nN).
move: ha; move:(cpred_pr pb knz) => [sa ->].
move/(expe_bounded1 sa) => hb.
by move:(clt_leT (cantor (CS_nat sa)) hb); move/(cleSltP sa).
Qed.

Lemma expe_0 : Nbexp \0c = \1c.
Proof.
rewrite /Nbexp.
suff: (expansions_ext_of \0c) = singleton emptyset.
  by move => ->; rewrite cardinal_set1.
apply:set1_pr.
  move: NS0 NS3 => ra rb.
  have ha:fgraph emptyset by apply: fgraph_set0. 
  have hb:domain emptyset = emptyset by rewrite domain_set0.
  have hc:range emptyset = emptyset by rewrite range_set0.
  have hd:expansion_value emptyset \2c = \0c.
   by rewrite /expansion_value /csumb; aw; rewrite csum_trivial//;aw.
  have lt1: \1c <c \3c. 
   rewrite - succ_zero; apply/(cltSSP CS0 CS2); apply: clt_02.  
  have he: cardinal (domain emptyset) = \0c by rewrite hb cardinal_set0.
  have hf: expansion_ext_of emptyset (cardinal (domain emptyset)) \0c.
    hnf; rewrite he;split => //; split => //; rewrite hb. 
    by split => // u /in_set0.
  apply/ Zo_P; split; last by split => //; left.
  apply/sub_fgraphsP; exists emptyset; fprops; apply/gfunctions_P2.
  split => //; rewrite hc; fprops. 
move => z za; move:(expe_bounded2 NS0 za) => /cle0 /card_nonempty.
by move /domain_set0_P. 
Qed.


Lemma expe_nat n: natp n -> natp (Nbexp n).
Proof.
move => h.
apply /card_finite_setP.
pose Ek k := gfunctions k \3c.
have fi: finite_set (Nintc n) by apply: finite_Nintcc. 
have:finite_set (unionb (Lg (Nintc n) Ek)).
  apply:finite_union_finite; rewrite /allf;aw;trivial  => k ki; rewrite LgV//.
  have kN:=(Nint_S ki).
  rewrite /finite_set.
  have ->: (cardinal (Ek k)) = cardinal (functions  k \3c).
    by rewrite -/(cpow _ _) cpow_pr0.
  apply/NatP;apply: (NS_pow NS3 kN).
suff: sub (expansions_ext_of n) (unionb (Lg (Nintc n) Ek)).
  apply/ sub_finite_set.
move => f fa; apply/setUb_P;aw; move: (expe_bounded2 h fa) => hb.
have hc:inc (cardinal (domain f)) (Nintc n) by move /(NintcP h):hb.
move: (Zo_hi fa) => [[[qa qb qc [qd qe qf]] _] _]. 
exists (cardinal (domain f)) => //; rewrite LgV//; apply/gfunctions_P2; split => //.
by move => t /(range_gP qd) [x xdf ->]; apply/(NltP NS3);  apply: qf.
Qed.

Lemma NS_expe_val f k: expansion_ext f k -> natp (expansion_value f \2c).
Proof.
move =>[bN kN b2 [fgf df vf]]; apply: finite_sum_finite. 
hnf; rewrite /allf; aw; split.
  move=> i idf; rewrite LgV//; rewrite df in vf idf; move: (vf _ idf) => h.
  apply:(NS_prod  (NS_lt_nat h bN) (NS_pow NS2 (NS_inc_nat kN idf))).
by rewrite df; apply: finite_set_nat.
Qed.


Definition expansion_ext_aug f i (k := (cardinal (domain f))):=
   Lg (csucc k) (fun z => Yo (z = \0c) i (Vg f (cpred z))).

Lemma expansion_ext_aug_p1 f i (n:= expansion_value f \2c)
   (f' :=  expansion_ext_aug f i) (m:= expansion_value f' \2c):
  expansion_ext_of_a f n ->  i<c \3c -> (n <> \0c \/ i <> \0c) ->
  (expansion_ext_of_a f' m /\ m = \2c *c n +c i).
Proof.   
rewrite /m/f' /expansion_ext_aug /expansion_ext_of_a.
set k := (cardinal (domain f)); rewrite Lgd.
move => [[[ n3 kN lt13[fgf df fp]] nv] kp] i3 bc.
set F := Lg _ _; set k1 := cardinal _.
have skN:= NS_succ kN.
have pa: k1 = csucc k by apply: card_nat.
have pb: inc k (csucc k) by apply: Nsucc_i.
have pc: exp_boundary F k1. 
  right; split; first by rewrite pa; apply: succ_nz.
  rewrite pa (cpred_pr2 kN) /F LgV//; case: (equal_or_not k \0c) => kz.
    Ytac0; case: bc => //; rewrite - nv /expansion_value /csumb.
    by rewrite csum_trivial //; aw; apply: card_nonempty.
  by Ytac0; case: kp => // [] [].
have pd: expansion_ext F k1.
  hnf; rewrite /F Lgd pa; split => //; split; fprops => j jb; rewrite LgV//.
  have jN:=(NS_inc_nat skN jb).
  Ytac jz => //; apply: fp; rewrite df; move:(cpred_pr jN jz) => [sa sb].
  apply/(NltP kN); apply /(cltSSP (CS_nat sa)(CS_nat kN)).
  by rewrite - sb; apply /(NltP skN).
split => //.
have pe:inc \0c (Nintc k) by apply /(NintcP kN);apply: (cle0n kN).
rewrite /expansion_value /F Lgd -(NintE skN)
  -(Nint_co_cc kN) (fct_sum_rec0 _ kN).
rewrite LgV//; Ytac0; rewrite cpowx0 (cprod1r (proj31_1 i3)); congr (_ +c i).
have ax: forall x, inc x (Nint k) -> inc (csucc x) (Nint1c k).
  move => t /(NintP kN) tk; apply/(Nint1cP kN); split; first by apply:succ_nz.
  by apply /(cleSltP (NS_lt_nat tk kN)).
have qx: (quasi_bij csucc (Nint k) (Nint1c k)).
  split; first by exact.
  + move => u v /Nint_S1 /CS_nat cu /Nint_S1 /CS_nat cv H. 
    by apply: csucc_inj.
  + move => y /(Nint1cP kN) [ynz yk];move:(NS_le_nat yk kN) => yN. 
    move: (cpred_pr yN ynz) => [sa sb]; rewrite sb; exists (cpred y) => //.
    by apply /(NintP kN); apply/(cleSltP sa); rewrite - sb.
rewrite  (csum_Cn2 _ qx) /csumb.
set G := Lg _ _.
have ->: G = Lg k (fun z => (Vg f z) *c (\2c ^c (csucc z))).
  rewrite - (NintE kN); apply:Lg_exten => j ji /=. 
  have ax1: inc (csucc j) (Nint1c k) by apply:ax.
  have ax2: inc (csucc j) (Nintc k).
    by move/(Nint1cP kN): ax1 => [_ h]; apply/(NintcP kN).
  by rewrite LgV// (Y_false (@succ_nz j)) (cpred_pr2 (Nint_S1 ji)).
rewrite - nv /expansion_value cprod2Dn  df; apply: csumb_exten.
by move => j jk /=; rewrite (cpow_succ _ (NS_inc_nat kN jk)) cprodA cprodC.
Qed.
  
Definition expansion_ext_dim f (k := (cardinal (domain f))):=
   Lg (cpred k) (fun z => (Vg f (csucc z))).

Lemma expansion_ext_dim_p1 f (n:= expansion_value f \2c)
  (f' :=  expansion_ext_dim f) (m:= expansion_value f' \2c) (i := Vg f \0c):
  expansion_ext_of_a f n -> n <> \0c ->
  [/\ i<c \3c, expansion_ext_of_a f' m & n = \2c *c m +c i].
Proof.
rewrite /m/f' /expansion_ext_dim /expansion_ext_of_a.
set k := (cardinal (domain f)); rewrite Lgd.
move => [[[ n3 kN lt13[fgf df fp]] nv] kp] nz.
case: (equal_or_not k \0c) => knz.
  case nz; rewrite - nv /expansion_value; apply:csum_trivial; aw.
  by apply: card_nonempty.
have [pkN pkv] :=(cpred_pr kN knz).
have zsdf: inc \0c (domain f)
  by rewrite df pkv; apply/(NleP pkN); apply: (cle0n).
set F := Lg _ _.
have li3: i <c \3c by apply: fp.
have r1:exp_boundary F (cpred k).
  case: kp => // ha;case: (equal_or_not (cpred k) \0c) => pkz; first by left.
  right; rewrite /F; move:(cpred_pr pkN pkz) => [sa sb].
  move: ha => [_ ha]; split; first by rewrite sb; apply: succ_nz.
  rewrite LgV//; [ue | rewrite {2} sb; apply/(NleP sa); fprops].
have r2: expansion_ext F (cpred k).
   rewrite /F; split => //; aw; split; fprops => j ji; rewrite LgV//; apply: fp.
   rewrite df pkv; apply /(NleP pkN); apply /(cleSltP (NS_inc_nat pkN ji)).
   by apply /(NltP pkN).
rewrite (card_nat pkN); split => //.
rewrite - nv /expansion_value /F Lgd df - (NintE kN)  {1} pkv.
  rewrite - (Nint_co_cc pkN).
rewrite (fct_sum_rec0 _ pkN) cpowx0 (cprod1r (proj31_1 li3)); congr (_ +c i).
have ax:lf_axiom csucc (Nint (cpred k)) (Nint1c (cpred k)).
  move => t /(NintP pkN) tk; apply/(Nint1cP pkN); split; first by apply:succ_nz.
  by apply /(cleSltP (NS_lt_nat tk pkN)).
have qx: (quasi_bij csucc (Nint (cpred k)) (Nint1c (cpred k))).
  split; first by exact.
  + move => u v /Nint_S1 /CS_nat cu /Nint_S1 /CS_nat cv H. 
    by apply: csucc_inj.
  + move => y /(Nint1cP pkN) [ynz yk];move:(NS_le_nat yk pkN) => yN. 
    move: (cpred_pr yN ynz) => [sa sb]; rewrite sb; exists (cpred y) => //.
    by apply /(NintP pkN); apply/(cleSltP sa); rewrite - sb.
rewrite  (csum_Cn2 _ qx) /csumb (NintE pkN) (NintE kN).
rewrite  /expansion_value cprod2Dn; apply:csumb_exten => j ji;rewrite LgV//.
by rewrite (cpow_succ _ (NS_inc_nat pkN ji)) cprodA cprodC.
Qed.

Lemma expansion_ext_dim_aug f n i:
   inc f (expansions_ext_of n) -> 
   expansion_ext_dim (expansion_ext_aug f i) = f.
Proof.
move => /Zo_hi [[[ n3 kN lt13[fgf df fp]] nv] kp].
rewrite /expansion_ext_dim /expansion_ext_aug.
rewrite Lgd (card_nat (NS_succ kN)) (cpred_pr2 kN).
apply:fgraph_exten; [fprops | done | by aw | aw => x xi].
have ha :=  (NS_inc_nat kN xi).
rewrite !LgV//.
  by rewrite  (Y_false (@succ_nz x)) (cpred_pr2 ha).
by apply /(NleP kN) /(cleSltP ha) /(NltP kN).
Qed.


Lemma expansion_ext_aug_dim f n:
   inc f (expansions_ext_of n) -> n <> \0c -> 
   expansion_ext_aug (expansion_ext_dim f) (Vg f \0c) = f.
Proof.
move => /Zo_hi [[[ n3 kN lt13[fgf df fp]] nv] kp] nz.
case: (equal_or_not (cardinal (domain f)) \0c) => knz.
   case: nz; rewrite - nv; apply:csum_trivial; aw.
   by apply: card_nonempty.
have [sa sb]:= (cpred_pr kN knz).
rewrite /expansion_ext_dim /expansion_ext_aug.
rewrite Lgd (card_nat sa) - sb.
apply:fgraph_exten; [fprops | done | by aw | aw => x xi].
rewrite (LgV xi); Ytac xz; first by ue.
move: (cpred_pr (NS_inc_nat kN xi) xz) => [sa' sb']; rewrite LgV//; first ue.
apply/(NltP sa); apply/(cleSltP sa'); rewrite - sb'. 
by apply/(cltSleP sa); rewrite - sb; apply /(NltP kN).
Qed.


Lemma expe_odd n: natp n -> Nbexp(csucc (cdouble n)) = Nbexp n. 
Proof.
move => nN.
  have lt1: \1c <c \3c. 
   rewrite - succ_zero; apply/(cltSSP CS0 CS2); apply: clt_02.  
pose F z := expansion_ext_aug z \1c.
pose v f := expansion_value f \2c.
have ha: forall f,  expansion_ext_of_a f (v f) ->
  (expansion_ext_of_a (F f) (v (F f)) /\  (v (F f)) = \2c *c  (v f) +c \1c).
  move => f h; apply: expansion_ext_aug_p1 => //; right; fprops.
symmetry; apply /card_eqP; set E1 := _ n; set E2 := _ (csucc _).
have ax: lf_axiom F E1 E2.
   move => f /Zo_hi h.
   have nv: n = v f by rewrite /v; move: h => [ [_ ->] _].
   have hb: expansion_ext_of_a f (v f) by rewrite - nv.
   have [sa sb]:=(ha _ hb).
   move: sa; rewrite sb - nv - (Nsucc_rw (NS_double nN)); apply:expe_p3.
pose G := expansion_ext_dim.
suff: (bijection (Lf F E1 E2)) by apply: equipotent_aux.
apply: lf_bijective; first done.
  rewrite /F;move => f1 f2 /(expansion_ext_dim_aug \1c) {2} <-. 
  by move /(expansion_ext_dim_aug \1c)  => {2} <- ->.
have dnz: (csucc (cdouble n)) <> \0c by apply: succ_nz.
move => y ye2; move:(expansion_ext_aug_dim ye2 dnz) => sa.
move/Zo_hi: ye2 => sb.
have h: (expansion_value y \2c) = csucc (cdouble n) by move:sb => [ [_ ->] _].
rewrite - h in sb dnz.    
have [ua ub]:= (expansion_ext_dim_p1 sb dnz).
move:(NS_expe_val (proj1(proj1 ub))); set m := _ _ \2c; rewrite h => na nb.
move:(succ_of_even (even_double nN)); rewrite nb; move => [_ nes].
move/(csum_of_evenP (even_double na) (NS_lt_nat ua NS3)):nes => ne1.
have: Vg y \0c <c \2c.
  split; first by apply/(cltSleP NS2). 
  move => un2;case:ne1; rewrite un2; apply: even_two.
move /clt2; case; first by move => un2;case:ne1; rewrite un2; apply: even_zero.
move => eq1.
move: (nb); rewrite eq1 (Nsucc_rw (NS_double nN)).
move/(csum_eq2r NS1 (NS_double nN) (NS_double na)) /(double_inj nN na) => eq2.
rewrite eq1 in sa; rewrite -/m - eq2 in ub.
exists (expansion_ext_dim y) => //;apply:(expe_p3 ub).
Qed.


Lemma expe_even n: natp n -> 
    Nbexp(cdouble (csucc n)) = Nbexp (csucc n) +c (Nbexp n).
Proof.
move => nN.
rewrite /Nbexp.
set Ea := expansions_ext_of _. 
set Eb :=  expansions_ext_of _; set Ec := expansions_ext_of _.
pose V z := (expansion_value z \2c).
have Ha: forall f n, inc f (expansions_ext_of n)-> V f = n.
  by move => f b /Zo_hi [ [_ q] _].
have di1: disjoint Eb Ec.
  apply:disjoint_pr => u /Ha ua /Ha ub.
  by move/NatP:nN => /finite_cP [_]; rewrite - ua ub.
rewrite csum2cl csum2cr - (csum2_pr5 di1).
symmetry.
pose F f:= expansion_ext_aug f (Yo (inc f Eb) \0c \2c).
have lt23: \2c <c \3c by apply:(cltS NS2).
have lt03: \0c <c \3c by apply:(clt_ltT clt_02 lt23).
pose Ez f := (expansion_ext_aug f \0c).
pose Et f := (expansion_ext_aug f \2c).
have Hb:forall f, inc f Eb -> inc (Ez f) Ea.
  move => z za; move: (Ha _ _ za) => eq1;apply: expe_p3.
  move/Zo_hi: za; rewrite - eq1 => zb.
  have zc:expansion_value z \2c <> \0c \/ \0c <> \0c. 
    left; rewrite -/(V _ )eq1; apply: succ_nz.
  move: (expansion_ext_aug_p1 zb lt03 zc) =>[ha].
 by rewrite csum0r; fprops; rewrite /cdouble/V; move => <-.
have Hc:forall f, inc f Ec -> inc (Et f) Ea.
  move => z za; move: (Ha _ _ za) => eq1;apply: expe_p3.
  move/Zo_hi: za; rewrite - eq1 => zb.
  have zc:expansion_value z \2c <> \0c \/ \2c <> \0c by right; fprops.
  move: (expansion_ext_aug_p1 zb lt23 zc) =>[ha]; rewrite -/(V z) eq1.
  by rewrite /cdouble (cprod_nS _ nN) => <-.
have ax: lf_axiom F (Eb \cup Ec) Ea.
  move => f /setU2_P fa; rewrite /F; Ytac h; first by apply: Hb.
  by case fa => // fc;apply: Hc.
have dsnz: cdouble (csucc n) <> \0c.
    exact (proj1(double_nz (NS_succ nN) (@succ_nz n))).
pose D f :=(expansion_ext_dim f).
have rax: forall f, inc f Ea -> 
  ((Vg f \0c) = \0c /\ inc (D f) Eb) \/ ((Vg f \0c) = \2c /\ inc (D f) Ec).
  move =>  z za; move: (Ha _ _ za) => eq1. 
  move/Zo_hi: za; rewrite - eq1 => zb.
  have vnz: V z <> \0c by rewrite eq1. 
  move:(expansion_ext_dim_p1 zb vnz) => [sa sb]; rewrite -/(V z) eq1.
  have mN:=(NS_expe_val (proj1 (proj1 sb))).
  case: (equal_or_not  (Vg z \0c) \0c) => ct0.
    rewrite ct0 (Nsum0r (NS_double mN)) => /(double_inj (NS_succ nN) mN).
    by move => eq; left; split => //;apply:expe_p3; rewrite eq.
  case: (equal_or_not  (Vg z \0c) \1c) => ct1.
    rewrite ct1 - (Nsucc_rw (NS_double mN)) => eq2.
    move:(proj2 (succ_of_even (even_double mN))) (even_double (NS_succ nN)).
    by rewrite - eq2.
  case: (equal_or_not (Vg z \0c) \2c) => ct2; last first.
    have: Vg z \0c <c \2c by split => //;by apply/(cltSleP NS2). 
    by move /clt2; case.
  rewrite /cdouble (cprod_nS _ nN) ct2. 
  move/(csum_eq2r NS2 (NS_double nN) (NS_double mN)) /(double_inj nN mN).
  by move => eq; right; split => //;apply:expe_p3; rewrite eq.
suff bg: bijection (Lf F (Eb \cup Ec) Ea).
   apply /card_eqP; apply: (equipotent_aux bg).
apply: lf_bijective; first done.
  pose H := expansion_ext_dim_aug.
  move => u v us vs; rewrite /F; Ytac ub; Ytac vb => eq.
  + by rewrite -(H _ _ \0c ub)   -(H _ _ \0c vb) eq.
  + case /setU2_P: vs => // vc.
    by rewrite -(H _ _ \0c ub)  -(H _ _ \2c vc) eq.
  + case /setU2_P: us => // uc.
    by rewrite -(H _ _ \2c uc)  -(H _ _ \0c vb) eq.
  + case /setU2_P: vs => // vc; case /setU2_P: us => // uc.
    by rewrite -(H _ _ \2c uc)  -(H _ _ \2c vc) eq.
move => y ye; move: (rax _ ye) (expansion_ext_aug_dim ye dsnz). 
set z := expansion_ext_dim y; case => [] [-> sb] eq.
  by exists z; [ apply/setU2_P; left | rewrite /F; Ytac0 ].
exists z; [ by apply/setU2_P; right | rewrite /F; Ytac hh => //;empty_tac1 z].
Qed.

Lemma expe_fusc n: natp n -> Nbexp n = fusc (csucc n).
Proof.
move: n.
suff: forall n, natp n -> forall k, k <=c n -> Nbexp k = fusc (csucc k).
  move => H n nN; apply:(H n nN); fprops.
apply: Nat_induction.
  by move => k /cle0 ->; rewrite succ_zero fusc1 expe_0.
move => n nN Hrec k lkn;case: (equal_or_not k (csucc n)) => ekn; last first.
   by apply: Hrec; apply /(cltSleP nN).
move:(NS_half nN) => hn.
rewrite ekn; case: (cdouble_halfV nN) => eq1; rewrite eq1.
   rewrite (expe_odd hn) - (double_succ hn) (fusc_even (NS_succ hn)).
   by apply: Hrec; apply: cle_halfn_n. 
rewrite  - (double_succ hn) (expe_even hn) (fusc_odd (NS_succ hn)).
rewrite csumC (Hrec _ (cle_halfn_n nN)) Hrec //.
by rewrite eq1;apply/cleSS; rewrite - eq1; apply: cle_n_doublen.
Qed.

(* sum in the Pascal triangle *)
Lemma sum_diag_pascal n: natp n ->
  csumb (Nintc n) (fun k => binom (n -c k) k)  = Fib (csucc n).
Proof.
move => nN. rewrite (NintcE nN).
move: clt_01 => clt01.
have i01: inc \0c \1c by apply: set1_1.
move:n nN {- 2} n (cleR (CS_nat nN)); apply: Nat_induction.
  move => n /cle0 ->; rewrite succ_zero Fib1 /csumb. 
  set F := Lg _ _.
  have df:domain F = singleton \0c by rewrite/F;aw. 
  have eq1: Vg F \0c = \1c by rewrite /F LgV//; rewrite cdiff_nn (binom0 NS0).
  rewrite (csum_trivial2 df) // eq1; fprops.
move => n nN Hrec m lemn; case: (equal_or_not m (csucc n)) => eqmn; last first.
  by apply: Hrec; apply /(cltSleP nN).
rewrite eqmn; case: (equal_or_not n \0c) => en0.
  rewrite en0 succ_zero succ_one Fib2.
  rewrite - succ_one (fct_sum_rec1 _ NS1) /csumb; set F := Lg _ _.
  have df: domain F = singleton \0c by rewrite /F; aw.
  have hb: \0c <c csucc \0c by rewrite succ_zero; apply:clt_01.
  have pa: Vg F \0c = \0c.
    rewrite /F (LgV i01) succ_zero cdiff_nn (binom_bad NS0 NS1) //.
  have pb: cardinalp(Vg F \0c) by rewrite pa; fprops.
  rewrite (csum_trivial2 df pb) pa (cdiff_n0 NS1) (binom0 NS1).
  by rewrite (Nsum0l NS1).
move: (cpred_pr nN en0) => [sa sb].
rewrite (fct_sum_rec1 _ (NS_succ nN)).
rewrite (induction_on_sum _ nN).
rewrite cdiff_nn (binom_bad NS0 (NS_succ nN) (succ_positive n)). 
rewrite csum0r; last by apply: CS_csum.
have hb: forall i, inc i n ->
  binom (csucc n -c csucc i) (csucc i) =  binom (n -c csucc i) (csucc i) 
  +c binom (cpred n -c i) i.
  move => i iI; move/(NltP nN): iI => lt1.
  have iN := (NS_lt_nat lt1 nN).
  have hb: csucc i <=c n by apply /(cleSltP iN).
  rewrite (cdiff_pr6 nN iN) (csucc_diff nN iN hb) - (cdiff_pr6 sa iN) - sb.
  by rewrite (binomSnSm (NS_diff (csucc i) nN) iN).
rewrite /csumb (Lg_exten hb) - /(csumb _ _) - sum_of_sums.
have ->: binom (csucc n -c \0c) \0c = binom (csucc (cpred n) -c \0c) \0c.
  rewrite - sb !binom0 //; fprops.
rewrite {3} sb (Hrec  _ (cpred_le (CS_nat nN))) - sb (csumC _ (Fib n)) - csumA.
rewrite {2} sb - (fct_sum_rec1 (fun i=> binom (n -c i) i) (NS_succ sa)).
by rewrite - sb (Fib_rec nN) (Hrec _ (cleR (CS_nat nN))).
Qed.


Lemma bin_mod2_rec1 n k : natp n -> natp k ->
  eqmod \2c (binom (csucc (csucc n)) (csucc (csucc k)))
  ((binom n (csucc (csucc k))) +c (binom n k)).
Proof.
move => nN kN.
move: (NS_succ nN) (NS_succ kN) => snN skN.
rewrite (binomSnSm snN skN)  (binomSnSm nN skN) (binomSnSm nN kN).
set A := binom _ _;rewrite csumA - (csumA A) (csumC A) csum_nn - csumA.
apply:(crem_prop NS2 card2_nz); try apply: NS_sum;apply: NS_binom; fprops.
Qed.

Lemma bin_mod2_rec2 n k: natp n -> natp k -> 
  eqmod \2c (binom (cdouble n) (cdouble k)) (binom n k).
Proof.
move => nN kN; case: (equal_or_not k \0c) => knz.
  by rewrite knz cdouble0 ! binom0 //; apply: NS_double.
move: (cpred_pr kN knz) => [sa ->].
move: {k kN knz} n nN (cpred k) sa; apply: Nat_induction.
  move => k kN.
  have ha: \0c <c csucc k by apply: succ_positive.
  have hb: \0c <c (cdouble (csucc k)). 
    by rewrite (double_succ kN); apply: succ_positive.
  rewrite cdouble0 (binom_bad NS0 (NS_double (NS_succ kN)) hb).
  by rewrite (binom_bad NS0 (NS_succ kN) ha).
move => n nN Hrec k kN.
have dnN := NS_double nN.
have dkN := NS_double kN.
have dskN := NS_double (NS_succ kN).
have ha: natp (binom (cdouble n) (cdouble (csucc k))) by apply:NS_binom;fprops.
have hb: natp (binom (cdouble n) (cdouble k)) by apply:NS_binom;fprops.
have hc:=(NS_binom nN (NS_succ kN)); have hd:= (NS_binom nN kN).
rewrite (double_succ nN) (double_succ kN). 
rewrite /eqmod (bin_mod2_rec1 (NS_double nN) (NS_double kN)).
rewrite - (double_succ kN) (crem_sum NS2 card2_nz ha hb)  (Hrec _ kN).
rewrite (binomSnSm nN kN) (crem_sum NS2 card2_nz hc hd).
congr ((_ +c _) %%c \2c); case: (equal_or_not k \0c) => ekz.
  rewrite ekz cdouble0 !binom0 //.
by move:(cpred_pr kN ekz) => [pN ->]; apply:Hrec.
Qed.


Lemma bin_mod2_prop1 n k: natp n -> natp k -> 
  (binom (cdouble n) (csucc (cdouble k))) %%c \2c =  \0c.
Proof.
move => nN kN.
case: (equal_or_not k \0c) => ekz.
  rewrite ekz cdouble0 succ_zero (binom1 (NS_double nN)).
  apply:(proj33(cdivides_pr1 nN NS2)).
move: (cpred_pr kN ekz) => [sa ->].
move: {k kN ekz} n nN (cpred k) sa; apply: Nat_induction.
  move => k kN. 
  have ha: \0c <c csucc (cdouble (csucc k)) by apply: succ_positive.
  have hb:= (NS_succ (NS_double (NS_succ kN))).
  by rewrite cdouble0 (binom_bad NS0 hb ha) (crem_of_zero NS2).
move => n nN Hrec k kN.
have dnN := NS_double nN.
have dkN := NS_double kN.
have sdkN := NS_succ dkN.
have sdskN := NS_succ (NS_double (NS_succ kN)).
have ha:natp (binom (cdouble n) (csucc (cdouble (csucc k)))) by apply:NS_binom.
have hb:natp (binom (cdouble n) (csucc (cdouble k))) by apply:NS_binom.
rewrite (double_succ nN) (double_succ kN) /eqmod (bin_mod2_rec1 dnN sdkN).
rewrite -(double_succ kN) (crem_sum NS2 card2_nz ha hb).
have ->: binom (cdouble n) (csucc (cdouble k)) %%c \2c = \0c.
  case: (equal_or_not k \0c) => knz.
    rewrite knz cdouble0 succ_zero (binom1 dnN).
    exact: (proj33(cdivides_pr1 nN NS2)). 
  by move:(cpred_pr kN knz) => [sa ->]; apply: Hrec.
by rewrite (Hrec _ kN) (csum0r CS0) (crem_of_zero NS2).
Qed.


Lemma bin_mod2_prop2 n k: natp n -> natp k -> 
  eqmod \2c (binom (csucc (cdouble n)) (cdouble k)) (binom n k).
Proof.
move => nN kN.
case: (equal_or_not k \0c) => ekz.
   rewrite ekz cdouble0 !binom0 //; fprops; apply:(NS_succ(NS_double nN)).
move:(cpred_pr kN ekz) => [sa ->].
have ha:=(NS_double nN). 
have hb:=(NS_succ(NS_double sa)).
have hc:= (NS_binom ha (NS_double (NS_succ sa))).
have he:=(NS_binom nN (NS_succ sa)).
have hd:=(NS_binom ha hb).
rewrite (double_succ sa) (binomSnSm ha hb) /eqmod  - (double_succ sa). 
rewrite (crem_sum NS2 card2_nz hc hd) (bin_mod2_rec2 nN (NS_succ sa)).
by rewrite (bin_mod2_prop1 nN sa) (Nsum0r (NS_rem \2c he)) (cmodmod2 he).
Qed.

Lemma bin_mod2_prop3 n k: natp n -> natp k -> 
  eqmod \2c (binom (csucc (cdouble n)) (csucc (cdouble k))) (binom n k).
Proof.
move => nN kN.
move:(NS_double nN)(NS_double kN) => n2N k2N.
move: (NS_binom n2N (NS_succ k2N)) (NS_binom n2N k2N) => ha hb.
have he := (NS_binom nN kN). 
rewrite (binomSnSm n2N k2N) /eqmod (crem_sum NS2 card2_nz ha hb).
rewrite (bin_mod2_rec2 nN kN) (bin_mod2_prop1 nN kN).
by rewrite (Nsum0l (NS_rem \2c he)) (cmodmod2 he).
Qed.


Lemma rem_two_prop1 m i: natp m -> natp i -> 
   (cdouble m) %%c \2c ^c (csucc i) = cdouble (m %%c \2c ^c i).
Proof.  
move =>mN iN. 
have p1nz: \2c ^c i <> \0c by apply:cpow_nz; apply: card2_nz.
move: (NS_pow NS2 iN) (NS_pow NS2 (NS_succ iN)) => p1N p2N.
move:(cdivision mN p1N p1nz).
set q :=  (m %/c \2c ^c i); set r := (m %%c \2c ^c i).
move => [qN rN [pa pb]].
have ha:cdivision_prop (cdouble m) (\2c ^c csucc i) q (cdouble r).
  rewrite - (cdouble_pow2 iN).
  split; first by rewrite pa - double_sum {1}/cdouble cprodA. 
  by apply /(double_monotone2 rN p1N).
by move: (proj2(cquorem_pr (NS_double mN) p2N qN (NS_double rN) ha)).
Qed.


Lemma rem_two_prop2 m i: natp m -> natp i -> 
   (csucc (cdouble m)) %%c \2c ^c (csucc i) = csucc (cdouble (m %%c \2c ^c i)).
Proof.  
move =>mN iN. 
have p1nz: \2c ^c i <> \0c by apply:cpow_nz; apply: card2_nz.
move: (NS_pow NS2 iN) (NS_pow NS2 (NS_succ iN)) => p1N p2N.
move:(cdivision mN p1N p1nz).
set q :=  (m %/c \2c ^c i); set r := (m %%c \2c ^c i).
move => [qN rN [pa pb]].
have drN:=(NS_double rN).
have ha:cdivision_prop (csucc (cdouble m)) (\2c ^c csucc i) q 
   (csucc (cdouble r)).
  rewrite - (cdouble_pow2 iN).
  split; first by rewrite pa - double_sum {1}/cdouble cprodA csum_nS.
  by apply /(double_monotone3 rN p1N).
by move: (proj2(cquorem_pr (NS_succ (NS_double mN)) p2N qN (NS_succ drN) ha)).
Qed.

Lemma binom_evenP n k: natp n -> natp k ->
  (evenp (binom n k) <->
   exists2 i, natp i & n %%c (\2c ^c i) <c  k %%c (\2c ^c i)).
Proof.
move => nN kN.
have aux:evenp (binom n k)  <-> (binom n k) %%c \2c = \0c.
  split; [by move => [] | move => h; split => //; exact:(NS_binom nN kN)].
apply: (iff_trans aux); clear aux.
have Ha:=(crem_of_zero NS2).
have Hb:= (crem_small NS2 clt_12).
move: n nN {-2} (n) (cleR (CS_nat nN)) k kN.
apply: Nat_induction.
  move => n /cle0 -> k kN.
  case: (equal_or_not k \0c) => kz.
    rewrite kz binom00 - Hb; split; first by move:card1_nz.
    by move => [i iN]; rewrite (crem_of_zero (NS_pow NS2 iN)) => [] [_].
  move/(strict_pos_P1 kN): kz => kp.
  rewrite (binom_bad NS0 kN kp) Ha; split => // _.
  exists k => //; rewrite (crem_of_zero (NS_pow NS2 kN)).
  by rewrite - (crem_small (NS_pow NS2 kN) (cantor (CS_nat kN))).
move => m mN Hrec n lemn k kN.
case:(equal_or_not n (csucc m)) => emn; last first.
   by apply: Hrec => //; apply /(cltSleP mN).
move: (NS_succ mN); rewrite - emn => nN.
move: (NS_half nN) (NS_half kN) => hnN hkN.
have ha: chalf n <=c m.
  apply /(cltSleP mN); rewrite - emn;case: (cdouble_halfV nN) => nv.
    rewrite {2} nv; apply:(clt_n_doublen hnN) => bad.
     by case: (@succ_nz m); rewrite -emn nv bad cdouble0.
  rewrite {2} nv;apply/(cltSleP (NS_double hnN)); apply :(cle_n_doublen hnN).
have aux: forall i, natp i -> natp (chalf n %%c \2c ^c i) 
    /\ natp (chalf k %%c \2c ^c i).
  by move => i iN; move: (NS_pow NS2 iN) => h; split; apply: NS_rem.
have aux2: forall i, natp i -> i %%c \2c ^c \0c = \0c.
  move => i iN; rewrite cpowx0; exact: (proj33 (cdivides_one iN)).
have Hc:=(Hrec _ ha _ hkN).
case: (cdouble_halfV nN);case: (cdouble_halfV kN) => kv nv.
+ rewrite kv nv (bin_mod2_rec2 hnN hkN); split.
    move/Hc => [i iN ip]; move: (NS_succ iN) => siN;exists (csucc i); first exact. (*foo*)
    move:(aux _ iN) => [pa pb].
    rewrite(rem_two_prop1 hnN iN) (rem_two_prop1 hkN iN).
    by apply /double_monotone2.
  move => [i iN ip]; apply/Hc; case: (equal_or_not i \0c) => eiz.
    by move: (proj2 ip); rewrite eiz -nv -kv (aux2 _ nN) (aux2 _ kN).
  move:(cpred_pr iN eiz) => [sa sb]; exists (cpred i); first exact. (*foo*)
  move:(aux _ sa) => [pa pb].
  move: ip; rewrite {1 2} sb (rem_two_prop1 hnN sa) (rem_two_prop1 hkN sa).
  by move/(double_monotone2 pa pb).
+ rewrite kv nv (bin_mod2_prop1 hnN hkN) - kv.
  split.
    move => _; exists \1c; [ apply: NS1 |rewrite (cpowx1 CS2)].
    rewrite(proj2 (even_double (NS_half nN))).
    have /oddp_alt[_ ->]:oddp k by rewrite kv; apply:(odd_succ_double hkN).
    apply: clt_01.
  rewrite - nv; split => //; apply:(NS_binom nN kN).
+ rewrite kv nv (bin_mod2_prop2 hnN hkN); split.
    move/Hc => [i iN ip]; move: (NS_succ iN) => siN;exists (csucc i); first exact. (*foo*)
*    move:(aux _ iN) => [pa pb].
    rewrite(rem_two_prop2 hnN iN) (rem_two_prop1 hkN iN).
    by apply /double_monotone3.
  move => [i iN ip]; apply/Hc; case: (equal_or_not i \0c) => eiz.
    by move: (proj2 ip); rewrite eiz -nv -kv (aux2 _ nN) (aux2 _ kN).
  move:(cpred_pr iN eiz) => [sa sb]; exists (cpred i); first exact. (*foo*)
  move:(aux _ sa) => [pa pb].
  move: ip; rewrite {1 2} sb (rem_two_prop2 hnN sa) (rem_two_prop1 hkN sa).
  by move/(double_monotone3 pa pb).
+ rewrite kv nv  (bin_mod2_prop3 hnN hkN); split.
    move/Hc => [i iN ip]; move: (NS_succ iN) => siN;exists (csucc i).
      exact.
    move:(aux _ iN) => [pa pb].
    rewrite(rem_two_prop2 hnN iN) (rem_two_prop2 hkN iN).
    apply /(cltSSP (CS_nat (NS_double pa)) (CS_nat (NS_double pb))).
    by apply /double_monotone2.
  move => [i iN ip]; apply/Hc; case: (equal_or_not i \0c) => eiz.
        by move: (proj2 ip); rewrite eiz -nv -kv (aux2 _ nN) (aux2 _ kN).
  move:(cpred_pr iN eiz) => [sa sb]. exists (cpred i); first exact. (*foo*)
  move:(aux _ sa) => [pa pb].
  move: ip; rewrite {1 2} sb (rem_two_prop2 hnN sa) (rem_two_prop2 hkN sa).
  move/(cltSSP (CS_nat (NS_double pa)) (CS_nat (NS_double pb))).
  by move/(double_monotone2 pa pb).
Qed.

Definition sum_diag_pascal2 n := 
  csumb (Nintc n) (fun k => (binom (n -c k) k) %%c \2c).

Lemma sum_diag_pascal2_0: sum_diag_pascal2 \0c = \1c.
Proof.
rewrite /sum_diag_pascal2/csumb Nint_cc00.
set F := Lg _ _.
have ha: domain F= singleton \0c by rewrite /F; aw.
have hb:  Vg F \0c = \1c.
  rewrite /F LgV; [by rewrite cdiff_nn (binom0 NS0) crem_12 |fprops].
have hc: cardinalp (Vg F \0c) by rewrite hb; apply: CS1.
by rewrite (csum_trivial2 ha hc).
Qed.


Lemma sum_diag_pascal_mod2_even n (S := sum_diag_pascal2) : natp n ->
  S (csucc (csucc (cdouble n))) = S (csucc n) +c S n.
Proof.
move => nN.
have ha:= (NS_succ nN); have dnN := (NS_double nN).
have hb:= (NS_succ dnN); have hc:=(NS_succ hb).
rewrite /S /sum_diag_pascal2 (split_sum_even_odd _ hc (@succ_nz _)).
rewrite (cpred_pr2 hb) (odd_half nN).  
rewrite - (double_succ nN) (even_half ha); apply: f_equal2;
   rewrite/csumb; apply: f_equal; 
   apply: Lg_exten => i ii;move:(Nint_S ii) => iN.
+ rewrite - (cprodBl NS2 ha iN); apply:(bin_mod2_rec2 (NS_diff i ha) iN).
+ rewrite (double_succ nN) (cdiff_pr6 hb (NS_double iN)).
  move /(NintcP nN): ii => /(double_monotone iN nN) /(cdiffSn dnN) ->.
  rewrite - (cprodBl NS2 nN iN); apply:(bin_mod2_prop3 (NS_diff i nN) iN).
Qed.


Lemma sum_diag_pascal_mod2_odd n (S := sum_diag_pascal2) : natp n ->
  S (csucc (cdouble n)) = S n.
Proof.
move => nN.
have dN := (NS_double nN).
have h:=(NS_succ dN).
rewrite /S /sum_diag_pascal2 (split_sum_even_odd _ h (@succ_nz _)).
rewrite (odd_half nN) (cpred_pr2 dN) (even_half nN). 
set A := ( X in X +c _ ); set B := csumb _ _.
have cA: cardinalp  A by apply:CS_csum.
have ->: B = csumb (Nintc n) (fun i => \0c).
  rewrite /B/cst_graph /csumb; apply:f_equal; apply:Lg_exten.
  move => i /(NintcP nN) lein; move:(NS_le_nat lein nN) => iN.
  rewrite (cdiff_pr6 dN (NS_double iN)).
  by rewrite - (cprodBl NS2 nN iN) (bin_mod2_prop1 (NS_diff i nN) iN).
rewrite csum_of_same cprod0l (csum0r cA) /A /csumb. 
apply:f_equal; apply:Lg_exten => i ii; move:(Nint_S ii) => iN.
move /(NintcP nN): ii => /(double_monotone iN nN) /(cdiffSn dN) ->.
rewrite - (cprodBl NS2 nN iN);apply: (bin_mod2_prop2 (NS_diff i nN) iN).
Qed.

Lemma sum_diag_pascal_prop n: natp n ->
   (sum_diag_pascal2 n) = fusc (csucc n).
Proof.
move: n. 
suff: forall n, natp n -> n <> \0c -> (sum_diag_pascal2 (cpred n)) = fusc n.
  move => H n nN. 
 rewrite - {1} (cpred_pr2 nN); apply:(H _ (NS_succ nN) (@succ_nz _)).
apply: fusc_induction.
+ done.
+ move => _.
  rewrite - {1} succ_zero (cpred_pr2 NS0) fusc1;apply:sum_diag_pascal2_0.
+ move => n nN H dnz; case: (equal_or_not n \0c) => enz.
    by case: dnz; rewrite enz cdouble0.
  move:(cpred_pr nN enz) => [sa sb]; rewrite (fusc_even nN) - (H enz).
  rewrite {1} sb (double_succ sa) (cpred_pr2 (NS_succ (NS_double sa))).
  rewrite (sum_diag_pascal_mod2_odd sa) //; apply: NS_succ.
+ move => k kN H1 H2 _.
  rewrite (fusc_odd kN) (cpred_pr2 (NS_double kN)).
  case: (equal_or_not k \0c) => ekn.
   by rewrite ekn cdouble0 succ_zero fusc0 fusc1 sum_diag_pascal2_0(csum0l CS1).
  move:(cpred_pr kN ekn) => [sa sb].
  rewrite sb (double_succ sa) (sum_diag_pascal_mod2_even sa).
  by rewrite - sb (H1  ekn) csumC - (H2 (@succ_nz _)) (cpred_pr2 kN).
Qed.

Lemma csum_fusc_row n: natp n ->
  csumb (interval_co Nat_order (\2c ^c n)  (\2c ^c (csucc n))) fusc 
  = \3c ^c n.
Proof.
move => nN. 
have ->: csumb(interval_co Nat_order (\2c ^c n) (\2c ^c (csucc n))) fusc =
   csumb (Nint (\2c ^c n)) (fun z => fusc (z +c (\2c ^c n))).
  move: (NS_pow NS2 nN) => ha.
  have hha := NS_sum ha ha.
  rewrite - (cdouble_pow2 nN) /cdouble - csum_nn.
  apply: csum_Cn2; split.
  + move => x /(NintP ha) len. 
    move:(NS_lt_nat len ha) => xN; move:(NS_sum xN ha) => sn.
    have hc:= (NS_pow NS2 (NS_succ nN)).
    have hb: \2c ^c n <=c x +c \2c ^c n by apply:csum_Mle0;fprops.
    apply/Nint_coP1 => //.
   by move:(csum_Mlteq ha len) => [pa pb]. 
  + by move => x y /Nint_S1 xN /Nint_S1 yN; apply:csum_eq2r.
  + move => y /Nint_coP [[_ pa pb] [[_ pc pd] pe]]; move: (cdiff_pr pb) => hd.
    exists (y -c ( \2c ^c n)) ; last by rewrite csumC  hd.
    apply /(NintP ha);rewrite - {1} hd in pd.
    have pf: \2c ^c n +c (y -c \2c ^c n) <> \2c ^c n +c \2c ^c n by ue.
    exact:(csum_lt2l ha (NS_diff (\2c ^c n) pa) ha (conj pd pf)).
move: n nN; apply: Nat_induction. 
  rewrite ! cpowx0 (proj2 Nint_co01) /csumb.
  set F1 := Lg _ _; have ha: (domain F1 =  singleton \0c) by rewrite /F1; aw.
  rewrite  (csum_trivial1 ha) /F1 (LgV (set1_1 \0c)). 
  by rewrite (csum0l CS1) fusc1(card_card CS1).
move => n nN Hrec.
have ha := (NS_pow NS2 nN).
rewrite (split_sum_even_odd_alt _ (NS_pow NS2 (NS_succ nN))).
rewrite - (cdouble_pow2 nN) (even_half ha) (odd_half ha).
have ->: csumb (Nint (\2c ^c n))
     (fun k => fusc (cdouble k +c cdouble (\2c ^c n))) =
  csumb (Nint (\2c ^c n)) (fun k => fusc (k +c (\2c ^c n))).
  apply: csumb_exten => i /Nint_S1 iN.
  rewrite double_sum; apply: fusc_even; fprops. 
have ->: csumb (Nint (\2c ^c n))
     (fun k => fusc (csucc (cdouble k) +c cdouble (\2c ^c n))) =
   csumb (Nint (\2c ^c n))
     (fun k => fusc (k +c \2c ^c n)  +c  fusc ((csucc k) +c (\2c ^c n))). 
  apply: csumb_exten => i /Nint_S1 iN.
  rewrite (csum_Sn _ (NS_double iN)) double_sum (fusc_odd (NS_sum iN ha)).
  by rewrite - (csum_Sn _ iN).
suff H: csumb (Nint (\2c ^c n)) (fun i => fusc (csucc i +c \2c ^c n)) =
  csumb (Nint (\2c ^c n)) (fun i => fusc (i +c \2c ^c n)).
  rewrite - sum_of_sums H ! Hrec csum_nn csumC cprodC -(cprod_nS _ NS2).
  by rewrite (cpow_succ _ nN).
have hb: (\2c ^c n) <> \0c by  apply cpow_nz; apply : card2_nz.
move:(cpred_pr ha hb) => [sa sb].
have hc: (Nint (\2c ^c n))  = (Nintc (cpred (\2c ^c n))). 
  by rewrite {1} sb - (Nint_co_cc sa).
symmetry.
rewrite {1} hc (fct_sum_rec0 _ sa) (Nsum0l ha) (fusc_pow2 nN).
rewrite (NintE ha) {3} sb (induction_on_sum _ sa) - sb  csum_nn.
rewrite - /(cdouble _) (cdouble_pow2 nN)  (fusc_pow2 (NS_succ nN)).
congr (_ +c \1c);apply:csum_Cn2; split.
+ move => x /(NltP sa) hd; apply /(Nint1cP sa); split;first by apply: succ_nz.
  by apply /(cleSltP (NS_lt_nat hd sa)).
+ move => x y /(NS_inc_nat sa) xN /(NS_inc_nat sa) yN.
  apply /csucc_inj; fprops.
+ move => y  /(Nint1cP sa) [ya yb]; move:(NS_le_nat yb sa) => yN.
  move:(cpred_pr yN ya) => [sc eq1]; exists (cpred y) => //.
  by apply /(NltP sa); apply/(cleSltP sc); rewrite - eq1.
Qed.



Lemma fusci_one a b: natp a -> natp b -> Fusci \1c a b = a +c b.
Proof.
move => aN bN; rewrite - succ_zero  - (cprod0r \2c) (fusci_odd NS0 aN bN).
by rewrite (fusci_zero _ (NS_sum aN bN)).
Qed.

Lemma fusci_palindrome_aux u u' v a b: 
   natp a -> natp b -> natp u -> natp u' -> natp v ->
   csucc (u +c u') = \2c ^c v ->
   Fusci (\2c ^c v +c u) a b = Fusci (\2c ^c v +c u') b a.
Proof.
move => an bn un u'n vn; move: v vn u u' a b un u'n an bn.
apply: Nat_induction.
  move => u u' a b uN  u'N aN bN; rewrite cpowx0 - succ_zero.
  move /(csucc_inj (CS_sum2 u u') CS0) /csum_nz => [-> ->].
  by rewrite succ_zero (csum0r CS1) (fusci_one aN bN) (fusci_one bN aN) csumC.
move => n nN Hrec u u' a b uN u'N aN bN; rewrite - (cdouble_pow2 nN) => eq1.
have p2N:=(NS_pow NS2 nN).
case:(p_or_not_p (evenp (u +c u'))) => ouu.
  move:(succ_of_even ouu);rewrite eq1; move => [_]; case.
  apply:(even_double p2N).
have: evenp u \/ evenp u'.
  case: (p_or_not_p (evenp u)) => ou; first by  left.
  case: (p_or_not_p (evenp u')) => ou'; first by right.
  case: ouu; exact: (csum_of_odd (conj uN ou) (conj u'N ou')).
wlog eu: a b aN bN u u' uN u'N eq1 ouu/ (evenp u).
   move => H ha;case: (ha) => aux; first by apply: H.
   by symmetry;apply: H => //; [rewrite csumC | rewrite csumC | left].
move:(NS_half uN) (NS_half u'N) => huN hu'N _.
move: (NS_sum huN hu'N) => shN.
move: (half_even eu) => h1.
case: (cdouble_halfV u'N) => h2.
  by case: ouu; rewrite h1 h2 double_sum; apply: even_double;fprops.
move: eq1; rewrite h1 h2 (csum_nS _ (NS_double hu'N)) double_sum.
rewrite - (double_succ shN); move /(double_inj (NS_succ  shN) p2N) => eq2.
rewrite (csum_nS _ (NS_double hu'N)) ! double_sum.
rewrite (fusci_even (NS_sum p2N huN) aN bN).
rewrite (fusci_odd  (NS_sum p2N hu'N) bN aN) (csumC b).
exact: (Hrec _ _ _ _ huN hu'N  (NS_sum aN bN) bN eq2).
Qed.

Lemma fusc_palindrome_bis u u' v w w'  
   (aux := fun u v w => csucc(cdouble (\2c ^c v +c u)) *c (\2c ^c w)):
   natp u -> natp u' -> natp v -> natp w ->  natp w' ->
   csucc (u +c u') = \2c ^c v -> 
   fusc (aux u v w)  = fusc (aux u' v w').
Proof.
move => uN u'N vN wN w'N eq.
have Ha: forall u v w, natp u ->natp v -> natp w -> 
   fusc (aux u v w) = Fusci (\2c ^c v +c u) \1c \1c.
  move => u1 v1 w1 u1n v1n w1n; rewrite /aux.
  move: (NS_sum (NS_pow NS2 v1n) u1n).
  set a := (\2c ^c v1 +c u1) => aN.
  move:(NS_succ (NS_double aN)); set b := (csucc (cdouble a)) => bN.
  rewrite - (fusci_val (NS_prod bN (NS_pow NS2 w1n))).
  transitivity (Fusci b \1c \0c); last first.
       rewrite fusci_odd  ?(csum0r CS1); fprops.
  move:w1 w1n; apply: Nat_induction. 
    by rewrite cpowx0 (cprod1r (CS_nat bN)).
  move => n nN <-; rewrite (cpow_succ _ nN) cprodA cprodC.
  by rewrite (fusci_even (NS_prod bN (NS_pow NS2 nN)) NS1 NS0) (csum0r CS1).
rewrite (Ha _ _ _ uN vN wN) (Ha _ _ _ u'N vN w'N).
exact: (fusci_palindrome_aux NS1 NS1 uN u'N vN eq).
Qed.

Definition Fuscj n m := Fusci n (fusc (csucc m)) (fusc m).

Lemma fuscj_zero m: natp m -> Fuscj \0c m = fusc m.
Proof. by move => mN; rewrite /Fuscj (fusci_zero _ (NS_fusc mN)). Qed.

Lemma fuscj_val n: natp n -> Fuscj n \0c = fusc n.
Proof. 
move: fusc_pr => [Ha Hb Hc Hd].
by move => nN; rewrite /Fuscj succ_zero Ha Hb (fusci_val nN).
Qed.

Lemma fuscj_even n m: natp n -> natp m -> 
   Fuscj (cdouble n) m = Fuscj n (cdouble m).
Proof. 
move: fusc_pr => [Ha Hb Hc Hd] nN mN.
move: (NS_fusc mN) (NS_fusc (NS_succ mN)) => sa sb.
by rewrite /Fuscj (fusci_even nN sb sa) (Hc _ mN) (Hd _ mN) csumC.
Qed.

Lemma fuscj_odd n m: natp n -> natp m -> 
   Fuscj (csucc (cdouble n)) m = Fuscj n (csucc (cdouble m)).
Proof.
move: fusc_pr => [Ha Hb Hc Hd] nN mN.
move: (NS_fusc mN) (NS_fusc (NS_succ mN)) => sa sb.
rewrite /Fuscj (fusci_odd nN sb sa) - (double_succ mN) (Hc _ (NS_succ mN)).
by rewrite (Hd _ mN) csumC.
Qed.

Lemma fuscj_one n: natp n -> Fuscj \1c n = Fuscj \0c (csucc (cdouble n)).
Proof.
move => nN.
by rewrite - succ_zero - {1} (cprod0r \2c) (fuscj_odd NS0 nN).
Qed.

Lemma fusc_fib1: fusc \2c = Fib \1c.
Proof.  by rewrite fusc2 Fib1. Qed.

Lemma fusc_fib2: fusc \1c = Fib \2c.
Proof.  by rewrite fusc1 Fib2. Qed.

Lemma fuscj_reverse n: natp n -> Fuscj n \0c = Fuscj \0c (base_two_reverse n).
Proof.
move:(cprod0r \2c) n => d2.
pose R a b := (b *c \2c ^c (clog2 a) +c (base_two_reverse a)).
suff: forall a, natp a -> forall b, natp b -> Fuscj a b = Fuscj \0c (R a b).
  by move => H n nN; rewrite(H _  nN _ NS0) /R cprod0l (Nsum0l (NS_reverse nN)).
have aux: forall b, natp b -> Fuscj \0c b = Fuscj \0c (R \0c b).
  move => b bN. 
  by rewrite /R clog0 base2r_zero cpowx0 (cprod1r (CS_nat bN))(Nsum0r bN).
apply: fusc_induction.
+ by move => b bN; apply: aux.
+ move => b bN; rewrite /R base2r_one clog1 (cpowx1 CS2) cprodC (fuscj_one bN).
  by rewrite (Nsucc_rw (NS_double bN)).
+ move => k kN Ha b bN.
  case: (equal_or_not k \0c) => knz. 
    by rewrite knz cdouble0; apply: aux.
  rewrite /R (clog_double kN knz) (base2r_even kN) - (cdouble_pow2 (NS_log kN)).
  by rewrite(fuscj_even kN bN) (Ha _ (NS_double bN)) /R cprodA (cprodC b).
+ move => k kN Ha Hb b bN.
  rewrite (fuscj_odd kN bN) (Ha _ (NS_succ (NS_double bN))) /R (base2r_odd kN).
  rewrite csumA (clog_succ_double kN) - (cdouble_pow2 (NS_log kN)) cprodA.
  by rewrite cprodC (cprod_nS _ (NS_double bN)) cprodC (cprodC b).
Qed.
  
(* rat_iterator *)

Definition rat_iterator x :=
    BQinv (\1q +q (BQdouble (BQ_of_Z(BQfloor x))) -q x).

Lemma QS_rati x: ratp x -> inc (rat_iterator x) BQ.
Proof.
move => h.
apply: QS_inv; apply: (QS_diff _ h); apply: (QSs QS1); apply:QSdouble.
by apply: BQ_of_Z_iQ; apply: ZS_floor.
Qed.

Lemma rati_0: rat_iterator \0q = \1q.
Proof.
rewrite /rat_iterator BQfloor_0 / BQdouble (BQprod_0r QS2) (BQsum_0r QS1).
by rewrite (BQdiff_0r QS1) BQinv_1.
Qed.


Lemma rati_pos x: inc x BQp -> inc (rat_iterator x) BQps.
Proof.
move =>h; apply:QpsS_inv.
move:(QpS_floor h) (BQp_sBQ h) => fp xq.
move: (BQ_of_Z_iQp fp) (proj2 (BQ_floorp xq)).
set y := BQ_of_Z _ => yp lt1.
have yq: ratp y by exact: (BQp_sBQ yp).
rewrite - (BQdouble_p yq) (BQsumA QS1 yq yq) (BQsumC (\1q +q y)).
rewrite /BQdiff - (BQsumA yq (QSs QS1 yq)  (QSo xq)).
by apply: (QpsS_sum_r yp); apply /(qlt_diffP xq (QSs QS1 yq)); rewrite BQsumC.
Qed.

Lemma BQfloor_spec_sum a b:
  ratp a -> (exists2 c, inc c BZ & b = BQ_of_Z c) ->
  BQ_of_Z (BQfloor (a +q b)) = BQ_of_Z (BQfloor a) +q b.
Proof.
move => aq [c cz ->].
have faz:= (ZS_floor aq).
have cq:= (BQ_of_Z_iQ cz).
have sz:= (ZSs faz cz).
rewrite (BQsum_cZ faz cz); congr BQ_of_Z.
move: (BQ_floorp aq); set fa := BQfloor a; move => [sa sb].
symmetry; apply: (BQ_floorp2 (QSs aq cq) sz); split.
  by rewrite - BQsum_cZ; move/(BQsum_le2r (proj31 sa) aq cq): sa.
rewrite - (BQsum_cZ faz cz) (BQsumC _ \1q) (BQsumA  QS1 (proj31 sa) cq).
by rewrite (BQsumC \1q); apply/(BQsum_lt2r aq (proj32_1 sb) cq).
Qed.

Lemma rati_neg x (f:= rat_iterator) (T:= fun x => BQinv (BQopp x)) (y := f x) :
   inc x BQps -> f (T y) = T x.
Proof.
move => xp; congr BQinv.
have xq:=(BQps_sBQ xp).
have yqps: inc y BQps by apply: (rati_pos (BQps_sBQp xp)).
have yq: ratp y by apply:BQps_sBQ.
have h0:= (ZS_floor xq); have h1:=(ZSp ZS2 h0).
move: (BQ_of_Z_iQ h0); set t := (BQ_of_Z (BQfloor x)) => tq.
have t2q:=(QSdouble tq).
have d1q: inc (\1q +q BQdouble t) BQ by apply:(QSs QS1).
have: T y = BQopp (\1q +q (BQdouble (BQ_of_Z (BQfloor x))) -q x). 
  rewrite /T (BQinv_opp yq); congr BQopp; apply: (BQinv_K (QS_diff d1q xq)).
rewrite (BQoppB d1q xq) => sa.
have hb:= (QSo (QSs QS1 tq)).
have ha: (exists2 c, inc c BZ & (BQopp (\1q +q BQdouble t)) = BQ_of_Z c).
  exists (BZopp (\1z +z (\2z *z (BQfloor x)))).
    apply:ZSo; apply:(ZSs ZS1 h1).
  by rewrite - BQopp_cZ - (BQsum_cZ ZS1 h1) -(BQprod_cZ ZS2 h0).
move:(f_equal BQ_of_Z (f_equal BQfloor sa)).
rewrite(BQfloor_spec_sum xq ha) => ->.
rewrite - (BQdouble_p tq) (BQsumA QS1 tq tq) (BQoppD (QSs QS1 tq) tq).
rewrite (BQsumA tq hb (QSo tq)) -/ (_ -q _) (BQdiff_sum tq hb) sa.
suff: (\1q +q BQdouble (BQopp (\1q +q t))) = BQopp(\1q +q BQdouble t).
  move => ->; rewrite (BQdiff_diff (QSo d1q) xq d1q) BQsumC /BQdiff. 
  by rewrite (BQsumC _ (BQopp x)) -/(_ -q _) (BQsum_diff d1q (QSo  xq)).
rewrite - {1} (BQopp_K QS1) (BQdouble_opp (QSs QS1 tq)).
rewrite -(BQoppD (QSo QS1) (QSdouble (QSs QS1 tq)))(BQdoubleD QS1 tq).
rewrite (BQsumA (QSo QS1) (QSdouble QS1) (QSdouble tq)).
rewrite (BQsumC (BQopp \1q)) -/(_ -q _) - (BQdouble_p QS1). 
by rewrite (BQdiff_sum QS1 QS1).
Qed.


Lemma rati_lt1 a b (A := BQ_of_Z a)  (B := BQ_of_Z b):
  inc a BZp -> inc b BZps ->
  rat_iterator (A /q (A +q B)) = (A +q B) /q B.
Proof.
move => azp bzps.
have az: intp a by apply:BZp_sBZ.
have bz: intp b by apply:BZps_sBZ.
move:(BQ_of_Z_iQ az)(BQ_of_Z_iQ bz)(BQ_of_Z_iQp azp)(BQ_of_Z_iQps bzps). 
rewrite -/A -/B => aq bq aqp bqps.
have ha: A <q A +q B by apply:(BQsum_Mps aq bqps).
have:inc (A +q B) BQps by apply/ qlt0xP; apply: qle_ltT ha; apply/ qle0xP.
move/BQps_iP => [/BQp_sBQ abq abnz].
rewrite /rat_iterator (BQ_floor_zero aqp ha) /BQdouble (BQprod_0r QS2).
rewrite (BQsum_0r QS1) (BQdiff_div QS1 aq abq abnz).
by rewrite (BQprod_1l abq) (BQdiff_sum aq bq) (BQinv_div bq abq).
Qed.

Lemma rati_gt1 a b (c := (a +z b) -z \2z *z (a %%z b)) 
  (A := BQ_of_Z a) (B := BQ_of_Z b)  (C := BQ_of_Z c):
  inc a BZp -> inc b BZps ->
  (inc c BZps /\ rat_iterator ((A +q B) /q B) =  B /q (B +q C)).
Proof.
rewrite /rat_iterator.
move => azp bzps; move:(BZp_sBZ azp) => az.
move/BZps_iP: (bzps) => [ bzp bnz]; move: (BZp_sBZ bzp) => bz.
move:(BZdvd_correct az bz bnz).
set q := (a %/z b); set r := (a %%z b); move => [qz rzp [eq1]].
rewrite (BZabs_pos bzp) => lt1 /BZp_sBZ rz.
have eq2: (a +z b) = (q +z \1z) *z b +z r. 
    rewrite eq1 BZsumC (BZsumA bz (ZSp bz qz) rz) (BZprodDl bz qz ZS1).
    by rewrite (BZprod_1l bz) (BZsumC b) BZprodC.
move:(BQ_of_Z_iQ az)(BQ_of_Z_iQ bz); rewrite -/A -/B => aq bq.
move:(BQ_of_Z_iQp azp)(BQ_of_Z_iQps bzps); rewrite -/A -/B => aqp bqps.
have fq: ratp ((A +q B) /q B) by apply:QS_div => //; apply:QSs.
have q1z := (ZSs qz ZS1); have q1q:=(BQ_of_Z_iQ q1z).
have eq0: c = (a -z r) +z (b -z r).
  rewrite /c -/r (BZdoublep rz).
  by rewrite(BZsum_ACA az (ZSo rz) bz (ZSo rz))- (BZoppD rz rz).
have czp: inc c BZps.
  rewrite eq0; apply:ZpsS_sum_r; last by apply/zlt0xP; apply/(zlt_diffP1 rz bz).  rewrite eq1 (BZdiff_sum1 rz (ZSp bz qz)). 
  exact: (ZpS_prod bzp(ZpS_quo azp bzp)).
have cz:= (BZps_sBZ czp); have abz:= (ZSs az bz).
have le1: BQ_of_Z (q +z \1z) <=q (A +q B) /q B.  
   apply /(Qdiv_Mlelege1 q1q (QSs aq bq) bqps).
   have ha:= (ZSp q1z bz).
   rewrite (BQsum_cZ az bz) (BQprod_cZ q1z bz).
   apply /(qle_cZ ha abz).
   rewrite eq2;apply:(BZsum_Mp ha rzp).
have le2: (A +q B) /q B <q BQ_of_Z (q +z \1z) +q \1q.
   apply/(Qdiv_Mltltge2 (QSs aq bq) bqps (QSs q1q QS1)).
   rewrite (BQprodDr bq q1q QS1) (BQprod_1r bq).
   apply /(BQsum_lt2r aq (QSp bq q1q) bq).
   rewrite (BQprod_cZ bz q1z); apply/(qlt_cZ az (ZSp bz q1z)).
   rewrite eq1 (BZprodDr bz qz ZS1) (BZprod_1r bz).
   by apply/(BZsum_lt2l rz bz (ZSp bz qz)).
split; first exact.
have ->: (BQfloor ((A +q B) /q B)) = q +z \1z. 
  by symmetry;apply: (BQ_floorp2 fq q1z). 
have ->: (A +q B) /q B = \1q +q A /q B.
  by rewrite (BQsum_div QS1 aq bq (BQps_nz bqps)) (BQprod_1l bq) BQsumC.
move: (QSdouble q1q) => s1q; move: (QSs QS1 s1q) => sq.
have q12z:= (ZSp ZS2 q1z); have q12bz:= (ZSp q12z bz).
rewrite (BQdiff_diff2 sq QS1 (QS_div aq bq)) (BQdiff_sum QS1 s1q).
rewrite (BQdiff_div s1q aq bq (BQps_nz bqps)).
rewrite (BQinv_div (QS_diff (QSp s1q bq) aq) bq).
rewrite /BQdouble (BQprod_cZ ZS2 q1z)(BQprod_cZ q12z bz).
rewrite (BQdiff_cZ q12bz az) (BQsum_cZ bz cz).
congr (B /q (BQ_of_Z _)).
apply: (BZsum_eq2r (ZS_diff q12bz az) (ZSs bz cz) az).
rewrite BZsumC (BZsum_diff az q12bz) (BZsumC _ a) (BZsumA az bz cz).
rewrite (BZsumA abz abz  (ZSo (ZSp ZS2 rz))) - (BZdoublep abz).
rewrite /BZdiff (BZopp_prod_r ZS2 rz) - (BZprodDr ZS2 abz (ZSo rz)).
rewrite - (BZprodA ZS2 q1z bz); congr (\2z *z _).
rewrite (BZsum_AC az bz  (ZSo rz)) eq1 -/(_ -z _) (BZdiff_sum1 rz (ZSp bz qz)).
by rewrite (BZprodDl bz qz ZS1)(BZprod_1l bz) BZprodC.
Qed.


Lemma rati_1: rat_iterator \1q = \2hq.
Proof.
rewrite /rat_iterator (BQfloor_Z ZS1) /BQdouble (BQprod_1r QS2).
by rewrite (BQdiff_sum QS1 QS2) BQinv_2.
Qed.

Lemma fusc_rem n (A :=fusc n) (B :=  fusc (csucc n)) : natp n -> 
   fusc (csucc (csucc n)) +c cdouble (A %%c B) = (A +c B).
Proof.
move:fusc_pr => [Ha Hb Hc Hd]; rewrite /A/B; clear A B;move: n.
apply: fusc_induction.
+ rewrite succ_zero Ha Hb succ_one fusc2 (csum0l CS1) -(crem_small NS1 clt_01).
  by rewrite cdouble0 (csum0r CS1).
+ rewrite succ_one fusc2 fusc3 Hb csum_11 (proj33 (cdivides_one NS1)).
  by rewrite cdouble0 (csum0r CS2).
+ move => k kN _.
  rewrite (Hc _ kN) (Hd _ kN) - (double_succ kN) (Hc _ (NS_succ  kN)).
  move: (NS_fusc (NS_succ  kN)) (NS_fusc kN).
  set u := fusc _; set v := fusc _ => uN vN.
  have lvvu: v <c (v +c u) by apply: (csum_M0lt vN); apply: fusc_nz'.
  by rewrite -(crem_small (NS_sum vN uN) lvvu) csumA csum_nn csumC. 
+ move => k kN;  move: (NS_succ kN)=> sN HR1 _.
  rewrite - (double_succ kN) (Hc _ sN) (Hd _ sN) (Hd _ kN).
  move:(crem_prop (NS_fusc sN) (fusc_nz' kN) NS1  (NS_fusc kN)).
  rewrite (cprod1r (CS_nat (NS_fusc sN))) csumC => ->.
  by rewrite - csumA HR1 csumC.
Qed.


Lemma rat_fusc n: natp n -> rat_iterator (fusc_quo n) = fusc_quo (csucc n).
Proof.
move => nN.
move:fusc_pr => [Ha Hb Hc Hd].
have aux: forall k, natp k -> inc (BZ_of_nat (fusc (csucc k))) BZps.
  move => k kN;move: (NS_succ kN) => skN;apply/BZps_iP; split. 
    by apply:BZ_of_natp_i; apply: NS_fusc.
  move /(BZ_of_nat_inj); apply: (fusc_nz' kN).
case: (equal_or_not n \0c) => nz.
  by rewrite nz succ_zero fusc_quo_0 fusc_quo_1 rati_0.
move:(cpred_pr nN nz); set m := cpred n; move => [mN mv]; rewrite mv.
move:(NS_half (NS_succ mN)) => hN.
case:(even_odd_dichot mN).
+ by move ->; rewrite succ_one fusc_quo_1 fusc_quo_2 rati_1.
+ move => [sa sb].
  move:(NS_succ hN) => shN.
  rewrite /fusc_quo sa - (double_succ hN) (Hd _ hN) (Hc _ hN) (Hc _ shN).
  set A := fusc _; set B := fusc _.
  have aN: natp A by apply: NS_fusc.
  have bN: natp B by apply: NS_fusc.
  move:(BZ_of_nat_i aN)(BZ_of_nat_i bN) => az bz.
  have ->: BQ_of_nat (A +c B) = BQ_of_nat A +q BQ_of_nat B. 
    by rewrite (BQsum_cZ az bz) (BZsum_cN aN bN).
  apply: (rati_lt1 (BZ_of_natp_i aN) (aux _ hN)).
+ move => [sa sb sc].
  move:(NS_succ hN) => shN; move:(NS_succ shN) => sshN.
  rewrite /fusc_quo sa -(double_succ hN) (Hd _ hN)  (Hd _ shN) (Hc _ shN).
  set A := fusc  _; set B := fusc _; set C :=  fusc _.
  have aN: natp A by apply: NS_fusc.
  have bN: natp B by apply: NS_fusc.
  have cN: natp C by apply: NS_fusc.
  move:(BZ_of_nat_i aN)(BZ_of_nat_i bN) (BZ_of_nat_i cN)  => az bz cz.
  have ->: BQ_of_nat (A +c B) = BQ_of_nat A +q BQ_of_nat B. 
    by rewrite (BQsum_cZ az bz) (BZsum_cN aN bN).
  have ap: inc (BZ_of_nat A) BZp by exact (BZ_of_natp_i aN).
  have bp: inc (BZ_of_nat B) BZps by apply: aux.
  have ->: BQ_of_nat (B +c C) = BQ_of_nat B +q BQ_of_nat C. 
    by rewrite (BQsum_cZ bz cz) (BZsum_cN bN cN).
  have r2N:= (NS_double (NS_rem B aN)).
  rewrite (proj2 (rati_gt1 ap bp)) (BZsum_cN aN bN) (BZrem_cN aN bN).
  rewrite - (fusc_rem hN) - (BZsum_cN cN r2N) (BZprod_cN  NS2 (NS_rem B aN)). 
  by rewrite (BZdiff_sum1 (BZ_of_nat_i r2N) cz).
Qed.


End RationalNumbers2.
Export  RationalNumbers2.

(*
Turning and turning in the widening gyre
The falcon cannot hear the falconer;
Things fall apart; the center cannot hold;
Mere anarchy is loosed upon the world,
The blood-dimmer tide is loosed, and everywhere
The ceremony of innocence is drowned;
The best lack all conviction, while the worst
Are full of passoniate intensity.

Surely some revelation is at hand;
Surely the Second Coming is at hand.
The Second Coming! Hardly are those words out
When a vast image out of Spiritus Mundi
Troubles my sight; somewhere in sands of the desert
A shape with lion body and the head of a man
A gaze blank and pitiless as the sun,
Is moving its slow thighs, while all about it 
Reel shadows of the indignant desert birds.
The darkness drops again; but now I know
That twenty centuries of stony sleep
Were vexed to nightmare by a rocking cradle,
And what rough beast, its hour come round at last,
Slouches toward Bethlehem to be born?
     (Yeats, the second coming)
*)