(** * Theory of Sets : Ordinals
  Copyright INRIA (2017-2018) Marelle Team (Jose Grimm).
*)

(* $Id: sset16b.v,v 1.5 2018/09/04 07:57:59 grimm Exp $ *)


Set Warnings "-notation-overridden".
From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Warnings "notation-overridden".

Require Export sset15 sset16a. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SmallOrdinals.

Definition card_15 := nat_to_B 15.
Definition card_8 := nat_to_B 8.
Definition card_13 := nat_to_B 13.
Definition card_19 := nat_to_B 19.

Lemma nat_to_B3: nat_to_B 3 = \3c.
Proof. by rewrite /=  succ_zero succ_one. Qed.

Lemma nat_to_B4: nat_to_B 4 = \4c.
Proof. by rewrite /card_four - nat_to_B3. Qed.

Lemma nat_to_B5: nat_to_B 5 = \5c.
Proof. by rewrite /card_five - nat_to_B4. Qed.

Lemma nat_to_B6: nat_to_B 6 = \6c.
Proof. by rewrite /card_six - nat_to_B5. Qed.

Lemma nat_to_B1: nat_to_B 1 = \1c. Proof. by rewrite /= succ_zero. Qed.

Lemma nat_to_B2: nat_to_B 2 = \2c.
Proof. by rewrite /= succ_zero succ_one. Qed.

Definition nds_k_of n :=
  Yo (n <=c card_8) (cpred n)
     (Yo (n = \9c) \4c (Yo (n = card_13) \6c (Yo (n = card_19) \6c \5c))).

Lemma nds_k_of_v n:
  nat_to_B (Nds.nds_k_of n) = nds_k_of (nat_to_B n).
Proof.
rewrite /Nds.nds_k_of /nds_k_of nat_to_B_ifle; Ytac h; Ytac0; clear h.
  case: n => /=.
    by rewrite cpred0.
  by move => n; rewrite (cpred_pr1 (CS_nat (nat_to_B_Nat n))).
have <-: nat_to_B 9 = \9c. 
 by rewrite /card_nine /card_eight/card_seven - nat_to_B6. 
rewrite - nat_to_B6 - nat_to_B5 - nat_to_B4.
by rewrite - !nat_to_B_ifeq. 
Qed.

Definition ndsC n := csucc (n *c (\2c ^c (cpred n))).
Definition nds_explicit C4 C5 C6 k i :=
  Yo (i = \0c) (C5 ^c k)
    (Yo (i = \1c) (C6 *c C5 ^c (k -c \1c)) 
       (Yo (i = \2c) (C6 ^c \2c *c C5 ^c (k -c \2c))
          (Yo (i = \3c)
              (Yo (k = \1c) (C4 ^c \2c)
                  (Yo (k = \2c) (C4 ^c \2c  *c C5)
                      (C6 ^c \3c *c C5 ^c (k -c \3c))))
              (C4 *c C5 ^c k)))).

Definition nds_sol' n := 
  Yo (n <=c \7c) (ndsC n)
     (nds_explicit (ndsC \4c) (ndsC \5c)(ndsC \6c) (n %/c \5c) (n %%c \5c)). 
Definition nds_sol n := Yo (n = \0c) \1c (nds_sol' (cpred n)).

Lemma ndsC_v n: nat_to_B (Nds.ndsC n) = ndsC (nat_to_B n).
Proof.
rewrite Nds.ndsCE /ndsC; case:n; first by rewrite cprod0l.
move => n /=; rewrite (cpred_pr2 (nat_to_B_Nat n)).
by rewrite nat_to_B_prod nat_to_B_pow /= succ_zero succ_one.
Qed.

Lemma nds_sol_nz n: natp n -> nds_sol (csucc n) = nds_sol' n.
Proof.
by move => nN; rewrite /nds_sol (Y_false (@succ_nz _)) (cpred_pr1 (CS_nat nN)).
Qed.

Lemma nds_sol_v n: nat_to_B (Nds.nds_sol n) =  nds_sol(nat_to_B n).
Proof.
case:n => [ | n]; first by rewrite/nds_sol /= succ_zero; Ytac0.
rewrite (nds_sol_nz (nat_to_B_Nat n)).
rewrite /Nds.nds_sol /Nds.nds_value/nds_sol' /nds_explicit.
have <-: nat_to_B 7 = \7c by rewrite /card_seven - nat_to_B6. 
rewrite nat_to_B_ifle; Ytac h; Ytac0; clear h; first by apply: ndsC_v.
set u4 := Nds.ndsC 4.
set u5 := Nds.ndsC 5.
set u6 := Nds.ndsC 6.
have ->: ndsC \5c = nat_to_B u5 by rewrite ndsC_v nat_to_B5.
have ->: ndsC \6c = nat_to_B u6 by  rewrite ndsC_v nat_to_B6.
have ->: ndsC \4c = nat_to_B u4 by rewrite ndsC_v nat_to_B4.
have NB2:=nat_to_B2. 
have NB3: nat_to_B 3 = \3c by rewrite /= succ_zero succ_one .
rewrite -nat_to_B5 - NB3 - NB2 - nat_to_B1; clear  NB3  NB2.
move: (nat_to_B_quorem n 5) => [<- <-].
rewrite !nat_to_B_ifeq.
pose nbp := nat_to_B_pow; pose nbm:= nat_to_B_prod.
Ytac eq0; Ytac0; first by rewrite nbp.
Ytac eq1; Ytac0; first by rewrite  -nat_to_B_diff subn1 nbm nbp.
Ytac eq2; Ytac0; first by rewrite nbm nbp nbp - subn2  -nat_to_B_diff.
Ytac eq3; Ytac0; last by rewrite nbm nbp.
Ytac eq4; Ytac0; first by rewrite nbp.
by Ytac eq5;Ytac0; rewrite nbm ! nbp -? nat_to_B_diff.
Qed.

Lemma NS_ndsC n: natp n -> natp (ndsC n).
Proof.
move => nN; exact: (NS_succ (NS_prod nN (NS_pow NS2 (NS_pred nN)))).
Qed.

Lemma nds_k_of_bd n: natp n -> \1c <c n ->
  \0c <c nds_k_of n /\ nds_k_of n <c n.
Proof.
move =>  nN np.
move: (B_to_nat_pa nN); set p := (B_to_nat n) => eqa.
have p1: 1 < p by apply/nat_to_B_gt1; rewrite eqa.
move: (Nds.nds_k_of_bd p1) => /andP [/nat_to_B_pos ha /nat_to_B_lt].
by move: ha; rewrite nds_k_of_v eqa.
Qed.

Lemma NS_nds_sol n: natp n -> natp (nds_sol n).
Proof.
move/B_to_nat_pa => <-;rewrite - nds_sol_v; apply: nat_to_B_Nat.
Qed.

Definition nds_fbd f:= forall n k, natp n ->  \2c <=c n ->
     \0c <c k -> k <c n ->
      (ndsC k) *c (f (n -c k)) <=c (f n).
Definition nds_fmax f:= forall n, natp n ->  \2c <=c n ->
   (exists k,  [/\ \0c <c k, k <c n & (ndsC k) *c (f (n -c k)) = (f n)]).

Definition nds_fixpt_eq f := forall n, natp n -> \2c <=c n ->
    f n = \csup (fun_image (Zo Nat (fun k => \0c <c k /\ k <c n ))
       (fun k => (ndsC k) *c (f (n -c k)))). 

Lemma nds_bdmax_nat f:
   [/\ f \0c = \1c, f \1c = \1c, nds_fbd f &  nds_fmax f] ->
   forall n, natp n -> natp (f n).
Proof.
move => [f0 f1 _ fm]; move => n nN; move:(cleR (CS_nat nN)).
move:n nN {1 3}n; apply: Nat_induction.
  move => n /cle0 ->; rewrite f0; apply: NS1.
move =>  n nN Hr p /cle_eqVlt; case; last first.
  move/(cltSleP nN); apply: Hr.
move ->; case: (czero_dichot (CS_nat nN)).
  move ->; rewrite succ_zero f1; apply:NS1.
move => /cge1P np.
move:(NS_succ nN) => nsN.
have np2: \2c <=c csucc n by rewrite - succ_one; apply/cleSS.
move:(fm (csucc n) nsN np2) => [k [/proj2/nesym ka kb <-]]; apply: NS_prod.
  apply:(NS_ndsC (NS_lt_nat kb nsN)).
apply: Hr; apply/(cltSleP nN); apply:(cdiff_ltb nsN (proj1 kb) ka).
Qed.
  
Lemma nds_bdmax_nat' f:
   [/\ f \0c = \1c, f \1c = \1c &  nds_fixpt_eq f] ->
   forall n, natp n -> natp (f n).
Proof.
move => [f0 f1 fe]; move => n nN; move:(cleR (CS_nat nN)).
move:n nN {1 3}n; apply: Nat_induction.
  move => n /cle0 ->; rewrite f0; apply: NS1.
move =>  n nN Hr p /cle_eqVlt; case; last first.
  move/(cltSleP nN); apply: Hr.
move ->; case: (czero_dichot (CS_nat nN)).
  move ->; rewrite succ_zero f1; apply:NS1.
move => /cge1P np.
move:(NS_succ nN) => nsN.
have np2: \2c <=c csucc n by rewrite - succ_one; apply/cleSS.
rewrite (fe _ nsN np2).
set I := Zo _ _; set E := fun_image _ _.
have EN: sub E Nat.
  move=> t /funI_P [k /Zo_P[ka [kb kc]] ->]; apply:(NS_prod (NS_ndsC ka)).
  apply: Hr;apply/(cltSleP nN); apply:(cdiff_ltb nsN (proj1 kc)).
  exact: (nesym (proj2 kb)).
have fsE: finite_set E.
  have hu: sub I (csucc n) by move => t /Zo_P [_ [_] /(NltP nsN) ].
  apply:(finite_fun_image  _ (sub_finite_set hu (finite_set_nat nsN))).
have neE: nonempty E.
  apply:funI_setne; exists \1c; apply: (Zo_i NS1); split; fprops.
  by apply/cltSleP.
move:(finite_subset_Nat EN fsE neE) => [m /EN me mg].
exact:(NS_le_nat (card_ub_sup (CS_nat me) mg) me).
Qed.

Lemma nds_max_bd_prop f:
   [/\ f \0c = \1c, f \1c = \1c, nds_fbd f &  nds_fmax f] <->
   [/\ f \0c = \1c, f \1c = \1c & nds_fixpt_eq f].
Proof.
split.
  move => ha.
  have fN:= (nds_bdmax_nat ha).
  move: ha => [f0 f1 fb fm]; split => // n nN  ge2.
  have ln1: \1c <c n by  apply/(cleSltP NS1); rewrite succ_one.
  set I := Zo _ _; set E := fun_image _ _.
  apply: cleA.
    have csE: cardinal_set E by move => t /funI_P [ k _ ->]; fprops.
    move: (fm _ nN ge2) => [k [ka kb kc]].
    apply: (card_sup_ub csE); apply/funI_P; exists k => //.
    by apply/Zo_P; split => //; apply(NS_lt_nat kb nN).
  apply:(card_ub_sup (CS_nat (fN _ nN))) => x /funI_P [k /Zo_P [ka [kb kc]] ->].
  exact:(fb n k nN ge2 kb kc).
move => ha.
suff: forall n, natp n -> \2c <=c n ->
  (forall k, \0c <c k -> k <c n -> ndsC k *c f (n -c k) <=c f n) /\ 
  (exists k, [/\ \0c <c k, k <c n & ndsC k *c f (n -c k) = f n]).
  move: ha => [f0 f1 fre] h; split => //.
    by move => n k ha hb hc hd; apply:(proj1 (h n ha hb)).
  move => n ha hb; exact:(proj2 (h n ha hb)).
move => n nN ne2.
move:(proj33 ha n nN ne2).
set I := Zo _ _; set E := fun_image _ _ => ->.
have csE: cardinal_set E by move => t /funI_P [ k _ ->]; fprops.
split.
  move => k lp lkn.
  apply:(card_sup_ub csE); apply/funI_P; exists k => //.
  apply/Zo_P; split => //; apply: (NS_lt_nat lkn nN). 
have fn:= (nds_bdmax_nat' ha).
have l1n: \1c <c n by apply/(cleSltP NS1); rewrite succ_one.
have EN: sub E Nat.
  move=> t /funI_P [k /Zo_P[ka [kb kc]] ->]; apply:(NS_prod (NS_ndsC ka)).
  apply(fn _ (NS_diff _ nN)).
have fsE: finite_set E.
  have hu: sub I n by move => t /Zo_P [_ [_] /(NltP nN) ].
  apply:(finite_fun_image  _ (sub_finite_set hu (finite_set_nat nN))).
have neE: nonempty E.
  apply:funI_setne; exists \1c; apply: (Zo_i NS1); split; fprops.
move:(finite_subset_Nat EN fsE neE) => [m me mg].
have ->: \csup E = m.
apply:cleA; last exact:(card_sup_ub csE me).
  apply:(card_ub_sup (CS_nat (EN _ me)) mg).
by move/(funI_P):me => [k /Zo_P[kN [ka kb]] ->]; exists k. 
Qed.

Lemma nds_sol_fix_pt (f := nds_sol):
   [/\ f \0c = \1c, f \1c = \1c & nds_fixpt_eq f].
Proof.
apply/ nds_max_bd_prop.
move:nds_sol_v => H.
split.
- by rewrite /f /nds_sol; Ytac0.
- by rewrite - nat_to_B1 /f- (H 1) Nds.nds_sol1.
- move => n k nN n2 kp kn.
  have kv:= (B_to_nat_pa (NS_lt_nat kn nN)).
  have nv :=(B_to_nat_pa nN).
  move: n2 kp kn; rewrite -kv -nv;set K := (B_to_nat k); set N := (B_to_nat n).
  rewrite - nat_to_B2.
  move  => /nat_to_B_le ln1 /nat_to_B_pos kp /nat_to_B_lt lkn. 
  have l0kn:  0 < K < N by rewrite kp lkn.
  rewrite /f - H - nat_to_B_diff - H - ndsC_v - nat_to_B_prod.
  apply/nat_to_B_le; exact: (Nds.nds_sol_bd ln1 l0kn).
move => n nN n2.
move:(B_to_nat_pa nN); set  N := (B_to_nat n) => nv.
move: n2; rewrite - nat_to_B2 - nv => /nat_to_B_le ln1.
move:(Nds.nds_sol_max ln1) => [k /andP [/nat_to_B_pos kp /nat_to_B_lt lkn] eq].
exists (nat_to_B k); split => //.
by rewrite - nat_to_B_diff / f -H -H -ndsC_v -nat_to_B_prod - eq.
Qed.

Lemma nds_sol_Bourbaki_conc (f := nds_sol):
  forall n, natp n -> card_15 <=c n -> 
      f(n +c \5c) = (ndsC \5c) *c f n. 
Proof.
move => n nN.
move:(B_to_nat_pa nN); set N := (B_to_nat n) => nv.
rewrite - nv - nat_to_B5 - nat_to_B_sum /f - nds_sol_v  - nds_sol_v.
move/nat_to_B_le/ Nds.nds_sol_rec5 => ->.
by rewrite - ndsC_v nat_to_B_prod.
Qed.


Lemma nds_k_of_prop f:
   f \0c = \1c -> f \1c = \1c -> 
   (forall n, natp n -> \1c <c n ->
              f n = ndsC (nds_k_of n) *c f (n -cnds_k_of n)) ->
   forall n, natp n ->  f n = nds_sol n.
Proof.
move => f0 f1 hb.
have hc: forall n, natp n -> natp (f n).
  move => n nN; move: {1 3}(n) (cleR (CS_nat nN)); move: n nN.
  apply:Nat_induction.
    move => n /cle0 ->; rewrite f0; apply: NS1.
  move => n nN Hr p; move/cle_eqVlt; case; last first.
    move/(cltSleP nN); apply: Hr.
  move ->; case: (czero_dichot (CS_nat nN)) => nz. 
      rewrite nz succ_zero f1; apply: NS1.
  have sn1: \1c <c csucc n by rewrite  - succ_zero; apply/cltSS.
  have snN := NS_succ nN.
  move:(nds_k_of_bd snN sn1) => [qa qb].
  have kN:=(NS_lt_nat qb snN).
  rewrite(hb _ snN sn1); apply: (NS_prod (NS_ndsC kN)).
  move:(cdiff_ltb snN (proj1 qb) (nesym (proj2 qa))) => /(cltSleP nN) le1.
  exact: (Hr _ le1). 
pose g n := B_to_nat (f (nat_to_B n)).
have hd n: f (nat_to_B n) = nat_to_B(g n).
  by rewrite /g (B_to_nat_pa (hc _ (nat_to_B_Nat n))).
have g1: g 1 = 1 by rewrite /g  /= succ_zero f1 - nat_to_B1 B_to_nat_pb.
have g0: g 0 = 1 by rewrite /g  /= f0 - nat_to_B1 B_to_nat_pb.
have gn: forall n,
     1 < n -> g n = Nds.ndsC (Nds.nds_k_of n) * g (n - Nds.nds_k_of n).
  move => n ln1; rewrite /g.
  move: (Nds.nds_k_of_bd ln1) => /andP [he hf].
  move/nat_to_B_gt1:(ln1) => ln2.
  rewrite  (hb (nat_to_B n) (nat_to_B_Nat n) ln2).
  rewrite - (nds_k_of_v n) - nat_to_B_diff - ndsC_v.
  set u := (n - Nds.nds_k_of n).
  have fN: natp (f (nat_to_B u)) by apply: (hc _ (nat_to_B_Nat u)).
  by rewrite -{1} (B_to_nat_pa fN) - nat_to_B_prod B_to_nat_pb.
move: (Nds.nds_value_prop g0 g1 gn) => gp.
move => n nN.
rewrite - (B_to_nat_pa nN) - nds_sol_v hd.
by case: (B_to_nat n); [   rewrite Nds.nds_sol0 g0 | move => m; rewrite gp].
Qed.

Lemma nds_alt f: 
  f \0c = \1c -> f \1c = \1c ->
  (forall n, natp n -> \1c <c n ->
     exists k, [/\ \0c <c k, k <c  n & f n <=c (ndsC k) *c f (n -c k)]) ->
  (forall n, natp n -> nds_sol (csucc n) <=c f (csucc n)) ->
  (forall n, natp n -> f n = nds_sol n).
Proof.
move => f0 f1 hf1 hf2.
have hc: forall n, natp n -> natp (f n).
  move => n nN; move: {1 3}(n) (cleR (CS_nat nN)); move: n nN.
  apply:Nat_induction.
    move => n /cle0 ->; rewrite f0; apply: NS1.
  move => n nN Hr p; move/cle_eqVlt; case; last first.
    move/(cltSleP nN); apply: Hr.
  move ->; case: (czero_dichot (CS_nat nN)) => nz. 
      rewrite nz succ_zero f1; apply: NS1.
  have sn1: \1c <c csucc n by rewrite - succ_zero; apply/cltSS.
  have snN := NS_succ nN.
  move:(hf1 _ snN sn1) => [k [ka kb kc]].
  move:(cdiff_ltb snN (proj1 kb) (nesym (proj2 ka))) => /(cltSleP nN) le1.
  apply: (NS_le_nat kc); apply: (NS_prod (NS_ndsC (NS_lt_nat kb snN))).
  by apply: Hr.
pose g n := B_to_nat (f (nat_to_B n)).
have hd n: f (nat_to_B n) = nat_to_B(g n).
  by rewrite /g (B_to_nat_pa (hc _ (nat_to_B_Nat n))).
have g1: g 1 = 1 by rewrite /g  /= succ_zero f1 - nat_to_B1 B_to_nat_pb.
have g0: g 0 = 1 by rewrite /g  /= f0 - nat_to_B1 B_to_nat_pb.
have gp2: forall n,  Nds.nds_sol n.+1 <= g n.+1.
  move => n; apply/nat_to_B_le; rewrite - hd nds_sol_v /=; apply: hf2.
  by apply: nat_to_B_Nat.
have gp1:forall n,
     1 < n -> exists2 k, 0 < k < n & g n <= Nds.ndsC k * g (n - k).
  move => n /nat_to_B_lt; rewrite nat_to_B1 => np.
  have nN := (nat_to_B_Nat n).
  move: (hf1 _ nN np) => [k [ka kb kc]].
  move: (B_to_nat_pa (NS_lt_nat kb nN)) => kv.
  exists (B_to_nat k).
    apply/andP; split; [ apply/nat_to_B_pos; ue | apply/nat_to_B_lt; ue].
  apply/nat_to_B_le; rewrite /g nat_to_B_diff kv (B_to_nat_pa (hc _ nN)).
  by rewrite nat_to_B_prod ndsC_v kv (B_to_nat_pa  (hc _ (NS_diff _ nN))).
move: (Nds.nds_alt g0 g1 gp1 gp2) => OK.
move => n /B_to_nat_pa <-.
case:  (B_to_nat n); first by rewrite  /= f0 /nds_sol; Ytac0.
by move => k; rewrite - nds_sol_v OK //.
Qed.

(* Study of the Bourbaki function  *)


Definition nds_sc (X: fterm) n g := osumf (fun z => (X (Vf g z))) n. 

Definition nds_sums (X: fterm) n := fun_image (permutations n) (nds_sc X n).

Definition nds_card (X: fterm) n := cardinal (nds_sums X n).

Definition nds_ax := ord_below.

Lemma nds_card_bd X n: natp n -> nds_card X n <=c (factorial n).
Proof.
move=> nN.
rewrite -{2} (card_nat nN) -(card_permutations (finite_set_nat nN)).
apply: fun_image_smaller. 
Qed.

Lemma nds_ax_perm X n f: natp n -> nds_ax X n -> 
   inc f (permutations n) ->
   (nds_ax (fun z => X (Vf f z)) n  /\ ordinalp (nds_sc X n f)).
Proof.
move=> nN ax => /Zo_P [ /functionsP [ff sf tf] bf].
have pc: nds_ax (fun z => X (Vf f z)) n.
  move => t /(NltP nN) tn; apply: ax; apply/(NltP nN); Wtac. 
by split => //; apply: OS_osumf.
Qed.

Lemma nds_sc_exten X X' n f: 
  natp n -> (same_below X X' n) -> 
  inc f (permutations n) ->
  nds_sc X n f = nds_sc X' n f.
Proof.
move => nN h /Zo_P [ /functionsP [fg sg tg] bg ];apply: (osumf_exten nN).
move => i /(NltP nN) ia; apply: h; apply/(NltP nN); Wtac.
Qed.

Lemma nds_sums_exten Y1 Y2 m: natp m -> same_below Y1 Y2 m ->
   nds_sums Y1 m = nds_sums Y2 m. 
Proof.
move => ha hb;set_extens t; move => /funI_P [z zp ->];apply/funI_P; ex_tac. 
  by apply:nds_sc_exten.
by symmetry;apply:nds_sc_exten.
Qed.

Lemma nds_card_exten Y1 Y2 m: natp m -> same_below Y1 Y2 m ->
   nds_card Y1 m = nds_card Y2 m. 
Proof.
by move => ha hb; rewrite /nds_card (nds_sums_exten ha hb).
Qed.

Lemma nds_card_perm_inv X n g:
  natp n -> nds_ax X n -> inc g (permutations n) -> 
  nds_card X n = nds_card (fun z => X (Vf g z)) n.
Proof.
move => nN ax /Zo_P [] /functionsP [fg sg tg] bg.
rewrite /nds_card /nds_sums; apply: f_equal.
set E := permutations n.
set_extens t; move /funI_P => [z ze ->]; apply /funI_P.
  move: (inverse_bij_fb bg) => ibg.
  move: ze =>/permutationsP [bz sz tz]; move:(proj1 (proj1 bz)) => fz.
  have fa: (inverse_fun g) \coP z by hnf;aw;split => //; [fct_tac | ue].
  have fb: function  ((inverse_fun g) \co z) by fct_tac.
  exists ((inverse_fun g) \co z).
  apply: Zo_i; [ apply /functionsP;red;saw | by apply compose_fb ].
  apply:(osumf_exten nN) => i lin.
  have iz: inc i (source z)  by rewrite sz; apply /(NltP nN i).
  have cp: inverse_fun g \coP z by split; [ fct_tac | exact | aw; ue].
  have fzy: inc (Vf z i) (target g) by rewrite tg - tz; Wtac.
  by rewrite (compfV cp iz) (inverse_V bg fzy).
move: ze => /permutationsP [bz sz tz]; move:(proj1 (proj1 bz)) => fz.
have fa: g \coP z by red;saw; ue.
have fb: function  (g \co z) by fct_tac.
exists (g \co z).
  apply: Zo_i; [ apply /functionsP;red;saw | by apply compose_fb ].
apply:(osumf_exten nN) => i lin.
by rewrite compfV // sz; apply/(NltP nN i).
Qed.

Lemma NS_nds_card X n: natp n -> natp (nds_card X n).
Proof.
move=> nN;exact:(NS_le_nat (nds_card_bd X nN) (NS_factorial nN)).
Qed.

Lemma nds_card_0 X: nds_card X \0c = \1c.
Proof.
apply: cleA.
  by move: (nds_card_bd X NS0); rewrite factorial0.
by apply/cle1P; apply:funI_setne; exists (identity \0c); apply:permutation_id.
Qed.

Lemma nds_card_1 X: nds_card X \1c = \1c.
Proof.
apply: cleA.
  by move: (nds_card_bd X NS1); rewrite factorial1.
by apply/cle1P; apply:funI_setne; exists (identity \1c); apply:permutation_id.
Qed.

Definition opos_below (f : fterm) n := forall k, k <c n -> \0o <o (f k).

Lemma osum_negl_recd X n: natp n -> opos_below X (csucc n) -> 
  (forall i, i<c n -> odegree (X (csucc i)) <o odegree (X \0c)) ->
  osumf X (csucc n) = X \0c.
Proof.
move => nN ha hb.
move:(ha _ (succ_positive n)) => pa; move :(proj32_1 pa) => pb.
move: n nN ha hb; apply: Nat_induction; first by rewrite succ_zero osum_f1.
move => n nN Hrec /(true_below_rec (NS_succ nN)) [qa qb].
move /(true_below_rec nN) => [qc qd].
by rewrite (osum_fS _ (NS_succ nN)) (Hrec qa qc); apply: ord_negl_p7.
Qed.

Lemma osum_negl_rec n e X: ordinalp e ->  X \0c = oopow e -> natp n ->
  (forall i, i<c n -> X (csucc i) <o oopow e) ->
  osumf X (csucc n) = oopow e.
Proof.
move => oe x0.
move: (OS_oopow oe) => oope.
move: n; apply: Nat_induction.
  by move => _; rewrite  succ_zero osum_f1 // x0.
move => n nN Hrec /(true_below_rec nN) [qa qb].
rewrite (osum_fS _ (NS_succ nN)) (Hrec qa).
by apply: ord_negl_opow.
Qed.

Lemma nds_card_different_deg_gen X n: natp n ->
  opos_below X (csucc n) -> 
  (forall i j, i <c j -> j <=c n -> odegree (X i) <o odegree (X j)) ->
  nds_ax X (csucc n) /\ nds_card X (csucc n) =  \2c ^c n.
Proof.
move => nN xp  xmon; move: (NS_succ nN) => sN.
have ax: nds_ax X (csucc n) by move => i /xp / proj32_1.
split => //.
move:(NleP nN) (NltP sN) => Ka Kb.
rewrite - card_setP; set E := \Po n; set F := (\Po (csucc n)).
pose Pe n := (permutations (csucc n)).
have Kc s i: inc s (Pe n) -> i <=c n -> Vf s i <c (csucc n).
  move/permutationsP => [[[fp _] _] ss ts] /Ka ins; apply/Kb; Wtac.
have Kc' s i: inc s (Pe n) -> i <=c n -> Vf s i <=c n.
  by move => h /(Kc _ _ h) /(cltSleP nN).
have Kd f i j: inc f (Pe n) -> i <=c n -> j <=c n ->
     Vf f i = Vf f j -> i = j.
  move/permutationsP => [[[_ h] _] sf _] /Ka isn /Ka jsn; apply:h; ue.
have Hb1 k s: k <=c n -> inc s (Pe n) -> Vf s k = n ->
   let s2 := nds_sc X k s in 
    ordinalp s2 /\ nds_sc X (csucc n) s = (X n) +o s2.
  move => lkn sp  sk; rewrite /nds_sc.
  set s2 := osumf (fun z => oopow (Vf s z)) k.
  have kN:= (NS_le_nat lkn nN).
  move: (cdiff_pr lkn) (NS_diff k nN); set m := n -c k => mp mN.
  have eq1 : k +c (csucc (n -c k)) = csucc n by rewrite (csum_nS _ mN) mp.
  move:(nds_ax_perm sN ax sp); rewrite - eq1; move=> [sax oo1].
  rewrite(osum_fA kN  (NS_succ mN) sax) -/s2.
  split; last (apply: f_equal2; last exact).
    apply: (OS_osumf kN) => i li; apply: ax; apply/ (Kc _ _ sp).
    by apply: (cleT (proj1 li) lkn).
  have qa: opos_below (fun z => X (Vf s (z +c k))) (csucc m).
    move => i il1; apply: xp;apply: (Kc _ _ sp).
    by rewrite - mp csumC; apply: csum_Meqle; apply/cltSleP.
  rewrite (osum_negl_recd mN qa) ? (Nsum0l kN) ? sk //.
  move => i lim; apply: (xmon _ _  _ (cleR (CS_nat nN))).
  have iN := (NS_lt_nat lim mN).
  have pa: (csucc i +c k)  <=c n.
    by rewrite - mp csumC; apply(csum_Meqle); apply/(cleSltP iN).
  move: (Kc'  _ _ sp pa) =>  /cle_eqVlt; rewrite - sk;case => //.
  move / (Kd s _ k sp pa lkn). rewrite -{2} (Nsum0l kN).
  by move/(csum_eq2r kN (NS_succ iN) NS0) =>h; case:(@succ_nz i).
pose ii f := Vf (inverse_fun f) n. 
pose pa f k := forall i j, i<c j -> j <c k -> f i <c f j.
pose mxi f := \csup (Zo (csucc (csucc n)) (pa (Vf f))).
have mxia f: let k := (mxi f) in inc f (Pe n) ->
   [/\ natp k, \0c <c k, k <=c csucc n, pa (Vf f) k &
       k = (csucc n) \/ Vf f k <c Vf f (cpred k)].
  move => k fp.
  set T := (Zo (csucc (csucc n)) (pa (Vf f))).
  have qa i: inc i T -> i <=c csucc n by move => /Zo_S /(NleP sN).
  move:(Nat_sup_pr sN qa); rewrite /T -/(mxi _) -/k => - [ra rb rc rd]. 
  have zT: inc \1c T.
    apply/Zo_P; split.
     by rewrite - succ_zero; apply/(NleP sN); apply:cleSS; apply:cle0n.
    by move => i j lij /clt1 ej0; move: lij; rewrite ej0 => /clt0.
  move: (rc _ zT) => /cge1P kp. 
  have re: inc k T by case: rd => // /set0_P => h;case: (h \1c). 
  move/Zo_P: re => [_ re].
  split => //.
  case /cle_eqVlt: rb; [ by left | move =>  ll; right].
  case: (p_or_not_p (pa (Vf f) (csucc k))) => hpa.
    have: (inc (csucc k)) T.
      by apply: Zo_i => //; apply/ (NleP sN); apply/cleSltP.
    by move/rc /cltNge; case; apply: cltS.
  ex_middle h.
  case: hpa => i j lij /(cltSleP ra) /cle_eqVlt; case; last by apply: re.
  move => jv.
  case: (equal_or_not k \0c) => knz; first by move:lij;rewrite jv knz => /clt0.
  move: (cpred_pr ra knz) =>[pN pv]. 
  have tN x: x <=c n ->  natp (Vf f x).
    move/(Kc' _ _ fp) => hw; apply/(NS_le_nat hw nN).
  have l3: cpred k <c k by rewrite {2} pv; apply: cltS.
  move/(cltSleP nN): ll => ksf; move: (cleT (proj1 l3) ksf) => pksf.
  case: (NleT_ell (tN _ ksf) (tN _ pksf)).
      by move/(Kd _ _ _ fp ksf pksf) => h'; case:(proj2 (cltS pN)); ue.
    done.
  move: lij; rewrite jv {1} pv => /(cltSleP pN); case /cle_eqVlt.
     by move ->.
  move => lipk l4; exact: (clt_ltT (re i (cpred k) lipk l3) l4).
have mxib f k i: inc f (Pe n) -> pa (Vf f) k -> k <=c csucc n -> 
    i <c k -> i <=c Vf f i.
   move => fp pak lkn lik.
   move: (NS_lt_nat (clt_leT lik lkn) sN) => iN.   
   move/permutationsP: fp => [[[ff injf] sjf] sf tf].
   move: i iN lik; apply: Nat_induction.
     move => w; move /(NltP sN): (clt_leT w lkn).
     rewrite - sf =>/(Vf_target ff); rewrite tf => /(NleP nN).
    by move/proj31 => cc; apply:(cle0x cc).
  move => i iN Hrec lei; move: (cltS iN) => liN.
  apply/(cleSltP iN); apply: (cle_ltT (Hrec (clt_ltT liN lei))).
  exact: (pak i (csucc i) liN lei).
have mxic f: inc f (Pe n) -> mxi f = csucc n -> Vf f n = n.  
  move => fp; move: (mxia f fp) => [kN kp ksn pak _] eksn.
  apply: cleA;first by apply/(Kc' _ _ fp (cleR (CS_nat nN))).
  by apply: (mxib _ _ _ fp pak ksn); rewrite eksn; apply: cltS.
have iip f: inc f (Pe n) -> [/\ Vf f (ii f) = n, ii f <=c n & 
     forall x, x <=c n -> Vf f x = n -> x = ii f].
  move/permutationsP  =>[ bf sf tf]; move: (Nsucc_i nN) => h.
  have fk1: Vf f (ii f) = n.
    by rewrite /ii (inverse_V bf) //; rewrite tf.
  have lt2: (ii f) <=c n.
    apply/Ka; rewrite - sf.
    by apply: (inverse_Vis bf); rewrite tf.
   rewrite -{4} fk1; split=> //  x fx.
   by apply/(proj2 (proj1 bf)); rewrite sf; apply/Ka.
have mxid f: inc f (Pe n) -> Vf f (cpred (mxi f)) <c n
     -> exists f', [/\ inc f' (Pe n), ii f' <c ii f &
   nds_sc X (csucc n) f  = nds_sc X (csucc n) f' ].
  move => fp le1.
  move: (mxia f fp); set k := mxi f; move => [kN kp ksn pak aux].
  have nkn: k = csucc n -> False.
    move => h;case: (proj2 le1); rewrite -/k h (cpred_pr1 (CS_nat nN)).
    by apply: mxic.
  case: aux => lt1; first by case: nkn.
  case: (cle_eqVlt ksn);[ by move => h;case nkn| move/(cltSleP nN) => lekn].
  case: (iip _ fp); set k1 := ii f => fk1 lt2 etc.
  move/permutationsP: (fp) => [bf sf tf]. 
  have ff := (proj1 (proj1 bf)).
  move: (cpred_pr kN (nesym (proj2 kp))) =>[pN pv].
  have lt3: cpred k <=c n.
    by apply/(cleSSP (CS_nat pN) (CS_nat nN)); rewrite - pv.
  case: (cleT_ell (proj31 lt2) (proj31 ksn)) => lt4.
      by move:lt1; rewrite - {1} lt4 fk1 => /cltNge; case; apply: Kc'.
    move: lt4; rewrite pv => /(cltSleP pN); case/cle_eqVlt => lt5.
      by case: (proj2 le1); rewrite -/k; rewrite - lt5.
    move: (cltSS lt5); rewrite - pv => lt6.
    move: (pak k1 (csucc k1) (cltS (NS_le_nat lt2 nN)) lt6); rewrite fk1.
    case /cltNge; apply: (Kc' _ _ fp (cleT (proj1 lt6) lekn)).
  pose f1 i :=  Yo (i <c k) (Vf f i) (Yo (i <c k1) (Vf f (csucc i))
     (Yo (i = k1) (Vf f k) (Vf f i))).
  have ax1: lf_axiom f1 (csucc n) (csucc n).
    have ksf: inc k (source f) by rewrite sf; apply/NleP.
    move => i lin; rewrite /f1; Ytac qa; [ Wtac | Ytac qb; last Ytac qc; Wtac].
    move: (clt_leT qb lt2) => likn.
    by rewrite sf; apply/(NleP nN); apply/(cleSltP (NS_lt_nat likn nN)). 
  pose f2 := Lf  f1 (csucc n) (csucc n). 
  have sjf2: surjection f2.
    apply: (lf_surjective ax1) ; rewrite -{1} tf => y /(proj2(proj2 bf)).
    move => [i isf ->]; rewrite sf in isf.
    have iN := (NS_inc_nat sN isf). 
    rewrite /f1.
    case: (NleT_el kN iN) => lt5; last by exists i => //; Ytac0.
    move: (cleNgt lt5) => lt54.
    case: (cle_eqVlt lt5) => lt6.
      exists k1; first by apply/Ka.
      Ytac0; rewrite (Y_false(cleNgt (proj1 lt4))) - lt6 Y_false => //.
      by case.
    have k1N := NS_le_nat lt2 nN.
    case: (NleT_el iN k1N) => lt7; last first.
       by move: lt7=> [/cleNgt qa qb]; exists i => //;Ytac0; Ytac0; Ytac0.
    have inz: i <> \0c by move => iz;move: lt6; rewrite iz => /clt0.
    move: (cpred_pr iN inz) =>[jN jv].
    have lt8: cpred i <c i by rewrite {2} jv; apply: cltS.
    exists  (cpred i); first by apply/Ka; apply: (cleT (proj1 lt8)); apply/Ka.
    rewrite (Y_true (clt_leT lt8 lt7)) -jv Y_false //; apply: cleNgt.
    by apply /(cltSleP jN); rewrite - jv.
  have bf2: bijection f2.
    rewrite /f2; apply:bijective_if_same_finite_c_surj; aw; trivial.
    apply: (finite_set_nat sN).
  have f2p: inc f2 (Pe n). 
    by rewrite/f2;apply/permutationsP; saw.
  move: (cpred_pr (NS_le_nat lt2 nN) (card_gt_ne0 lt4)) => [k2N k2v].
  move: (cltS k2N); rewrite - k2v => lt9.
  move: (cleT (proj1 lt9) lt2) => le10.
  have qa: inc (cpred k1) (csucc n) by apply/Ka.
  move: lt4; rewrite {1} k2v => /(cltSleP k2N) => lt10.
  have f2sk: Vf f2 (cpred k1)  = n.
    move /cleNgt: lt10 => lt10.
    by rewrite /f2 LfV//; rewrite /f1; Ytac0; Ytac0; rewrite - k2v. 
  have iif2 : ii f2 <c k1.
    have qb: inc (cpred k1) (source f2) by  rewrite /f2; aw.
    by move: (inverse_V2 bf2 qb); rewrite /ii f2sk => ->.
  exists f2; split => //.
  move: (cdiff_pr lt10) (NS_diff k k2N); set k2 := _ -c _ => eqa d1N.
  move: (Hb1 _ _ lt2 fp fk1) => [os1 ->].
  move: (Hb1 _ _ le10 f2p f2sk) => [os2 ->]; apply: f_equal.
  rewrite /nds_sc.
  set Y1 :=  (fun z : Set => X (Vf f z)).
  set Y2 :=  (fun z : Set => X (Vf f2 z)).
  have Ke i: i <=c  n -> ordinalp (Y1 i).
    by move => iln; move: (proj32_1 (xp _ (Kc _ _ fp iln))).
  have ax3: nds_ax Y1  k1.
    move => i lik; apply: (Ke _ (cleT (proj1 lik) lt2)).
    have ax4: nds_ax (fun z => Y1 (z +c k)) (csucc k2).
     move => i /(cltSleP d1N) lik; apply:Ke.
     move:(csum_Meqle k lik); rewrite csumC eqa => qc; apply: (cleT qc le10).
  have ax2: nds_ax Y2 (cpred k1). 
    move => i lin. move: (cleT (proj1 lin) le10) => /Ka lt12.
    by rewrite /Y2/f2 LfV//;move/(NltP sN):(ax1 _ lt12) => /xp/proj32_1.
  rewrite - eqa in ax2. 
  rewrite - eqa (osum_fA kN d1N ax2).
  have eqc : k +c (csucc k2) = k1 by  rewrite k2v - eqa csum_nS.
  rewrite - eqc in ax3.
  rewrite - eqc (osum_fA kN (NS_succ d1N) ax3). 
  rewrite (osum_f1r d1N ax4) (csum0l (CS_nat kN)).
  set U := osumf (fun i => Y1 (csucc i +c k)) k2.
  have ->: osumf (fun z  => Y2 (z +c k)) k2 = U.
    apply: (osumf_exten d1N) => i lik; rewrite /Y1 /Y2 /f2/f1.
    have lt11:  i +c k <c k1.
      apply: clt_ltT lt9; rewrite - eqa csumC; apply: (csum_Meqlt kN lik).
    move/Ka: (cleT (proj1 lt11) lt2) => lt13.
    move:(cleNgt  (csum_Mle0 i (CS_nat kN))) => lt12.
     by rewrite LfV//; Ytac0; Ytac0; rewrite (csum_Sn _ (NS_lt_nat  lik d1N)).
   have y1kp: \0o <o Y1 k by apply: xp; apply/(Kc _ _ fp).
   have y1pkp: \0o <o Y1 (cpred k) by  apply: xp; apply/(Kc _ _ fp). 
   have oU: ordinalp U.
     apply: OS_osumf => // i lin; apply: ax3; rewrite csumC.
     by apply: (csum_Meqlt kN); apply: cltSS.
   have oy1 := (proj32_1 y1kp).
   have oy3 := (proj32_1 y1pkp).
   have oy2: ordinalp (osumf Y1 k).
     by apply: (OS_osumf kN) => i lin; apply: (Ke _ (cleT (proj1 lin) lekn)).
   have oy4:  ordinalp (osumf Y1 (cpred k)).
     apply: (OS_osumf pN) => i lin; exact: (Ke _ (cleT (proj1 lin) lt3)).
   rewrite - (osumA oU oy1 oy2); apply: f_equal.
   have ->:  osumf Y2 k =  osumf Y1 k.
      apply: (osumf_exten kN) => i lik; rewrite /Y1 /Y2 /f2/f1.
      rewrite LfV//; [ by Ytac0 | apply/Ka; apply: (cleT (proj1 lik) lekn)].
   rewrite {2 3} pv (osum_fS _ pN). 
   rewrite (osumA oy1 oy3 oy4).
   have lt12: Vf f (cpred k) <=c n by apply/Kc'.
   by rewrite (ord_negl_p7 y1kp y1pkp (xmon _ _ lt1 lt12)).
have mixe f: inc f (Pe n) -> exists f', [/\ inc f' (Pe n),    
   pa (Vf f') (ii f') &  nds_sc X (csucc n) f = nds_sc X (csucc n) f' ].
   move => hyp.
  set T := Zo (Pe n) (fun s => nds_sc X (csucc n) f = nds_sc X (csucc n) s).
  suff: exists2 f', inc f' T &  pa (Vf f') (ii f').
     by move => [s /Zo_P  [qa qb] qc]; exists s.
  have hu s: inc s T -> Vf s (cpred (mxi s)) <c n ->
    exists2 s', inc s' T & ii s' <c ii s.       
    move => /Zo_P [sa sb] sc; move: (mxid _ sa sc) => [s' [sd se sf]].
    by rewrite /T;exists s' => //; rewrite sb sf; apply Zo_i.
  set W := fun_image T ii.
  have neW: nonempty W by apply: funI_setne; exists f; apply/Zo_i.
  have sWn: sub W Nat.
   by move => y /funI_P [s /Zo_P [/iip [_ qa _] _] ->];apply: (NS_le_nat qa nN).
  move: (inf_Nat sWn neW); set im := intersection _; move => [mW iml].
  move: mW =>/funI_P[s sT sm].
  move/Zo_P: (sT) =>  [qa qb].
  move: (mxia _ qa) =>[ra rb rc rd re].
  move: (cpred_pr ra (nesym(proj2 rb))) => [sa sb].
  move: (rc);rewrite {1} sb =>/(cleSltP sa) /(cltSleP nN) /(Kc' _  _ qa).
  case/cle_eqVlt; last first. 
     move=> /(hu  _ sT) [s' qc]; rewrite - sm => /cltNge; case. apply: iml.
     apply/funI_P; ex_tac.
  move => eqa; exists s => //.
  have ->: ii s =  (cpred (mxi s)).
    move/permutationsP: qa => [bf sf tf].
    rewrite /ii - eqa (inverse_V2 bf) //; rewrite sf; apply/Ka.
    apply/(cleSSP (CS_nat sa) (CS_nat nN)). ue.
  move => i j lij ljk; apply: (rd i j lij); rewrite sb.
  exact: (clt_ltT ljk (cltS sa)).
set G :=  (nds_sums X (csucc n)).
pose pe x f := [/\ inc f (Pe n), pa (Vf f) (ii f) & nds_sc X (csucc n) f = x].
pose fu x :=  choose (pe x).
have fup x: inc x G -> pe x (fu x).
  move => xe; apply:choose_pr.
  by move:xe => /funI_P [f /mixe [f' [qa qb ->]] ->]; exists f'.
pose fv s := fun_image (ii s) (Vf s).
have fvp f: inc f (Pe n) -> pa (Vf f) (ii f) -> cardinal (fv f) = ii f.
  move => fp pak; move: (iip _ fp) => [qa qb _].
  rewrite /fv - {2} (card_card (proj31 qb)); apply:cardinal_fun_image.
  move:(NS_le_nat qb nN) => kN.
  move => i j /(NltP kN) l1 /(NltP kN) l2 ee.
  case: (cleT_ell (proj31_1 l1) (proj31_1 l2)) => lij; first by rewrite lij.
    by move: (proj2 (pak i j lij l2)).
  by case: (proj2 (pak j i lij l1)).
have axg f: inc f (Pe n)  -> pa (Vf f) (ii f) ->  inc (fv f) E.
  move => qa qb; apply/setP_P => u/funI_P [j ja ->].
  move: (iip _ qa) => [qd qe qf].
  move/(NltP (NS_le_nat qe nN)): ja => ja; move:(cleT (proj1 ja) qe) => l1.
  apply/(NltP nN); split; first by apply/(Kc' _ _ qa). 
  move => ee; case: (proj2 ja); exact: (qf _ l1 ee).
have axf x: inc x G -> inc (fv (fu x)) E.
  by move/fup=> [qa qb qc]; apply: axg.
have Hb2 f: inc f (Pe n) -> let s2 := nds_sc X (ii f) f in 
   ordinalp s2 /\ nds_sc X (csucc n) f = X n +o s2.
  move => h;  move: (iip _ h) => [qa qb qc].
  exact: (Hb1 _ _ qb h qa).
have rinj u v : inc u G -> inc v G -> fv (fu u) = fv (fu v) -> u = v.
  move => /fup [qa qb qc] /fup [qa' qb' qc'] sfi.
  rewrite -qc - qc'. 
  rewrite (proj2 (Hb2 _ qa)) (proj2 (Hb2 _ qa')); apply: f_equal.
  move: (iip _ qa)  (iip _ qa')=> [i1 i2 i3] [i1' i2' i3'].
  have: ii (fu u) = ii (fu v).
    by rewrite - (fvp _ qa qb)  - (fvp _ qa' qb') -/(fv _) sfi.
  set k := ii (fu u) => kv.
  have kN:= (NS_le_nat i2 nN).
  rewrite - kv; apply: (osumf_exten kN) => i lik; congr X; move: i lik.
  suff: forall m, natp m -> forall i, i <c m -> i <c k -> 
     Vf (fu u) i = Vf (fu v) i.
    by move => H i lik; apply: (H k kN i lik lik).
  apply: Nat_induction; first by move => i /clt0.
  move => m mN Hrec i /(cltSleP mN); case/(cle_eqVlt); last by apply: Hrec.
  move => -> lik.
  have: inc (Vf (fu u) m) (fv (fu u)) by apply: funI_i; apply /(NltP kN).
  rewrite sfi /fv - kv => /funI_P [j /(NltP kN)ljk eqa].
  move/permutationsP: qa => [[[_ ra] rb] sf tf].
  have  aux t: t <c k -> inc t (source (fu u)).
    rewrite sf => tk; apply/(NleP nN); exact: (cleT (proj1 tk) i2).
  case: (cleT_ell  (proj31_1 ljk) (CS_nat mN)) =>  lmj.
       by rewrite eqa lmj.
     move: (Hrec j lmj ljk); rewrite - eqa => ss; case: (proj2 lmj).
     by apply: ra => //; apply: aux.
  rewrite -/k kv in ljk; move: (qb' _ _ lmj ljk);  rewrite - eqa => /proj1 lt1.
  clear ra rb sf tf j lmj ljk eqa aux.
  have:inc (Vf (fu v) m) (fv (fu v)).
    by apply: funI_i; rewrite -kv;apply /(NltP kN).
  rewrite - sfi /fv  => /funI_P [j /(NltP kN)ljk eqa].
  move/permutationsP: qa' => [[[_ ra] rb] sf tf].
  have  aux t: t <c k -> inc t (source (fu v)).
    rewrite sf => tk; apply/(NleP nN); exact: (cleT (proj1 tk) i2).
  case: (cleT_ell  (proj31_1 ljk) (CS_nat mN)) =>  lmj.
       by rewrite  eqa lmj.
     move: (Hrec j lmj ljk); rewrite - eqa => ss; case: (proj2 lmj).
     by apply: ra => //; apply: aux.
  by move: (qb _ _ lmj ljk); rewrite - eqa => /cltNge; case.
suff Hc s1 s2: inc s1 (Pe n) -> inc s2 (Pe n) -> pa (Vf s1) (ii s1) ->
    pa (Vf s2) (ii s2) -> 
    nds_sc X (csucc n) s1 =  nds_sc X (csucc n) s2 -> fv s1 = fv s2.
  suff: bijection (Lf (fun t => (fv (fu t)))  G E).
    by rewrite /nds_card; move/card_bijection; aw.
  apply: lf_bijective => //.
  move => y yE; move:(nth_elt_dbl_prop1 nN yE).
  set f := Lf _ _ _; move => [fp ys yv fk pak].
  set t := (nds_sc X (csucc n) f).
  have tG: inc t G by apply/funI_P; ex_tac.
  ex_tac; rewrite /fv yv. 
  move:(fup _ tG)=> [qa qb qc].
  have ra: cardinal y = ii f. 
    move/permutationsP: fp => [bf  sf tf].
    by rewrite /ii - fk (inverse_V2 bf) // sf; apply/Ka.
  rewrite ra in pak *. 
  by apply: (Hc _ _ fp  qa pak qb); rewrite qc. 
clear mxi mxia mxib mxic mxid rinj.
move => fp1 fp2 pa1 pa2.
move: (Hb2 _ fp1) (Hb2 _ fp2) => [os1 ->] [os2 ->].
move /(osum2_simpl os1 os2 (ax _ (cltS nN))); rewrite /nds_sc.
pose Ht m := opos_below X m  /\ 
   (forall i j, i <c j -> j <c m -> odegree (X i) <o odegree (X j)).
have: Ht n.
  split; first by  move => i lin; apply: xp; apply: (clt_ltT lin (cltS nN)).
  by move => i j lij /proj1 ljn; apply: xmon.
set K1 := fv s1; set K2 := fv s2.
pose q n K f :=
    [/\ sub K n, K = fun_image (cardinal K)f & pa f (cardinal K)].
move: (fvp _ fp2 pa2); rewrite -/K2 => aux1.
move: (fvp _ fp1 pa1); rewrite -/K1 => aux2.
have: q n K2 (Vf s2). 
   hnf; rewrite aux1; split => //; by apply/setP_P; apply: axg.
have: q n K1 (Vf s1).
  hnf; rewrite aux2; split => //; by apply/setP_P; apply: axg.  
rewrite - aux1 - aux2; clear aux1 aux2.
set f1 := Vf s1; set f2 := Vf s2; move: K1 K2 f1 f2.
clear  Hb1 G axf fu fup fv fvp axg.
clear  ii iip mixe pe  Hb2 pa1 pa2 os1 os2.
clear sN  E F ax s1 s2 xp xmon fp1 fp2  Ka Kb Kc Kc' Kd.
move: n nN.
have prop0 n K: natp n ->  sub K (csucc n) ->  ~inc n K -> sub K n.
  move => nN ha h t tK.
  move: (ha _ tK)=> /(NltP (NS_succ nN)) /(cltSleP nN) /cle_eqVlt; case.
    by move => tn; case: h; rewrite - tn.
  by move/(NltP nN).
have prop1 n K : natp n -> sub K n -> natp (cardinal K).
  by move => nN /sub_smaller; rewrite (card_nat nN) => x; apply (NS_le_nat x).
have hw n K f: natp n -> sub K n -> (forall i, i <c cardinal K -> inc (f i) K)
  -> Ht (csucc n) -> osumf (fun z => X (f z)) (cardinal K) <o X n.
  move => nN ha hb [ht1 ht2].
  apply: (olt_leT _ (proj1 (the_cnf_p4  (ht1 _ (cltS nN))))).
  have ii:=(indecomp_prop4  (OS_degree (proj32_1 (ht1 _ (cltS nN))))).
  have: forall i, i <c (cardinal K) ->  X (f i) <o oopow (odegree (X n)).
    move => i /hb /ha /(NltP nN) => fin.
    apply:(olt_leT  (proj2 (the_cnf_p4 (ht1 _ (clt_ltT fin (cltS nN)))))).
    apply:opow_Mo_le; apply/oleSltP;exact: (ht2 _ _ fin (cltS nN)).
  move: (prop1 _ _ nN  ha).
  move:(cardinal K); apply:Nat_induction.
    move => _; rewrite osum_f0; exact: (proj1 ii).
  move => m mN Hr ax; move: (true_below_rec mN ax) => [ax1 ax2].
  rewrite (osum_fS _ mN). 
  apply:(indecomp_prop2 ax2 (Hr ax1) ii).
have prop3 n K f: let K1 := K -s1 n in let k1 := cpred (cardinal K) in 
   natp n -> q (csucc n) K f -> 
   inc n K -> [/\ [/\ cardinal K  = csucc (cardinal K1),
                      natp (cardinal K1) & k1 = cardinal K1],
                  k1 <c cardinal K, f k1 = n ,
       forall i, i <c cardinal K1 -> inc (f i) K1 & q n (K -s1 n) f].
  move => /= nN [qa qb qd] nK; move: (NS_succ nN) => snN.
  move: (cpred_pr5 nK) (csucc_pr2 nK).
  have Kn:=  (prop1 _ _ snN qa).
  set k := cpred _; set k' := cardinal _ => eq1 eq2. 
  have ckz: cardinal K <> \0c by  rewrite eq2; apply: succ_nz.
  move: (cpred_pr Kn ckz); rewrite - eq1 -/k; move => [kN eq3].
  move: (cltS kN); rewrite - eq3 eq1 =>lt1.
  move: nK; rewrite {1} qb => /funI_P [i /(NltP Kn) lik fv].
  move: lik; rewrite {1} eq3  =>/(cltSleP kN); move/(NltP Kn):(lt1) => lt2.
  rewrite {1} eq1 ;move/cle_eqVlt; case => ik1; last first.
    case: (cltNge (qd _ _ ik1 lt1)); rewrite - fv.
    by apply /(cltSleP nN)/(NltP  snN) /qa; rewrite qb; apply: funI_i.
  rewrite ik1 in fv; clear i ik1.
  move: (kN); rewrite eq1 => kN'.
  have hu:  forall i, i <c k' -> inc (f i) (K -s1 n).
    move => i lik; apply/setC1_P.
    move/(NltP Kn) : (clt_ltT lik lt1) => ik2.
    have fik:inc (f i) K by rewrite qb; apply funI_i.
    by split => // eq4; case: (proj2 (qd _ _ lik lt1)); rewrite eq4 fv. 
  split => //; split.
  - by apply:(prop0 _ _ nN); [ move => t/setC1_P [/qa] | move=> /setC1_P [_]].
  - rewrite {1} qb; set_extens t.
      move => /setC1_P [/funI_P [i lik ->] fjn]; apply/funI_P; exists i => //.
      apply/(NltP kN'); split; last by move => ba; case: fjn; ue.
      by apply/(cltSleP kN'); rewrite - eq2; apply /NltP.
    move/funI_P =>[i /(NltP kN') lik ->]; rewrite - qb; apply/setC1_P.
    move/(NltP Kn) : (clt_ltT lik lt1) => ik2.
    have fik:inc (f i) K by rewrite qb; apply funI_i.
    by split => // eq4; case: (proj2 (qd _ _ lik lt1)); rewrite eq4 fv. 
  - move => i j lij ljk; apply:(qd _  _ lij (clt_ltT ljk lt1)).
apply: Nat_induction.
  by move => K K' f f''   [ /sub_set0 -> _ _] [/sub_set0 -> _  _] _.
move => n nN Hrec K K' f f' qp qp' Htt.
have sN := NS_succ nN.
have pa' t: inc t  (csucc n) -> inc t n \/ t = n.
  move/(NltP sN) /(cltSleP nN) /cle_eqVlt; case; first by right.
  by move/(NltP nN); left.
move: (qp) (qp')=> [pr1 pr2 pr4] [pr1' pr2' pr4'].
move: (prop0 _ _ nN pr1)  (prop0 _ _ nN pr1') => hu hv.
have cKN:= prop1 _ _ sN pr1; have cKN':= prop1 _ _ sN pr1'.
have ax0 i: inc i (csucc n) -> ordinalp (X i).
  move/(NltP sN) => lin; exact: (proj32_1 ((proj1 Htt) _ lin)).
have hx: nds_ax (fun z => X (f z)) (cardinal K).
  by move => i /(NltP cKN) ii;apply:ax0; apply: pr1; rewrite pr2;apply: funI_i.
have hx': nds_ax (fun z => X (f' z)) (cardinal K').
  move => i /(NltP cKN') ii;apply:ax0.
  by apply: pr1'; rewrite pr2';apply: funI_i.
have Htn : Ht n.
  split; first by exact: (proj1 (true_below_rec nN (proj1 Htt))).
  by move => i j lij ljn; apply: (proj2 Htt i j lij (clt_ltT ljn (cltS nN))).
case: (inc_or_not n K) => inK; case: (inc_or_not n K') => inK'.
- move: (prop3 _ _ _  nN  qp inK).
  set K1 := K -s1 n; set k1 := cpred _. 
  move => [[k1v k1N k2v] lt1 fk1 fk2 qp1].
  move: (prop3 _ _ _  nN  qp' inK').
  set K1' := K' -s1 n; set k1' := cpred _.
  move => [[k1v' k1N' k2v'] lt1' fk1' fk2' qp1'].
  have ax1: ordinalp (osumf (fun z =>  X (f z)) k1).
    apply: (OS_osumf (NS_lt_nat lt1 cKN)) => i ii.
    apply: (hx _ (clt_ltT ii lt1)).
  have ax1': ordinalp (osumf (fun z => X (f' z)) k1').
    apply: (OS_osumf (NS_lt_nat lt1' cKN')) => i ii.
    apply: (hx' _ (clt_ltT ii lt1')).
  have o3:= (proj32_1 (proj1 Htt _ (cltS nN))).
  rewrite k1v k1v' (osum_fS _ k1N)  (osum_fS _ k1N') - k2v fk1 - k2v' fk1'.
  move/(osum2_simpl ax1 ax1' o3); rewrite  k2v k2v' => ss.
  rewrite - (setC1_K inK) - (setC1_K inK').
  by rewrite -/K1 (Hrec _ _ _ _ qp1 qp1' Htn ss).
- move: (hv inK') => ra eq0.
  have r4: forall i, i <c cardinal K'-> inc (f' i) K'.
    by rewrite {2} pr2' => i lik; apply: funI_i; apply/NltP.
  move: (hw _ _ _ nN ra r4 Htt); rewrite - eq0 => lt1.
  move: (prop3 _ _ _  nN  qp inK) => [_ qb qc qd].
  by case: (oleNgt (osum_Mon1 cKN qb hx)); rewrite qc.
- move: (hu inK) => ra eq0 .
  have r4: forall i, i <c cardinal K-> inc (f i) K.
    by rewrite {2} pr2 => i lik; apply: funI_i; apply/NltP.
  move: (hw _ _ _ nN ra r4 Htt); rewrite  eq0 => lt1.
  move: (prop3 _ _ _  nN qp' inK') => [qa qb qc qd].
  by case: (oleNgt (osum_Mon1 cKN' qb hx')); rewrite qc.  
- by move: (hu inK) (hv inK')  => ra rb; apply: Hrec.
Qed.

Lemma nds_card_different_deg n: natp n ->
  nds_ax oopow (csucc n) /\ nds_card  oopow (csucc n) = \2c ^c n. 
Proof.
move => nN.
have ha: opos_below oopow (csucc n).
  by move => y tn; apply: oopow_pos; exact: (proj1 (proj31_1 tn)).
have hb i j: i <c j -> j <=c n -> odegree (oopow i) <o odegree (oopow j).
  move => /oclt lij _.
  by rewrite (odegree_opow (proj31_1 lij)) (odegree_opow (proj32_1 lij)).
exact: (nds_card_different_deg_gen nN ha hb).
Qed.

Lemma osum_of_nat n X: natp n -> (forall i, i <c n -> natp (X i)) ->
  osumf X n = csumb n X.
Proof.
move: n; apply: Nat_induction.
  by move => _; rewrite osum_f0 /csumb csum_trivial //; aw.
move => m mN Hrec zp; rewrite (osum_fS _ mN)  (succ_of_nat mN).
have ha: forall i, i <c m -> natp (X i). 
  move => i lim; apply: zp; exact: (clt_ltT lim (cltS mN)).
have zmN:= (zp _ (cltS mN)); move: (Nat_decent mN) => mm.
have sN: natp (csumb m X). 
  apply:finite_sum_finite; split.
    by hnf; aw;move => i lim; rewrite LgV//; apply: ha; apply /(NltP mN).
  by aw; apply: finite_set_nat.
by rewrite (csumA_setU1 X mm) (Hrec ha) csumC (osum2_2int zmN sN).
Qed.

Lemma osum_of_nat_bis n X f: natp n -> (forall i, i <c n -> natp (X i)) ->
  inc f (permutations n) ->
  nds_sc X n f = osumf X n.
Proof.
move => nN ax /permutationsP[bf sf tf].
have ax2: forall i, i <c n -> natp (X (Vf f i)).
  move => i /(NltP nN) libe; apply: ax;apply/(NltP nN).
  move: (proj1 (proj1 bf)) => ff; Wtac.
rewrite /nds_sc ! osum_of_nat // -{1} sf - tf.
have qb: quasi_bij (Vf f) (source f) (target f).
  move:bf => [[ff hh] [_ sj]]; split => // t tsf; Wtac.
by rewrite (csum_Cn2 X qb).
Qed.

Lemma nds_of_nat n X:  natp n -> (forall i, i <c n -> natp (X i)) ->
  nds_card X n = \1c.
Proof.
move => nN Xp.
suff: (nds_sums X n) = singleton (osumf X n).
  by rewrite /nds_card;move => ->; rewrite cardinal_set1.
apply: set1_pr1.
  move:(permutation_id n) => ip; apply/funI_setne; ex_tac.
move => s/funI_P [z zp ->]; exact:osum_of_nat_bis.
Qed.

Lemma nds_type0 n X: 
  natp n -> \2c <=c n -> nds_ax X n -> (exists2 i, i<c n & X i = \0o) -> 
  exists2 Y, nds_ax Y n & nds_card X n <c nds_card Y n.
Proof.
move => nN ln2 ax Hx.
have nz:= (card_ge2_nz ln2).
move: (cpred_pr nN nz); set m := cpred n; move => [mN nv].
have: exists Z,
    [/\ nds_ax Z n, nds_card X n = nds_card Z n & Z m = \0o].
  move: Hx => [i lin Xz].
  have iin: inc i n by apply /(NltP nN).
  move /(NltP nN): (cpred_lt nN nz) => ipn.
  move:(transposition_prop nN iin ipn).
  set G := Lf _ _ _; move => [Gp Gi Gpn Go GGx].
  move:(proj1(nds_ax_perm nN ax Gp));set Z := (fun z => X (Vf G z)) => axZ.
  by exists Z; rewrite (nds_card_perm_inv nN ax Gp) /m /Z Gpn. 
move => [Z [axZ -> Z0]]; clear X ax Hx.
wlog xnz: Z Z0 axZ/ exists2 i, i <c m & Z i <> \0o. 
  move=> Ha; case: (p_or_not_p(exists2 i, i <c m & Z i <> \0o)) => Hx.
    by apply: Ha.
  have Xn: forall i, i <c n -> natp (Z i).
    rewrite nv => i /(cltSleP mN)/ cle_eqVlt; case.
      move ->;rewrite Z0; apply:NS0.
    move => im; case: (equal_or_not (Z i) \0o) => h; first by rewrite h; fprops.
    by case: Hx; exists i.
  pose X1 := fun i => Yo (i = m) \0o \1o.
  have X1n: forall i, i <c n -> natp (X1 i).
    rewrite /X1; move => i ii; Ytac h; fprops.
  have X1m:  X1 m = \0o by rewrite /X1; Ytac0.
  move: ln2; rewrite - succ_one {1}nv;move/(cleSSP CS1 (CS_nat mN))/cge1P => n1.
  have X10: exists2 i, i <c m & X1 i <> \0o.
    exists \0c => //; rewrite /X1 (Y_false (proj2 n1)); fprops.
  have ax1: nds_ax X1 n by move => i /X1n /OS_nat.
  by rewrite (nds_of_nat nN Xn) -(nds_of_nat nN X1n); apply: Ha.
have lmn:  m <c n by move: (cltS mN); rewrite nv.
have axm: nds_ax Z m by move => i lin; apply: axZ; move: (clt_ltT lin lmn).
have alsp: forall v, inc v (nds_sums Z m) -> \0o <o v.
  move => v /funI_P [s sp ->].
  move: (nds_ax_perm mN axm sp) => [ha hb].
  apply:(osum_fnz mN ha).
  move/permutationsP: sp => bsp.
  move: (inverse_bij_bp bsp) => [[[isb _] _] iss ist].
  move: bsp=> [bs ss ts].
  move: xnz => [k lkm Zk].
  have ktf: inc k (target s) by  rewrite ts; apply/(NltP mN).
  move: (inverse_V bs ktf); rewrite -/k => kv.
  exists  (Vf (inverse_fun s) k); last by rewrite kv.
  by apply/(NltP mN); Wtac; rewrite iss - ts.
have [e oe ep]: exists2 e, ordinalp e &  
  (forall i, i<c m -> Z i <o oopow e). 
  suff: exists2 x, ordinalp x & (forall i, i<c m -> Z i <=o x).
    move => [x ox xle]; move:(OS_succ ox) => osx; exists (osucc x) => //.
    move => i /xle le; apply: (ole_ltT le); apply/oleSltP.
    by apply:ord_eps_p1.
  clear nv Z0 xnz lmn alsp.
  move: m mN axm; apply:Nat_induction.
    move => _; exists \0o; [ exact: OS0 | by  move => i /clt0].
  move => m mN Hrec h. 
  move: (true_below_rec mN h)=> [sa sb].
  move: (Hrec  sa) => [a oa ap].
  move:(omax_p1 oa sb) => [sc sd].
  exists (omax a (Z m)); first exact: (proj32 sc).
  move => i /(cltSleP mN) /cle_eqVlt; case; first by move ->.
  move/ap => le1; apply: (oleT le1 sc).
pose T u i := Yo (i = m) u (Z i).
have To u: ordinalp u -> nds_ax (T u) n.
rewrite nv /T => ou i /(cltSleP mN) /cle_eqVlt [] li; try Ytac0 => //.
   by rewrite (Y_false (proj2 li)); apply: axm.
have Tuv u: ordinalp u -> 
  forall v, inc v (nds_sums Z m) -> inc (u +o v)  (nds_sums (T u) n).
  move => ou v /funI_P [s sp ->].
  move: (extension_perm mN sp).
  set es := extension s m m; move => [esp esout esin].
  rewrite - nv in esp; apply/funI_P; ex_tac.
  rewrite/nds_sc nv (osum_fS _ mN) esout/T; Ytac0; congr osum2.
  apply: (osumf_exten mN) => i /(NltP mN) lin; rewrite esin //.
  have: inc (Vf s i) m by move/permutationsP: sp => [[[ff _] _ ] sf tf]; Wtac.
  by move/(NltP mN) => /proj2 nn; Ytac0.
set u := oopow e.
have ou:= (OS_oopow oe).
have us: inc u (nds_sums (T u) n).
  apply/funI_P; move: (rotation_prop mN); rewrite - nv.
  set f := Lf _ _ _; set g := Lf _ _ _.
  move => [pf pg ifg [fo fa1 fa2 gn ga]].
  exists f; first exact.
  rewrite /T /nds_sc nv (osum_negl_rec oe) //.
    by rewrite fo; Ytac0.
  by move => i lin; rewrite (fa1 _ lin)  (Y_false (proj2 lin)); apply: ep.
move: (To  u ou) => axT.
exists (T u); first exact: (To  u ou).
apply/(cleSltP (NS_nds_card Z nN)).
have ->: nds_card Z n = cardinal(nds_sums Z m).
  rewrite /nds_card /nds_sums; congr cardinal.
  set_extens z; last first.
    rewrite nv; move: (Tuv _ OS0) => rb zv.
    have oz: ordinalp z.
      move/funI_P: zv =>[w wp ->]; exact: (proj2(nds_ax_perm mN axm wp)).
    move: (rb _ zv); rewrite (osum0l oz) - nv.
    congr inc; apply:(nds_sums_exten nN)=> i lin; rewrite /T.
    by Ytac h => //; rewrite h Z0.
  move => /funI_P [f fp ->].
  rewrite nv in fp; move: (partial_rotation mN fp).
  set k := Vf (inverse_fun f) m.
  set (g:= fun i => Yo (i <c k) (Vf f i) (Vf f (csucc i))).
  move => [lekn fk axg gp].
  apply/funI_P; ex_tac.
  move: (cdiff_pr lekn) (NS_diff k mN); set q:= _ -c _ => sb qN.
  move/(cleSSP (proj31 lekn) (proj32 lekn)): (lekn) => li0n1.
  have kN:=(NS_le_nat lekn mN).
  have skN:=(NS_succ kN).
  pose g0 i := Z (Vf (Lf g m m) i).
  pose f0 i := Z (Vf f i).
  move/permutationsP: (fp) => [bf sf tf]; move: (proj1(proj1 bf)) => ff.
  rewrite -nv in sf tf.
  have ax1: nds_ax f0 (csucc k +c q).
    rewrite (csum_Sn _ kN) sb - nv => i lin; rewrite /f0; apply: axZ.    
    by apply/(NltP nN);  Wtac; rewrite sf; apply/(NltP nN).
  have ax2: (nds_ax g0 (k +c q)).
    rewrite sb => i/(NltP mN) lin; rewrite /g0 LfV//; apply axm. 
    by move: (axg _ lin) => /(NltP mN) h1. 
  have osa: ordinalp (osumf f0 k).
    apply: (OS_osumf kN) => i lin; rewrite /f0; apply: axZ.
    apply/(NltP nN); Wtac; rewrite sf;apply/(NltP nN).
    exact: (clt_ltT lin (cle_ltT lekn lmn)).
  move:(osum_fA skN qN ax1);rewrite (csum_Sn _ kN) sb nv -/(nds_sc _ _ _) => ->.
  rewrite (osum_fS _ kN) {2} /f0 fk Z0 (osum0l osa).
  rewrite /nds_sc - {3} sb (osum_fA kN qN ax2); apply: f_equal2.
    apply:(osumf_exten qN) => i lim; rewrite /f0/g0 /g.
    have ha: inc (i +c k) m. 
      apply /(NltP mN); rewrite -{1} sb (csumC _ q); apply:(csum_Mlteq kN lim).
    have hb: ~(i +c k <c k).
      move:(csum_Mle0 i (proj31 lekn)) => ua ub; case: (cleNgt ua ub).
    by rewrite LfV//; Ytac0; rewrite (csum_nS _ kN).
  apply:(osumf_exten kN) => i lim; rewrite /f0/g0 /g. 
  rewrite LfV //; [ by Ytac0 |apply /(NltP mN); apply: (clt_leT lim lekn) ].
have alsp': ~inc \0o (nds_sums Z m) by move /alsp; case.
rewrite - (csucc_pr alsp').
have: injection (Lf (osum2 u) (nds_sums Z m +s1 \0o) (nds_sums (T u) n)).
  have H x: inc x (nds_sums Z m +s1 \0o) -> ordinalp x.
    case /setU1_P; last by move ->; apply: OS0.
    move => /funI_P [p pp ->]; exact:proj2 (nds_ax_perm mN axm pp).
  apply: lf_injective.
    by move => x/setU1_P; case; [ apply: Tuv | move ->; rewrite (osum0r ou)].
  move => x y /H xs /H ys; apply: (osum2_simpl xs ys ou).
by move /inj_source_smaller; aw.
Qed.

Lemma nds_same_deg_s2 e c1 c2 r1 r2:
  ordinalp e -> ordinalp c1 -> r1 <o oopow e -> 
  \0o <o c2 -> ordinalp r2 ->
  (oopow e *o c1 +o r1) +o (oopow e *o c2 +o r2) =
  (oopow e *o (c1 +o c2) +o r2).
Proof.
set p := oopow e;move => oe oc1 pa pb or2.
have op := OS_oopow oe.
have or1:= (proj31_1 pa).
have oc2:= (proj32_1 pb).
have oa := OS_prod2 op oc1.
have ob := OS_prod2 op oc2.
have oc := OS_sum2 ob or2.
have H:=(ord_negl_prod or1 op  pb (indecomp_prop1 (indecomp_prop4 oe) pa)).
rewrite - (osumA oa or1 oc) (osumA  or1 ob or2) H (osumA oa ob or2).
by rewrite - (oprodD oc1 oc2 op).
Qed.


Lemma nds_same_deg_sn e (c r: fterm) n:
  natp n -> \0c <c n -> ordinalp e -> 
  (forall i, i<c n -> \0o <o c i /\ r i <o oopow e) ->
  osumf (fun i => oopow e *o (c i) +o r i) n =
  oopow e *o (osumf c n) +o (r \0c).
Proof.
move => nN nz oe.
have op := (OS_oopow oe).
move: (cpred_pr nN (nesym (proj2 nz))) => [pN ->].
move: (cpred n) pN; clear n nN nz; apply: Nat_induction.
  rewrite succ_zero => H.
  move: (H _ (clt_01)) => [[[_ oc _] _] [[or _ _] _]].
  have ot:= (OS_sum2 (OS_prod2 op oc) or).
  by rewrite (osum_f1 oc) (osum_f1).
move => n nN Hrec ol.
move:(true_below_rec (NS_succ nN) ol) => [sa [/proj32_1 ocn rs]].
move:(proj31_1 (proj2(sa _ (succ_positive n)))) => or0.
rewrite (osum_fS _ (NS_succ nN)) (Hrec sa).
move:(true_below_rec nN sa) => [sb [[/proj32 oc0 /nesym cnz]_]].
have pc: \0o <o osumf c (csucc n).
  have /(OS_osumf nN) ha: nds_ax c n by move => i /sb [/proj32_1 ].
  rewrite (osum_fS _ nN); apply: (ord_ne0_pos  (OS_sum2 oc0 ha)).
  by case/(osum2_zero oc0 ha).  
by rewrite (nds_same_deg_s2 oe ocn rs pc or0) (osum_fS _ (NS_succ nN)).
Qed.

Lemma nds_same_deg_s_perm e (c r: fterm) n f
      (X := (fun i => oopow e *o (c i) +o r i)): 
  natp n -> \0c <c n-> ordinalp e -> 
  (forall i, i<c n -> \0o <o c i /\ r i <o oopow e) ->
  (forall i, i<c n ->  c i <o omega0)  ->
  inc f (permutations n) ->
  nds_sc X n f =
  oopow e *o (osumf c n) +o (r (Vf f \0c)).
Proof.
move => nN nz oe h1 h2 fp.
move:(fp) =>  /Zo_P [] /functionsP [fz sz tz] bz.
have sa: forall i, i <c n -> \0o <o c (Vf f i) /\ r (Vf f i) <o oopow e.
  move => i /(NltP nN) lin; apply: h1; apply /(NltP nN); Wtac.
transitivity
 (osumf(fun i => oopow e *o (c (Vf f i)) +o r (Vf f i)) n).
  by apply:(osumf_exten nN) => i lin.
have h3: forall i, i <c n -> natp (c i).
  by move => i  /h2 /olt_omegaP. 
by rewrite (nds_same_deg_sn nN nz oe sa) - /(nds_sc c n f) (osum_of_nat_bis). 
Qed.

(* noter la modif *)

Lemma nds_card_same_deg_bd e X n: natp n -> \0c <c n ->
  (opos_below X n) ->
  (forall i, i <c n -> odegree (X i) = e) ->
  nds_card X n <=c n.
Proof.
move => nN nz pa pb.
pose c i := the_cnf_lc (X i).
pose r i := the_cnf_rem (X i).
have pc i: i<c n -> [/\ \0o <o c i, c i <o omega0, (r i) <o oopow e
      & X i = oopow e *o (c i) +o (r i)].
  move => lein; move: (pa _ lein) (pb _ lein) => sa sb.
  by move: (the_cnf_split sa); rewrite sb. 
have oe: ordinalp e.
  rewrite -(pb _ nz); exact: (OS_degree (proj32_1 (pa _ nz))).
set s1:= oopow e *o (osumf c n).
have os1: ordinalp s1. 
  apply: (OS_prod2 (OS_oopow oe) (OS_osumf nN _)) => i lin.
  by move:(pc _ lin) => [ /proj32_1 h _ _ _].
set E := (permutations n).
set F1 := (fun_image E (nds_sc X n)).
set F2 := (fun_image E (fun f => r (Vf f \0c))).
have pe i: i<c n -> c i <o omega0  by move =>  /pc[].
have pd i: i<c n -> \0o <o c i /\ r i <o oopow e by move => /pc[].
have pf: forall f, inc f E -> nds_sc X n f = s1 +o (r (Vf f \0c)).
  move => f fp; rewrite - (nds_same_deg_s_perm nN nz oe pd pe fp).
  by apply:(nds_sc_exten nN _ fp) => i /pc [].
have pg: forall z, inc z E -> inc (Vf z \0c) n.
  move => z /Zo_P [] /functionsP [fz sz tz] bz; Wtac.
  by rewrite sz; apply/(NltP nN). 
have osF: ordinal_set F2.
  by move=> s /funI_P [z /pg  /(NltP nN) /pc  [_ _ /proj31_1 h _] ->].
suff: nds_card X n = cardinal (fun_image n r).
  move ->; rewrite -{2} (card_nat nN); apply:fun_image_smaller.
symmetry.
apply/card_eqP.
exists (Lf (fun z => s1 +o z) F2 F1); split.
* apply:lf_bijective.
  + by move => s /funI_P [z ze -> ]; apply /funI_P; ex_tac; rewrite (pf _ ze).
  + by move => u v /osF ou /osF ov /(osum2_simpl ou ov os1).
  + move => s /funI_P [z ze -> ];  rewrite (pf _ ze).
    exists (r (Vf z \0c)) => //;apply/funI_P; ex_tac.
* rewrite lf_source;set_extens t.  
  move => /funI_P [z /pg ze -> ];  apply /funI_P; ex_tac.
  move => /funI_P [i /(NltP nN) iI ->]; apply /funI_P.
  move: (permutation_exists1 nN iI) => [f fe <-]; ex_tac.
* by aw.
Qed.

Definition nds_F n := 
 \csup (Zo Nat (fun z => exists2 X, nds_ax X n & nds_card X n = z)).

Lemma nds_f_def n (f := nds_F n): natp n ->
  [/\ natp f,
   f <=c factorial n,
   (exists2 X, nds_ax X n & nds_card X n = f) &
   (forall X, nds_ax X n -> nds_card X n <=c f)].
Proof.
move => nN.
set T := (Zo Nat(fun z => exists2 X, nds_ax X n & nds_card X n = z)).
move: (NS_factorial nN) => tb.
have tc: (forall i, inc i T -> i <=c (factorial n)).
  rewrite /T;move=> i /Zo_P [iN [X ea <-]]; exact: (nds_card_bd X nN). 
move: (Nat_sup_pr tb tc) => [pa pb pc pd].
have pe X: nds_ax X n -> inc (nds_card X n) T.
  by move => ax; apply: Zo_i;[ apply: NS_nds_card | exists X].
case:pd => h.
  set X := (fun z: Set => \0o). 
  have aX: nds_ax X n by rewrite /X;move => i _ /=; apply: OS0.
  by empty_tac1 (nds_card X n); apply: pe.
by split => //; [ move:h => /Zo_P [_] | move=> X xv; apply: pc;  apply: pe].
Qed.

Lemma nds_sd1 n: natp n -> \2c ^c n <=c nds_F (csucc n).
Proof.
move => nN.
move: (nds_card_different_deg nN) => [ra rb].
move: (nds_f_def (NS_succ nN)) => [_ _ _ rc].
by move: (rc _ ra); rewrite rb.
Qed.

Lemma nds_f2: nds_F \2c = \2c.
Proof.
apply: cleA.
  by move: (proj42 (nds_f_def NS2)); rewrite factorial2.
by move: (nds_sd1 NS1); rewrite (cpowx1 CS2) succ_one.
Qed.

Lemma nds_sd2 n: natp n -> \2c <c n -> n <c (nds_F n). 
Proof.
move => nN ngt2.
have nnz:= nesym (proj2(clt_ltT clt_02 ngt2)).
move:(cpred_pr nN nnz) => [n1N sa].
have npz: cpred n <> \0c.
  move => h; move: sa (proj1 ngt2). 
  by rewrite h succ_zero => -> /(cltNge clt_12).
move:(cpred_pr n1N npz) => [n2N sb].
have pN:= NS_pow NS2 n2N.
have ha : \2c <=c \2c ^c cpred (cpred n).
   apply:(cpow_Mle1 CS2) => mz.
   by case:(proj2 ngt2); rewrite sa sb mz succ_zero succ_one.
have hb: csucc (cpred n) <c \2c ^c cpred n.
  rewrite sb (cpow_succ _ n2N) cprodC - csum_nn.
  rewrite (Nsucc_rw (NS_succ n2N)) (Nsucc_rw n2N) - csumA csum_11 csumC.
  exact:(csum_Mlelt pN  ha (cantor (CS_nat n2N))).
rewrite sa; exact: (clt_leT hb (nds_sd1 n1N)).
Qed.

Definition nds_type X n k :=
  (opos_below X n) /\
  (exists m, [/\ ordinalp m,
     (forall i,  i<c n -> m <=o odegree (X i)) &
     cardinal (Zo n (fun i => odegree (X i) = m)) = k]).

Definition nds_FA n k:= 
 \csup (Zo Nat (fun z => exists X, [/\ nds_ax X n, nds_card X n = z
     & nds_type X n k])).

Lemma nds_type_exists_bd n k:
   natp n -> \0c <c k -> k <=c n -> exists X,
   nds_ax X n /\ nds_type X n k.
Proof.
move => nN kp lkn. 
have kz := (nesym (proj2 kp)).
pose X i := Yo (i <c k) \1o omega0.
have ha: nds_ax X n by move => t _; rewrite /X; Ytac h; fprops.
have hb: opos_below X n.
  move => i _; rewrite /X; Ytac h; [apply: olt_01| apply: olt_0omega].
exists X; split => //; split => //. 
move: odegree_one odegree_omega => dg1 dgo.
exists \0o; split; [ exact: OS0 | by move => i /ha/OS_degree /ole0x | ].
set E := Zo _ _. 
move:(NS_le_nat lkn nN) => kN.
rewrite -(card_nat kN); congr cardinal.
set_extens t.
  move => /Zo_P [ /(NltP nN) lth]; rewrite /X; Ytac h1.
    by move => _; apply/(NltP kN).
  by rewrite dgo => ba; case: card1_nz.
move => /(NltP kN) ltl;apply: Zo_i.
  apply /(NltP nN); exact:(clt_leT ltl lkn).
by rewrite /X; Ytac0; rewrite dg1.
Qed.


Lemma nds_FA_def n k (v := nds_FA n k):
  natp n -> \0c <c k -> k <=c n -> 
  [/\ natp v,
   v <=c  (nds_F n),
   (forall X,  nds_ax X n -> nds_type X n k -> nds_card X n <=c v) &
   (exists  X, [/\ nds_ax X n, nds_type X n k & nds_card X n = v])].
Proof.
move=> nN kp kn.
rewrite /v /nds_FA; set T:= Zo Nat _.
have tb: natp (nds_F n) by move: (nds_f_def nN) => [ok _].
have tc: (forall i, inc i T -> i <=c  (nds_F n)).
  move => i /Zo_P [_ [X [ax <- _]]].
  by move: (nds_f_def nN) => [_ _ _ p4]; apply: p4.
move: (Nat_sup_pr tb tc) => [pa pb pc pd].
have pe X: nds_ax X n ->  nds_type X n k -> inc (nds_card X n) T.
  by move => ax ax2; apply: Zo_i;[ apply: NS_nds_card | exists X].
split => //.
  by move=> X ax ax2; apply: pc; apply: pe.
case: pd; last by move /Zo_P=> [_ [X [p1 p2 p3]]];exists X; split.
move: (nds_type_exists_bd nN kp kn)=> [X [ax  tx]] te.
empty_tac1 (nds_card X n);apply:pe.
Qed.


Lemma nds_FA_21: nds_FA \2c \1c = \2c.
Proof.
move: (nds_FA_def NS2 clt_01 cle_12);rewrite nds_f2.
set v := (nds_FA \2c \1c);move => [vN lv2 ha hb].
apply: (cleA lv2).
move:(nds_card_different_deg NS1).
rewrite succ_one (cpowx1 CS2); move => [r1 r2].
suff foo: nds_type oopow \2c \1c by  rewrite - r2; exact: (ha _ r1 foo).
split; first by move => i li2; exact (oopow_pos (OS_cardinal (proj31_1 li2))).
have e0:= OS0.
exists \0c; split => //.
  move => i /proj31_1/ OS_cardinal oi.
  by rewrite (odegree_opow oi); apply: ole0x. 
apply/set_of_card_oneP; exists \0c; apply: set1_pr.
  by apply: (Zo_i inc_C0_C2); rewrite  (odegree_opow e0).
by move => t /Zo_P [/C2_P]; case => -> //; rewrite  (odegree_opow OS1).
Qed.

Lemma nds_F_FA_def n (g := nds_FA n) (f:= nds_F n):
  natp n -> \2c <=c n ->
  (forall k,  \0c <c k -> k <c n  -> (g k) <=c f) /\ 
  (exists k, [/\ \0c <c k,  k <c n & (g k) = f]).
Proof.
move=> nN nge2.
split.
  by move => k kp kn ; move: (nds_FA_def nN kp (proj1 kn)) => [_ pa _].
case: (equal_or_not n \2c) => en2.
  move: clt_12 clt_01 => ra rb. 
  rewrite /f /g en2 nds_f2; exists \1c; split => //; exact: nds_FA_21.
move: (nds_f_def nN); rewrite -/f; move=> [_  _ [X ax fv] pd].
move: (clt_leT clt_02 nge2) => np.
case: (p_or_not_p (exists2 i, i<c n & X i = \0o)) => tp0.
  move:(nds_type0 nN nge2 ax tp0) => [y ay xsy].
  by case: (cleNgt(pd y ay)); rewrite - fv.
set E:= fun_image  n (fun i => odegree (X i)).
set m := intersection E.
set F :=  (Zo n (fun i => odegree (X i) = m)).
have s1: sub F n by apply Zo_S.
move: (sub_smaller s1); rewrite (card_nat nN) => kn.
have osE: ordinal_set E.
  rewrite /E; move=> t /funI_P [z /(NltP nN) /ax zi ->]. 
  by apply: OS_degree.
have neE: nonempty E by apply:funI_setne; exists \0c; apply/(NltP nN).
move: (ordinal_setI neE osE); rewrite -/m => mE.
set k := cardinal F.
have kp: \0c <c k.
  move: mE => /funI_P [z zn zv].
  apply: (card_ne0_pos (CS_cardinal _) (card_nonempty1 _)).
  by exists z; apply: Zo_i.
have kt: nds_type X n k.
  split.
    move => i lin; case: (ozero_dichot (ax _ lin)) => //.
    by move => baa;case: tp0; exists i.
  have om: ordinalp m  by apply:osE.
  exists m; split => // i /(NltP nN) lin.
  have uE: inc (odegree (X i)) E by apply /funI_P; ex_tac.
  by split; [ exact |  apply: osE | apply:setI_s1].
have eq1: g k = f.
  move:(nds_FA_def nN kp kn) => [_ _ qa  [Y [ax' x3 x4]]];  apply cleA.
    by rewrite /g - x4; apply: pd.
  by move: (qa _ ax kt); rewrite fv. 
case: (equal_or_not k n) => ekn; last by exists k.
case: (cltNge (nds_sd2 nN (conj nge2 (nesym en2)))); rewrite -/f - eq1 /g ekn.
move: (nds_FA_def nN np (cleR (CS_nat nN))).
move => [vB vle _ [Y [ay [ty1 [m' [om mp1 mp2]]] <-]]].  
have fsI:= (finite_set_nat nN).
move: (cardinal_setC4 (@Zo_S n (fun i => odegree (Y i) = m'))  fsI).
rewrite (card_nat nN) mp2  cdiff_nn => /card_nonempty /empty_setC si.
apply: (nds_card_same_deg_bd nN np ty1 (e:=m')).
by move => i  /(NltP nN) /si /Zo_hi.
Qed.

Definition nds_sc_K X K := csumb (cardinal K)(fun z => X (nth_elt K z)). 

Lemma nds_sc_Kval n c K: natp n ->  inc K (\Po n) ->
   nds_sc_K c K = csumb K c.
Proof.
move => nN /setP_P Kb. 
rewrite /nds_sc_K.
have KN: sub K Nat by move => t tK; move:(NS_inc_nat nN (Kb _ tK)).
set q := cardinal K; set f := nth_elt K.
have qN: natp q by apply:(sub_nat_finite nN Kb).
have ha: forall i, i <c q -> inc (f i) K.
  move => i iq; apply:(nth_elt_inK (NS_lt_nat iq qN) KN iq).
have: forall j, inc j K -> exists2 i, i <c q & j = f i.
  move => j jK; apply: (nth_elt_surj KN qN jK).
have : forall i j, i <c q -> j <c q -> f i = f j -> i = j.
  move => i j /(NltP qN) iq /(NltP qN) jq.
  move:(proj2 (proj1 (proj1(nth_elt_bf KN qN)))).
  have ax: lf_axiom (nth_elt K) (cardinal K) K.
    by move => t /(NltP qN) /ha.
  aw => h; move: (h i j iq jq); rewrite !LfV//.
have: finite_set K by apply/NatP.
move: q qN (f) (K) ha; clear.
apply: Nat_induction.
  move => k K  _ _ _  sf.
  have h: domain (Lg K c) = emptyset.
    by aw; apply /set0_P => t /sf [i /clt0].  
  by rewrite csumb0 /csumb (csum_trivial h). 
move => n nN Hrec f K fK fsK  fi fs.
rewrite (csum_fs _ nN).
have nn:= (cltS nN).
move:(fK _ nn) => fnK.
move: (setC1_K fnK); set K1:= K -s1 (f n) => Kv.
have h1: forall i, i <c n -> inc (f i) K1.
  move => i lin; move:(clt_ltT lin nn) => h; move: (fK _ h).
  rewrite - Kv =>/setU1_P; case => // eq; move:(fi _ _ h nn eq) => ein.
  by case: (proj2 lin).
have h2:=(sub_finite_set (@sub_setC K (singleton (f n))) fsK).
have h4: forall i j, i <c n -> j <c n -> f i = f j -> i = j.
  move => i j lin ljn;apply (fi _ _ (clt_ltT lin nn) (clt_ltT ljn nn)).
have h5:forall j, inc j K1 -> exists2 i : Set, i <c n & j = f i.
  move => j /setC1_P [/fs [i /(cltSleP nN) lin ->] h].
  case: (equal_or_not i n) => ein; first by case: h; rewrite ein.
  by exists i.
have fnk1:~ inc (f n) K1 by move/setC1_P=>  [ _ ].
by rewrite (Hrec f K1 h1 h2  h4 h5) - Kv (csumA_setU1 _ fnk1).
Qed.

Lemma nds_C_prop n a: natp n -> inc a n ->
  cardinal (\Po (n -s1 a)) =  \2c ^c (cpred n).
Proof.
move => mN an.
case: (equal_or_not n \0c) => mp; first by  move: an; rewrite mp => /in_set0. 
move:(cpred_pr mN mp) => [pnN pnv].
have ->: cpred n = cardinal (n -s1 a).
  by apply:csucc_inj;fprops;rewrite - pnv - (csucc_pr2 an) (card_nat mN).
by rewrite  cpowcr - card_setP.
Qed.

Definition nds_sc_Ktau X K tau :=
  nds_sc (fun z => X (nth_elt K z))  (cardinal K) tau.

Definition nds_tn_S X n:=
   unionf (\Po n) (fun K =>
      fun_image (permutations (cardinal K)) (nds_sc_Ktau X K)).
Definition nds_tn_C X n :=  cardinal (nds_tn_S X n).

Definition nds_tn_ax X n :=
    (forall i, i<c n -> \0o <o (X i)) /\
    exists2 e, ordinalp e & forall i, i<c n -> odegree (X i)  = e.

Definition nds_tn_sup n :=
  \csup(Zo Nat (fun z => exists2 X, nds_tn_ax X n & nds_tn_C X n = z)).

Lemma nds_tn_small X n:
   natp n -> nds_ax X n ->
   nds_tn_C X n <=c (\2c ^c n) *c (factorial n).
Proof.
move => nN ax.
rewrite /nds_tn_C /nds_tn_S; set F:= (fun K : Set => _).
apply: (cleT (csum_pr1_bis (\Po n) F)).
rewrite - card_setP cprod2cl cprodC - csum_of_same.
apply:csum_increasing; aw; trivial  => K KN;rewrite !LgV//.
move/setP_P:KN => KN.
move:(sub_smaller KN); rewrite (card_nat nN) => ka.
have nKN:=(NS_le_nat ka nN).
apply: cleT  (factorial_monotone nN ka).
have pa: finite_set (cardinal K) by apply/NatP; rewrite double_cardinal. 
rewrite - (double_cardinal K) -(card_permutations pa).
by apply:fun_image_smaller.
Qed.

Lemma nds_tn_def n (f:=  nds_tn_sup n): natp n ->
  [/\ natp f, \0c <c f, 
  (exists2 X, nds_tn_ax X n & nds_tn_C X n = f) &
  (forall X, nds_tn_ax X n -> nds_tn_C X n <=c f)].
Proof.
move => nN.
rewrite /f /nds_tn_sup; set T := Zo _ _.
have kN:=(NS_prod (NS_pow NS2 nN) (NS_factorial nN)).
set k := \2c ^c n *c factorial n.
have H: forall X, nds_tn_ax X n -> nds_tn_C X n <=c k.
  by move => X [ax _]; apply:(nds_tn_small nN) => i /ax /proj32_1.
have H1:forall X, nds_tn_ax X n -> natp (nds_tn_C X n).
  move => X x1; exact:(NS_le_nat (H _ x1) kN).
have ks:forall i, inc i T -> i <=c k by move => z /Zo_hi [X /H ax <-].
pose X (i:Set):= \1o.
have ax: nds_tn_ax X n.
split; first by  move => i _; exact olt_01.
  by exists \0o; [ apply:OS0 | move=> i _; rewrite odegree_one].
have ta: inc (nds_tn_C X n) T by  apply: (Zo_i (H1 _ ax)); exists X.
have ha: \0c <c union T. 
  have: nonempty (nds_tn_S X n).
    have idp:=(permutation_id n).
    exists (nds_sc  (fun z => X (nth_elt n z)) (cardinal n) (identity n)).
    apply/setUf_P; exists n; first by apply:setP_Ti.
    rewrite /nds_sc_Ktau (card_nat nN);apply/funI_P;ex_tac.
  move /card_nonempty1; rewrite -/(nds_tn_C X n) => h0.
  have cst:cardinal_set T by move => t /Zo_S /CS_nat.
  exact:(clt_leT (card_ne0_pos  (cst _ ta) h0) (card_sup_ub cst ta)).
move: (Nat_sup_pr  kN ks) => [pa pb pc pd];split => //; last first.
  move => Y x1; apply: pc; apply/ Zo_P; split; [by apply: H1 | by exists Y].
by case:pd => h1; [ empty_tac1 (nds_tn_C X n) | exact: (Zo_hi h1)].
Qed.

Lemma nds_tn_zero: nds_tn_sup \0c = \1c.
Proof.
move:(nds_tn_def NS0) => [_ _ [X ax <-] _].
rewrite /nds_tn_C /nds_tn_S setP_0 setUf_1 cardinal_set0 permutations_set0.
by rewrite funI_set1 cardinal_set1.
Qed.

Lemma nds_tn_prop2 n X:  natp n -> \0c <c n -> nds_tn_ax X n ->
  (nds_tn_S X n) =
  unionf n (fun a => fun_image (\Po (n -s1 a))
    (fun K => oopow  (odegree (X \0c)) *o (csumb (K +s1 a) (the_cnf_lc \o X)) 
           +o the_cnf_rem (X a)))
  +s1 \0c.
Proof.
move => nN np ax.
set ee := (odegree (X \0c)).
have nds_tn_axE i: i <c n ->
  [/\ \0o <o (the_cnf_lc (X i)), (the_cnf_lc (X i))  <o omega0,
    the_cnf_rem (X i) <o oopow ee &
    X i = oopow ee *o (the_cnf_lc (X i)) +o (the_cnf_rem (X i))].
   move => lin.
   move: ax => [ax1 [e ea eb]].
   by move: (the_cnf_split (ax1 i lin)); rewrite (eb _ lin) /ee (eb _ np).
have tn8 K s: 
  inc K (\Po n) -> inc s (permutations (cardinal K)) ->
  nonempty K ->
  nds_sc_Ktau X K s =
  oopow ee *o nds_sc_K (the_cnf_lc \o X) K
          +o the_cnf_rem (X (nth_elt K (Vf s \0c))).
  set m := cardinal K;move => /setP_P sb sp nek.
  move:(sub_smaller sb); rewrite (card_nat nN); rewrite -/m  => ckn.
  have mN:=(NS_le_nat ckn nN).
  have mz:= (card_ne0_pos (CS_nat mN) (card_nonempty1 nek)).
  pose c z := the_cnf_lc (X (nth_elt K z)).
  pose r z := the_cnf_rem (X (nth_elt K z)).
  have aux: forall i, i <c m ->
    [/\ \0o <o c i, c i <o omega0,  r i <o oopow ee
        & X (nth_elt K i) = oopow ee *o c i +o r i ]. 
    move => i l1.
    have sKN: sub K Nat by move => t /sb/(NltP nN) => h; apply(NS_lt_nat h nN).
    move: (nth_elt_inK (NS_lt_nat l1 mN) sKN l1) => /sb/(NltP nN).
    by move/nds_tn_axE.
  have h2: ordinalp ee.
    by move:(proj2 ax) => [e ea eb]; rewrite /ee (eb _ np).
  have h3 i: i <c m-> \0o <o c i /\ r i <o omega0 ^o ee by move =>  /aux []. 
  have h4 i: i <c m -> c i <o omega0  by move => /aux[].
  have -> : nds_sc_K (the_cnf_lc \o X) K = osumf c m.
     by rewrite osum_of_nat // => i /h4 /olt_omegaP.
  rewrite /nds_sc_Ktau -(nds_same_deg_s_perm mN mz h2 h3 h4 sp).
  apply:(osumf_exten mN)  => i /(NltP mN) lin.
  have /aux [_ _ _]//: (Vf s i) <c m.
  apply/(NltP mN).
  move/(permutationsP): sp => [[[fs _] _] ss ts]; Wtac.
have H s: nds_sc_Ktau X emptyset s = \0c.
  by rewrite  /nds_sc_Ktau cardinal_set0/nds_sc osum_f0. 
set c := (the_cnf_lc \o X).
set_extens v.
  move/setUf_P => [K ka /funI_P [s sp sv]].
  case:(emptyset_dichot K) => ke; first by rewrite sv ke H; fprops.
  apply/setU1_P; left; apply /setUf_P.
  move: (nth_elt_prop7 nN ka sp ke); set a := (nth_elt K (Vf s \0c)) => ak.
  move/setP_P:(ka) => kb.
  have an: inc a n by apply: kb.
  ex_tac; apply /funI_P;exists (K -s1 a).
    by apply/setP_P => t/setC1_P [ha hb]; apply/setC1_P; split=> //; apply: kb.
  by  rewrite sv (tn8 _ _ ka sp ke) (setC1_K ak) (nds_sc_Kval c nN ka).
case/setU1_P => h1; last first.
  rewrite h1; apply/setUf_P; exists emptyset; first by apply: setP_0i.
  apply/funI_P; exists (identity (cardinal emptyset)); last by rewrite H.
  apply:permutation_id. 
move/setUf_P: h1 => [a aN /funI_P[K /setP_P Kb ->]].
have nk1: ~ (inc a K) by move /Kb => /setC1_P[].
have eq1:= setU1_K nk1.
have ha: inc (K +s1 a) (\Po n).
  apply /setP_P => t/setU1_P; case; [by move/Kb => /setC1_P[] |  by move ->].
have hb: inc a (K +s1 a) by fprops.
have Kne: nonempty (K +s1 a) by ex_tac.
move: (nth_elt_prop8 nN ha hb) => [f fp aaa].
apply/setUf_P; ex_tac;apply/funI_P; ex_tac.
by rewrite (tn8 _ _ ha fp Kne) - aaa  (nds_sc_Kval c nN ha).
Qed.


Lemma nds_tn_max X n: natp n -> \0c <c n -> nds_tn_ax X n ->
  nds_tn_C X n <=c ndsC n.
Proof.
move => nN np ax.
rewrite /ndsC /nds_tn_C (nds_tn_prop2 nN np ax); set F:= (fun a : Set => _).
suff h: cardinal (unionf n F) <=c  (n *c \2c ^c cpred n).
  have w:cardinalp (n *c \2c ^c cpred n) by fprops.
  case: (inc_or_not \0c (unionf n F)) => ha. 
    rewrite (setU1_eq ha); apply:(cleT h (cleS0 w)).
  by rewrite (csucc_pr ha); apply /(cleSSP (CS_cardinal _) w).
apply: (cleT(csum_pr1_bis n F));rewrite cprodC - csum_of_same.
apply:csum_increasing; aw; trivial  => a abn; rewrite !LgV//.
rewrite - (nds_C_prop nN abn); apply:fun_image_smaller.
Qed.

Definition sumpow2 K := csumb K (fun z => \2c ^c z).

Lemma sumpow2_N1 K: finite_set K -> sub K Nat -> natp (sumpow2 K).
Proof.
move => ha hb; apply:finite_sum_finite; saw.
hnf;aw => x xk; rewrite LgV//; apply:(NS_pow NS2 (hb _ xk)).
Qed.

Lemma sumpow2_N2 n a K:
  natp n -> inc K (\Po (n -s1 a)) -> natp (sumpow2 K).
Proof.
move => nN /setP_P h1; move:(sub_trans h1 (@sub_setC _ _)) => h2.
have h3:= (sub_trans h2 (NS_inc_nat nN)).
exact (sumpow2_N1 (sub_finite_set h2 (finite_set_nat nN)) h3).
Qed.

Lemma sumpow2_rec a K: inc a K -> 
  sumpow2 K = sumpow2 (K -s1 a) +c (\2c ^c a). 
Proof. 
by move=> aK; rewrite -{1} (setC1_K aK) /sumpow2 (csumA_setU1 _ (@setC1_1 a K)).
Qed.

Lemma sumpow2_inj n K1 K2 : natp n ->
  (forall i, inc i K1 -> i<c n) -> (forall i, inc i K2 -> i<c n) ->
   sumpow2 K1 = sumpow2 K2 -> K1 = K2.
Proof.
pose p K n :=  (forall i, inc i K -> i <c n).
have bd: forall n, natp n -> forall K, p K n -> sumpow2 K <c \2c ^c n.
  apply: Nat_induction.
    move => K h; rewrite cpowx0.
    case:(emptyset_dichot K). 
      by move => ->; rewrite /sumpow2 /csumb  csum_trivial; fprops; aw.
    by move => [i /h /clt0].
  move => m mN Hrec K kP.
  set K':= K -s1 m.
  have /Hrec r1:(p K' m).
     by move => i /setC1_P [/kP /(cltSleP mN) h1 h2].
  rewrite (cpow_succ _ mN) cprodC - csum_nn.
  case: (inc_or_not m K) => ink.
     rewrite (sumpow2_rec ink); apply:csum_Mlteq; fprops.
  rewrite -(setC1_eq ink); apply: (clt_leT r1); apply:csum_M0le; fprops.
move => nN; move: n nN K1 K2; apply: Nat_induction.
  move => K1 K2 h1 h2 sv.
  case:(emptyset_dichot K1) => ha.
      case:(emptyset_dichot K2) => hb; first by rewrite ha hb.
     by move:hb => [i/h2 /clt0].
   by move:ha => [i/h1 /clt0].
move => n nN Hrec K1 K2 h1 h2.
have kk1:(p (K1 -s1 n) n). 
  by move => i /setC1_P [/h1 /(cltSleP nN) hu hv].
have kk2:(p (K2 -s1 n)  n). 
  by move => i /setC1_P [/h2 /(cltSleP nN) hu hv].
have l1:= bd _ nN _ kk1. 
have l2:= bd _ nN _ kk2.
have pN:= (NS_pow NS2 nN).
case: (inc_or_not n K1) => nk1; case: (inc_or_not n K2) => nk2.
+ have hh1:= (NS_lt_nat l1 (NS_pow NS2 nN)).
  have hh2:= (NS_lt_nat l2 (NS_pow NS2 nN)).
  rewrite (sumpow2_rec nk1) (sumpow2_rec nk2) => eq2.
  move:(csum_eq2r pN hh1 hh2 eq2) => eq3.
  by rewrite - (setC1_K nk1) - (setC1_K nk2) (Hrec _ _ kk1 kk2 eq3).
+ move: l2; rewrite (sumpow2_rec nk1) (setC1_eq nk2) => l2 eq.
  move: (csum_M0le (sumpow2 (K1 -s1 n)) (CS_nat pN)).
  by rewrite csumC eq => /(cltNge l2).
+ move: l1; rewrite (setC1_eq nk1)  (sumpow2_rec nk2) => l1 eq.
  move: (csum_M0le (sumpow2 (K2 -s1 n)) (CS_nat pN)).
  by rewrite csumC - eq =>  /(cltNge l1).
+ by rewrite - (setC1_eq nk1) - (setC1_eq nk2); apply: Hrec.
Qed.

Lemma omega_monom_inj a b c d: 
  natp a -> natp b -> natp c -> natp d ->
  omega0 *o a +o b = omega0 *o c +o d -> (a = c /\ b = d).
Proof.  
move => aN bN cN dN eq1.
have aux: forall u v, natp u -> natp v -> natp (omega0 *o u +o v) -> u = \0c. 
  move => u v uN vN /(oltP OS_omega) h; ex_middle h1.
  have l1:= (oprod_Mle1 OS_omega (ord_ne0_pos (OS_nat uN) h1)).
  by case:(oleNgt (oleT l1 (osum_Mle0 (proj32 l1) (OS_nat vN)))).
case: (czero_dichot (CS_nat aN))=> az.
  move: eq1; rewrite az oprod0r (osum0l (OS_nat bN)) => eq1.
  rewrite eq1 in bN.
  by rewrite eq1 (aux _ _ cN dN bN)  oprod0r (osum0l (OS_nat dN)). 
case: (czero_dichot (CS_nat cN))=> cz.
  move: eq1; rewrite cz oprod0r (osum0l (OS_nat dN)) => eq1.
  case: (nesym (proj2 az));rewrite - eq1 in dN; exact:(aux _ _ aN bN dN). 
move:(the_cnf_omega_kj (conj aN az) bN) => [_ [_ e1 e2]]. 
move:(the_cnf_omega_kj (conj cN cz) dN) => [_ [_ e3 e4]]. 
by rewrite eq1 in e1 e2; rewrite e1 in e3; rewrite  e2 in e4.
Qed.

Definition nds_base := fun i => omega0 *o (\2c ^c i) +o i.

Lemma nds_base_prop i (u := nds_base i) : natp i ->
  [/\ odegree u = \1c, the_cnf_lc u = (\2c ^c i) & the_cnf_rem u = i].
Proof.
move => iN.
by case: (proj2 (the_cnf_omega_kj (conj (NS_pow NS2 iN) (cpow2_pos i)) iN)).
Qed.

Lemma nds_tn_ex_ax n:  natp n -> nds_tn_ax nds_base n.
Proof.
move => nN; split.
  move => i lin; move:(NS_lt_nat lin nN) => yN.
  exact:(proj1 (the_cnf_omega_kj (conj (NS_pow NS2 yN) (cpow2_pos _)) yN)). 
exists \1o; first by apply:OS1.
by move => i lin; move:(NS_lt_nat lin nN) => /nds_base_prop [].
Qed.

Lemma nds_tnmax_ex n: natp n -> 
  (nds_tn_S nds_base n) =
  unionf n (fun a => fun_image (\Po (n -s1 a))
    (fun K => omega0 *o (sumpow2 (K +s1 a)) +o a)) +s1 \0c.
Proof. 
move => nN.
have npr:=(NS_inc_nat nN).
case: (czero_dichot (CS_nat nN)) => np.
  rewrite /nds_tn_S np setP_0 setUf_0 set0_U2 setUf_1 cardinal_set0.
  apply: set1_pr1.
    apply: funI_setne; move: (permutation_id \0c) => h; ex_tac.
  move => i /funI_P [z zz ->].
  by rewrite /nds_sc_Ktau /nds_sc cardinal_set0 osum_f0.
rewrite (nds_tn_prop2 nN np (nds_tn_ex_ax nN)).
f_equal; apply: setUf_exten => a /npr an; apply: funI_exten => K KP.
rewrite (proj33 (nds_base_prop an)) (proj31 (nds_base_prop NS0)).
rewrite oopow1; apply: f_equal2; [apply: f_equal | exact].
apply: csumb_exten => t tK; apply: (proj32 (nds_base_prop _)).
move/setP_P: KP => KP.
by case/setU1_P: tK; [ move/KP => /setC1_P [/npr] |  move->].
Qed.

Lemma nds_tn_ex_val n: natp n ->  nds_tn_C nds_base n = ndsC n.
Proof.
move => nN.
have ha: forall i, natp i -> natp (\2c ^c i).
  move => i; apply:(NS_pow NS2).
rewrite /nds_tn_C (nds_tnmax_ex nN).
have sk2_S a K: inc K (\Po (n -s1 a)) -> 
   sumpow2 (K +s1 a) = sumpow2 K +c \2c ^c a. 
  move => /setP_P KS.
  by rewrite /sumpow2 (csumA_setU1) // => /KS /setC1_P [].
have sk2_N a K: inc a n ->  inc K (\Po (n -s1 a)) -> natp (sumpow2 (K +s1 a)).
  move => aN KP. rewrite (sk2_S a K KP); apply:(NS_sum (sumpow2_N2 nN  KP)).
  exact:(NS_pow NS2 (NS_inc_nat nN aN)).
rewrite csucc_pr; last first.
  move/setUf_P => [a an /funI_P [K Ka]]; apply/nesym.
  have aN :=  (NS_inc_nat nN an).
  move:(OS_nat (sk2_N _ _ an Ka)) => o1.
  move/(osum2_zero (OS_prod2 OS_omega o1) (OS_nat aN)) => /proj1.
  apply:(oprod2_nz OS_omega o1 omega_nz); rewrite (sk2_S _ _ Ka) => /csum_nz.
  by move => [_] /cpow2_nz.
rewrite /ndsC; congr csucc;rewrite csum_pr4_bis; last first.
  move => i j iN jN; case (equal_or_not i j) => eij; [by left | right].
  apply:disjoint_pr => u /funI_P [K1 K1p uv1] /funI_P [K2 K2p uv2]; case eij.
  rewrite uv1 in uv2.
  move: (sk2_N _ _ iN K1p)  (sk2_N _ _ jN K2p) => e2 e4.
  by case: (omega_monom_inj e2  (NS_inc_nat nN iN) e4 (NS_inc_nat nN jN) uv2).
set F := fun a:Set => _.
suff H: forall a, inc a n -> F a = \2c ^c cpred n.
   rewrite - {2} (card_nat nN)  (cprod2cl). 
   by rewrite cprodC - csum_of_same; apply: csumb_exten => i ib /=; apply: H.
move => a an; rewrite - (nds_C_prop nN an) /F cardinal_fun_image //.
move => K1 K2 K1a K2a /= eq1.
move:(sk2_N _ _ an K1a) (sk2_N _ _ an K2a) => s1N s2N.
have aN := (NS_inc_nat nN an).
move: (proj1 (omega_monom_inj s1N aN s2N aN eq1)).
rewrite (sk2_S _ _ K1a) (sk2_S _ _ K2a) => eq2.
move:(csum_eq2r (NS_pow NS2 aN) (sumpow2_N2 nN K1a) (sumpow2_N2 nN K2a)  eq2).
apply: (sumpow2_inj nN) => i.
  by move/setP_P: K1a => h; move=> /h /setC1_P /proj1/(NltP nN).
  by move/setP_P: K2a => h; move=> /h /setC1_P /proj1/(NltP nN).
Qed.


Lemma nds_tn_value n: natp n -> nds_tn_sup n = ndsC n.
Proof.
move => nN.
case: (czero_dichot (CS_nat nN)) => np.
  by rewrite np nds_tn_zero /ndsC cprodC cprod0r succ_zero.
move: (nds_tn_def nN) => [_ _ [X hx eq1] hu].
apply: cleA; first by rewrite - eq1; exact:(nds_tn_max nN np hx).
rewrite - (nds_tn_ex_val nN); apply: (hu _ (nds_tn_ex_ax nN)).
Qed.


Definition nds_type_nor X n k e:=
 [/\ nds_type X n k, ordinalp e,
    forall i, i<c k -> odegree (X i) = e  &
    forall i, k <=c i -> i <c n -> e <o odegree (X i)].

Lemma nds_type_nor_ex X n k: 
   natp n -> \0c <c k -> k <=c n -> nds_type X n k ->
   exists Y e,  [/\ nds_type_nor Y n k e &
                      nds_card Y n = nds_card X n].
Proof.
move => nN knz lekn [ha [m [om h1]]].
set E := Zo _ _ => ce.
have ax:nds_ax X n by move => i /ha/proj32_1.
have sk: sub  k n by case: lekn.
have kN:=(NS_le_nat lekn nN).
have sE: sub E n by apply: Zo_S.
case: (nth_elt_dbl_prop2 nN sE); set f := Lf _ _ _; move => fp; rewrite ce.
move: (nds_card_perm_inv nN ax fp); set Y:= fun i =>X (Vf f i) => yv fv.
rewrite yv.
exists Y,m; split; last reflexivity.
move:fp => /Zo_P [/functionsP [ff sf tf] bf] .
have sisf: sub  k (source f) by rewrite sf.
move: (cardinal_image sisf (proj1 bf));rewrite- fv (card_nat  kN) => ck.
have pa i: i <c n -> \0o <o (Y i).
  move => /(NltP nN) ii; apply: ha; apply/(NltP nN); Wtac.
have pb i: i <c n -> m <=o odegree (Y i).
  move => /(NltP nN) ii; apply: h1;apply/(NltP nN); Wtac.
have pc: forall i, i <c k -> odegree (Y i) = m.
  move => i /(NltP kN) ik. 
  have/Zo_hi //: inc (Vf f i) E
    by rewrite fv; apply/(Vf_image_P ff sisf); ex_tac.
have pd: (Zo n (fun i => odegree (Y i) = m)) = k.
  set_extens t. 
    move => /Zo_P [ta tb].
    have: inc (Vf f t) E by apply:Zo_i; [Wtac | apply: tb ].
    rewrite fv => /(Vf_image_P ff sisf) [u usf].
    move: ta (sk _ usf); rewrite - sf => hb hc hd.
    by rewrite(proj2(proj1 bf) _ _ hb hc hd).
  move => ta; apply /Zo_P;split; first by apply: sk.
  by apply: pc; apply /(NltP kN). 
have pe i: k <=c i -> i <c n -> m <o odegree (Y i).
  move => ki kin; split; [ by apply: pb | move => sa ].
  have: inc i k.
    by rewrite - pd; apply /Zo_P; split; [by apply/(NltP nN) | done].
   by move/(NltP kN) => /(cleNgt ki).
have pf:nds_type Y n k.
  split;[ exact|  exists m]; rewrite pd (card_nat kN); split; exact.
split; exact.
Qed.


Lemma nds_tn_C_exten Z Y n: natp n -> same_below Z Y n ->
  nds_tn_C Z n = nds_tn_C Y n.
Proof.
move => nN h.
have aux: forall K s, inc K (\Po n) ->
    inc s (permutations (cardinal K)) -> nds_sc_Ktau Z K s = nds_sc_Ktau Y K s.
  move => K s /setP_P Kb /permutationsP [[[fs _] _ ] ss tf].
  have fsK:=(sub_finite_set Kb (finite_set_nat nN)).
  have ckN: natp (cardinal K) by apply /NatP.
  have sKN:=(sub_trans Kb (NS_inc_nat nN)).
  apply:(osumf_exten ckN) => i lin; apply: h.
  have h1: Vf s i <c cardinal K.
     by apply /(NltP ckN); Wtac; rewrite ss;apply /(NltP ckN).
  apply/(NltP nN); apply: Kb; apply: (nth_elt_inK (NS_lt_nat h1 ckN) sKN h1).
rewrite /nds_tn_C /nds_tn_S; apply: f_equal.
set_extens t; move => /setUf_P [K KP /funI_P [s sp ->]]; 
  apply /setUf_P; ex_tac; apply/funI_P;first  ex_tac. 
exists s; [ done |  symmetry;exact:(aux K s KP sp)].
Qed.
  
Section NdsStudy.
Variables (X: fterm) (n k e: Set).
Hypothesis nN: natp n.
Hypothesis knz: \0c <c k. 
Hypothesis kln: k <c n.
Hypothesis Xax: nds_type_nor X n k e.

Let pL f i := k <=c Vf f i.
Let pS f i := Vf f i <c k.
Let fL f := intersection (Zo Nat (fun i => i <c n /\ pL f i)).

Lemma nds_fL_prop f: inc f (permutations n) -> 
  [/\ natp (fL f), (fL f) <=c k,  (fL f) <c n,  pL f (fL f) & 
      forall j, j <c (fL f) -> pS f j].
Proof.
move => fp; rewrite /fL; set E:= Zo _ _.
move/permutationsP:(fp) =>[[injf [ff fs]] sf tf].
have nee: nonempty E.  
  move:(perm_int_surj nN fp kln) => [i lin si].
  exists i;apply:Zo_i;[ by apply: (NS_lt_nat lin nN) | split => //].
  rewrite /pL si; apply: (cleR (proj31_1 kln)).
have seN: sub E Nat by apply:Zo_S.
move: (inf_Nat seN nee); set i:= intersection E. 
move => [/Zo_P [iN [ha hb]] etc].
have kN:= (NS_lt_nat kln nN).
have aux:  forall j, j <c i -> pS f j.
  move => j lji.
  move: (clt_ltT lji ha) => ljn; move/(NltP nN): (ljn) => jb.
  have /(NltP  nN) /proj31_1 cf: (inc (Vf f j) n) by Wtac.
  case: (cleT_el (proj31_1 kln) cf) => // jfL; case:(cltNge lji).
  by apply: etc; apply:(Zo_i  (NS_lt_nat ljn nN)).
split => //.
case: (NleT_el iN kN) => // lki.
have aux2: forall i, i <=c k -> pS f i. 
  by move => j jk; apply: aux; exact: (cle_ltT jk lki).
rewrite /pS in aux2.
have h3: sub (Nintc k) (source f).
  move => j/(NintcP kN) ja; rewrite sf; apply/(NltP nN);exact:(cle_ltT ja kln).
have su1: sub (Vfs f (Nintc k)) k.
  move => t /(Vf_image_P ff h3) [u /(NintcP kN) ul1 ->].
  by apply/(NltP kN); apply: aux2.
move: (sub_smaller su1).
rewrite(cardinal_image h3 injf) (card_Nintc kN) (card_nat kN) => l1.
case: (cleNgt l1 (cltS kN)).
Qed.

Lemma nds_fL_prop2 f m (q:= (fL f) +c m) :
  inc f (permutations n) -> natp m -> q <c n ->
  (forall j, j<c m -> pL f ((fL f) +c j)) ->
  [\/ (m = n -c k /\ forall j, j <c n -> q <=c j -> pS f j),
     pL f q |
    q <> \0c /\
    exists p, [/\ natp p, csucc (q +c p) <c n,
       pL f (csucc (q +c p)),
       pL f (cpred q) &
       forall z, z <=c p -> pS f (q +c z) ]].
Proof.
move => fp mN inb Hi.
move: (nds_fL_prop fp) => [sa _ sb sc sd].
move/permutationsP: fp => [bf sf tf].
have ff: function f by fct_tac.
have qN: natp q by apply: NS_sum.
have kN:= (NS_lt_nat kln nN).
set E1 := Zo Nat (fun z => [/\ z <c n, pL f z & q <=c z]).
set E2:= Zo Nat (fun z => [/\ z <c n, pL f z & z <c q]).
set E3:= n -s k.
have: disjoint E1 E2. 
  by apply: disjoint_pr => u /Zo_P[_ [_ _ ha]]/Zo_P[_ [_ _ /(cleNgt ha)]].
move/csum2_pr5;rewrite - csum2cl - csum2cr.
have E3tf: sub E3 (target f) by rewrite tf;move => t /setC_P [].
have ->: E1 \cup E2 = fun_image E3 (Vf (inverse_fun f)).
   set_extens t => h.
    have[ha hb]: t <c n /\ k <=c Vf f t by case/setU2_P:h => /Zo_P[_ [ha hb _]].
    have tsf: inc t (source f) by rewrite sf; apply /(NltP nN).
    have se:=(inverse_V2 bf tsf).
    apply/funI_P; exists (Vf f t); last by exact.
    apply /setC_P; split; [ Wtac | by move/(NltP kN) => /(cleNgt hb)].
  move/funI_P:h => [z zi ->]; move: (E3tf _ zi) => ft.
  have eq2:=(inverse_V bf ft).
  have zt:= (inverse_Vis bf ft).
  rewrite sf in zt; move /(NltP nN): zt => lt1.
  have izN:= (NS_lt_nat lt1 nN).
  move/setC_P: zi => [/(NS_inc_nat nN) zN hb].
  case: (NleT_el kN zN) => zz; last by case: hb; apply /(NltP kN).
  by case: (NleT_el qN izN) => lea; apply /setU2_P; [left | right];
     apply:Zo_i => //; split => //; rewrite /pL eq2.
have ->: E2 = fun_image m (fun z => (fL f) +c z).
  set_extens t.
    move/Zo_P => [tN [tn h tq]]; apply/funI_P.
    case: (cleT_el (proj31_1 sb)(proj31_1 tq)) => le1.
      move:tq; rewrite - (cdiff_pr le1) => tq.
      move /(NltP mN):(csum_lt2l sa (NS_diff (fL f) tN) mN tq) => di; ex_tac.
    by move: h (sd _ le1);rewrite /pL /pS => ua /(cleNgt ua).
  move /funI_P => [z /(NltP mN) zi ->]; apply/Zo_P.
  have lt1:=  (clt_ltT (csum_Meqlt sa zi) inb).
  have sf1 := (csum_Meqlt sa zi).
  split; [ exact:(NS_lt_nat lt1 nN) | by split => //; apply: Hi ].
rewrite cardinal_fun_image; last first.
  by move => i j /E3tf /(inverse_V bf) {2}<- /E3tf  /(inverse_V bf) {2}<- ->.
rewrite cardinal_fun_image; last first.
  by move => i j im jm /=; apply:(csum_eq2l sa); apply: (NS_inc_nat mN).
rewrite /E3 -/(_ -c _) (card_card (CS_nat mN)) => cc.
have cE1N: natp (cardinal E1).
  by move:(NS_diff k nN); rewrite cc => /(NS_in_suml (CS_cardinal E1)).
have ci:= (CS_nat mN).
case: (cleT_ell (CS_diff n k) ci) => cink.
+ constructor 1; split; first by symmetry.
  move => j ljn lqj.
  have jsf: inc j (source f) by rewrite sf; apply /(NltP nN).
  move:(Vf_target ff jsf); rewrite tf; move/(NltP nN) => ha.
  case: (cleT_el (proj31_1 kln) (proj31_1 ha)) => hb; last exact.
  rewrite cink - {1} (csum0l ci) in cc.
  move:(esym(csum_eq2r mN NS0 cE1N cc))=>/card_nonempty hw.
  have jE1: inc j E1 by apply:Zo_i; [apply: (NS_lt_nat ljn nN) | ].
  empty_tac1 j.
+ by move: (csum_M0le (cardinal E1) ci);rewrite csumC - cc=> /(cltNge cink).
+ have lt1: Vf f q <c n by apply/(NltP nN); Wtac; rewrite sf;apply/(NltP nN).
  case: (cleT_el (CS_nat kN) (proj31_1 lt1)) => lt2; first by constructor 2.
  constructor 3.
  case: (equal_or_not m \0c) => inz.
    by move:sc lt2; rewrite /pL /q inz (csum0r (proj31_1 sb))=> ua /(cleNgt ua).
  split; first by move/csum_nz; case. 
  case: (emptyset_dichot E1) => nee.
    by move: (proj2 cink); rewrite cc nee cardinal_set0 (csum0l ci).
  have seB: sub E1 Nat by apply:Zo_S.
  move: (inf_Nat seB nee) =>[]; set j:= intersection E1 => ja jb.
  move/Zo_P: ja => [jN [ljn jc lqj]].
  have eq0:= (cdiff_pr lqj).
  case: (equal_or_not (j -c q) \0c) => eq1.
    by move: jc; rewrite - eq0 eq1 (csum0r (proj31 lqj)) /pL => /(cltNge lt2).
  move: (cpred_pr (NS_diff _ jN) eq1)=> []. 
  set p :=  (cpred (j -c q)) => pN pv.
  have eq4:q +c csucc p = j by rewrite - pv.
  have eq2: csucc (q +c p) = j by rewrite - (csum_nS _ pN).
  move: (cpred_pr mN inz) => [ia ib].
  have eq3: q = csucc (fL f +c (cpred m)) by rewrite -(csum_nS _ ia) - ib.
  move: (cpred_pr1 (CS_sum2 (fL f) (cpred m))); rewrite - eq3 => eq5.
  move: (cltS ia); rewrite - ib => /Hi; rewrite - eq5 => eq6.
  exists p; rewrite eq2; split => //.
  move => z /(cltSleP pN) zm.
  move:(csum_Meqlt qN zm); rewrite eq4 => l1.
  have ra := (clt_ltT l1 ljn).
  have qnz:= (NS_lt_nat ra nN).
  move/(NltP nN):(ra); rewrite - sf => /(Vf_target ff); rewrite tf.
  move /(NltP nN) => /proj31_1 fzn.
  case: (cleT_el (CS_nat kN) fzn) => // l2.
  have: (inc (q +c z) E1).
    by apply:Zo_i => //; split => //; apply:(Nsum_M0le _ qN).
  by move/jb => /(cltNge l1).
Qed.

Lemma nds_fL_prop3 i l f:
  inc f (permutations n) -> natp i -> natp l ->
  (csucc (csucc (i +c l))) <c n ->
  pL f i -> 
  (forall j, j <=c l -> pS f (csucc (i+c j))) ->
  pL f (csucc (csucc (i +c l))) ->
  exists g, 
     [/\ inc g (permutations n), nds_sc X n f = nds_sc X n g,
        forall j, j<c (csucc i) -> Vf f j = Vf g j & pL g (csucc i)].
Proof.
move => fp iN lN ltil2n p1 p2 p3.
set i1:= csucc i; set il2:= csucc (csucc (i +c l)); set il3:= csucc il2.
set il:= csucc (i +c l).
rewrite -/il2 in ltil2n.
have il1N:= NS_succ (NS_sum iN lN).
have il2N:= (NS_lt_nat ltil2n nN).
have il3N: inc il3 Nat by apply:NS_succ il2N. 
have i1N:= NS_succ iN.
have i2N:= NS_succ i1N.
have leil3n: il3 <=c n by apply/cleSltP.
have lti1il2: i1 <c il2.
  rewrite /i1 /il2; apply:cltSS. 
  exact (cle_ltT (Nsum_M0le l iN) (cltS (NS_sum iN lN))). 
have lti1n:=(clt_ltT lti1il2 ltil2n).
have ltin:= (clt_ltT (cltS iN) lti1n).
have Ha: inc il2 n by apply /(NltP nN).
have Hb: inc i1  n by apply /(NltP nN).
have le1:=(cleS (NS_succ iN)).
move: (transposition_prop nN Ha Hb).
set g := Lf _ _ _.
move => [gp gssi gsi ngsi ggi].
move/permutationsP: (gp) => [[[fg _] _] sg tg].
move/permutationsP: (fp) => [[[ff _] _] sf tf].
set h:= f \co g.
have fgP: f \coP g by split => //; ue.
have pa: forall j, j <c csucc i -> Vf f j = Vf h j.
  move => j jsi.
  have jb: inc j n by apply /(NltP nN); exact : (clt_ltT jsi lti1n).
  have jb': inc j (source g) by ue.
  have ne1:= (proj2(clt_ltT jsi (lti1il2))).
  rewrite /h compfV//; rewrite ngsi //; exact (proj2 jsi).
have pb: forall j, inc j  n -> il3 <=c j -> Vf f j = Vf h j.
  move => j jsi l3.
  have jb': inc j (source g) by ue.
  have lt1:= (clt_leT (cltS il2N) l3).
  have ne2:= (nesym (proj2 (clt_ltT lti1il2 lt1))).
  have ne1:= nesym(proj2 lt1).
  by rewrite /h compfV // ngsi.
have hp:= (permutation_Sc fp gp).
have hh: pL h i1 by rewrite /h /pL compfV //; [ rewrite gsi | rewrite sg].
suff: nds_sc X n f = nds_sc X n h by exists h; split; exact.
move: Xax => [[hw _] _ hu hv]. 
have ax: nds_ax X n by move => z /hw /proj32_1.
move: (nds_ax_perm nN ax fp) (nds_ax_perm nN ax hp).
rewrite /nds_sc. 
set Y:= (fun z => X (Vf f z)).
set Z:= (fun z => X (Vf h z)); move => [aY _ ] [aZ _].
move: (cdiff_pr leil3n); set m := _ -c _ => mv.
have mN: natp m by apply: (NS_diff _ nN).
rewrite - mv in aY aZ |- *. 
rewrite (osum_fA il3N mN aY) (osum_fA il3N mN aZ).
apply: f_equal2.
   apply: (osumf_exten mN) => z zm.
   have le2:il3 <=c z +c il3 by apply: csum_Mle0; fprops.
   have le3: inc (z +c il3) n. 
     by apply/(NltP nN); rewrite - mv (csumC il3); apply:csum_Mlteq.
   by rewrite /Y/Z pb.
set a := X (Vf f i); set b := X(Vf f i1); set c:= X(Vf f il2).
have il2sg: inc il2 (source g) by  ue.
have i1sg: inc i1 (source g) by  ue.
have ib: inc i n by apply /(NltP nN).
have ig: inc i (source g) by ue.
rewrite 2! (osum_fS _ il2N).
rewrite {1} /Z {1}/Y /h (compfV fgP il2sg) gssi -/b -/c.
have le2: csucc (csucc i) <=c il2.
  apply/(cleSSP (CS_succ i) (CS_succ ((i +c l)))).
  apply/(cleSSP (CS_nat iN) (CS_sum2 i l)).
  apply: (Nsum_M0le _ iN).
move: (cdiff_pr le2); set m1 := _ -c _ => m1v.
have m1N: inc m1 Nat by apply: (NS_diff _ il2N).
rewrite mv in aY aZ.
have aY': nds_ax Y (csucc (csucc i) +c m1).
  move => z; rewrite m1v => l1; apply: aY; exact:(clt_ltT l1 ltil2n).
have aZ': nds_ax Z (csucc (csucc i) +c m1).
  move => z; rewrite m1v => l1; apply: aZ; exact:(clt_ltT l1 ltil2n).
have ha:= cltS iN.
have hb:= (proj2 (clt_ltT ha lti1il2)).
rewrite - m1v (osum_fA i2N m1N aY') (osum_fA i2N m1N aZ').
rewrite 2! (osum_fS _ i1N) 2! (osum_fS _ iN).
rewrite {2 3} /Y {2 3} /Z /h (compfV fgP ig)(compfV fgP i1sg).
rewrite gsi (ngsi _ ib hb (proj2 ha)) -/a -/b -/c.
set A:= osumf _ m1.
set B:= osumf _ i.
have <-: A = (osumf (fun z => Z (z +c csucc (csucc i))) m1).
  apply: (osumf_exten m1N) => j lej.
  have [_ /nesym ltb]:i1 <c j +c csucc (csucc i).
     apply/(cleSltP i1N); apply:csum_Mle0; fprops.
  have lta: j +c csucc (csucc i) <c il2.
     rewrite - m1v (csumC _ m1); exact: (csum_Mlteq i2N lej).
  have hc: inc (j +c csucc (csucc i)) (source g).
    rewrite sg; apply/(NltP nN); rewrite - mv /il3 - m1v.
    rewrite (csum_Sn _ (NS_sum i2N m1N)) (csumC _ m1).
    apply: (clt_ltT lta); rewrite (csumC m1) m1v.
    apply /(cltSleP (NS_sum il2N mN)) /csum_M0le; fprops.
  by rewrite /Y/Z /h (compfV fgP hc) (ngsi _ _ (proj2 lta) ltb) // - sg. 
have <-: B = osumf Z i.
  apply: (osumf_exten iN) => j lej; rewrite /Y/Z pa //.
  exact: (clt_ltT lej ha).
have oA: ordinalp A.
   apply: (OS_osumf m1N) => j jl1; apply: aY'.
   rewrite (csumC _ m1); exact:(csum_Mlteq i2N jl1).
have oB: ordinalp B.
   apply: (OS_osumf iN) => j jl1; apply: aY; exact (clt_ltT jl1 ltin).
have fis: Vf f i <c n by apply/(NltP nN); Wtac.
have fil2s: Vf f il2 <c n by apply/(NltP nN); Wtac.
have fi1s: Vf f i1 <c n by apply/(NltP nN); Wtac.
have da:= (hv _ p1 fis).
have dc:= (hv _ p3 fil2s); rewrite -/c in dc.
move: (hu _(p2 _ (cle0n lN))).
rewrite (csum0r (CS_nat iN)); rewrite -/b => db.
have d1a: odegree b <o odegree a by ue.
have d1c: odegree b <o odegree c by ue.
move: (hw _ fis) (hw _ fil2s)(hw _ fi1s); rewrite -/a -/b -/c => ap cp bp.
move: (proj32_1 ap)(proj32_1 bp)(proj32_1 cp) => oa ob oc.
have hc: l +c (csucc (csucc i)) = il2.
  by rewrite csumC (csum_Sn _ i1N) (csum_Sn _ iN).
have [eq1 eq2]: (A +o a = a /\ A +o c = c).
  have: m1 <=c l.
    apply:(csum_le2l i2N m1N lN).
    rewrite m1v (csumC _ l) hc; apply:cleR; fprops.
  rewrite /A; move:m1N; move:(m1); apply: Nat_induction.
    by move => _; rewrite osum_f0 (osum0l oa) (osum0l oc).
  move => q qN Hrec sql.
  have ql:= (cleT (cleS qN) sql).
  move:(Hrec ql) => [eqa eqb].
  set d := (Y (q +c csucc (csucc i))).
  have oD: ordinalp (osumf (fun z => Y (z +c csucc (csucc i))) q).
    apply: (OS_osumf qN) => j jlt; apply:aY.
    have jlt1:=(clt_leT jlt ql).
    move:(csum_Mlteq i2N  jlt1); rewrite hc => hd;apply:(clt_ltT hd ltil2n).
  have ql': q <c l by apply/(cleSltP qN).
  have lt2: q +c csucc (csucc i) <c n.
     move:(csum_Mlteq i2N ql'); rewrite hc => hd; exact(clt_ltT hd ltil2n).
  have lt3: Vf f (q +c csucc (csucc i)) <c k.
    have eq3: q +c (csucc (csucc i)) = csucc (i +c (csucc q)).
      rewrite (csum_nS _ i1N) csumC. 
      by rewrite (csum_Sn _ iN) (csum_nS _ qN).
    by move: (p2 _ sql); rewrite - eq3. 
  move: (hu _ lt3); rewrite -/(Y _ ) -/d => dd.
  have dp: \0o <o  d.
    by apply: hw; apply /(NltP nN); Wtac; rewrite sf;apply /(NltP nN).
  have ot:= proj32_1 dp.
  have d2a: odegree d <o odegree a by ue.
  have d2c: odegree d <o odegree c by ue.
  rewrite !(osum_fS _ qN) - (osumA ot oD oa) eqa.
  rewrite - (osumA ot oD oc) eqb.
  by rewrite (ord_negl_p7  dp ap d2a)(ord_negl_p7 dp cp d2c).
rewrite (osumA ob oa oB) (ord_negl_p7 bp ap d1a)  (osumA oA oa oB) eq1.
rewrite (osumA oc oa oB) (osumA oA (OS_sum2 oc oa) oB) (osumA oA oc oa) eq2.
rewrite (osumA ob (OS_sum2 oc oa) oB)(osumA ob oc oa) (ord_negl_p7 bp cp d1c).
done.
Qed.


Lemma nds_fL_prop4 f:
  inc f (permutations n) -> exists g,
  [/\ inc g (permutations n), nds_sc X n f = nds_sc X n g,
      fL f  = fL g &
      forall i, i<c n -c k -> pL g ((fL g) +c i) ].
Proof.
move => fp.
move: (NS_diff k nN) (cleR (CS_diff n k)).
move:{1 2 4} (n -c k); apply: Nat_induction. 
  by move => _; exists f; split => // i /clt0.
move => q qN Hrec le1.
move:(cleS qN) => le2.
move: (Hrec (cleT le2 le1)) => [g [ga gb gc gd]].
move: (nds_fL_prop ga) => [aa ab ac ad ae].
have kN:= (NS_lt_nat kln nN).
move: (csum_Meqlt kN (clt_leT (cltS qN) le1)).
rewrite (cdiff_pr (proj1 kln))=> lt2.
move: (cle_ltT (csum_Mleeq q ab) lt2) => lt3.
case:(nds_fL_prop2 ga qN lt3 gd).
+ by move => [ua _]; move: le1 (cltS qN); rewrite - ua => sa /(cleNgt sa).
+ move => h; exists g; split; [ exact | exact| exact | ].
  move => j; move/(cltSleP qN) => ljq.
  case: (equal_or_not j q) => ejq; [ ue | by apply: gd].
set q1:= fL g +c q.
move => [q1p [ j [jN ja jb jc jd]]].
move: (cpred_pr (NS_sum aa qN) q1p); rewrite -/q1; move=> [je ef].
have eg:=(csum_Sn j je).
have sa: csucc (csucc (cpred q1 +c j)) <c n by rewrite -eg - ef.
have sc: pL g (csucc (csucc (cpred q1 +c j)))  by rewrite -eg - ef.
have sb: (forall j0, j0 <=c j -> pS g (csucc (cpred q1 +c j0))). 
  by move => j1 jl1; rewrite -(csum_Sn _ je) - ef; apply: jd.
move:(nds_fL_prop3 ga je jN sa jc sb sc) => [g1 [r1 r2 r3 r4]].
rewrite -ef in r3 r4.
have sw: fL g = fL g1.
  move: (nds_fL_prop r1) => [aa' _ _ ad' ae'].
  have af: fL g <=c q1 by apply /csum_M0le; fprops.
  have q1N: natp q1 by move:(NS_succ je); rewrite - ef.
  case: (NleT_el aa' q1N) => ag; last first. 
    by move:(ae' _ ag) r4; rewrite /pS/pL => l1 /(cltNge l1).
  case:(NleT_ell aa aa') => l3.  
  + exact.
  + move: (ae' _ l3) ad; rewrite /pL/pS (r3 _ (clt_leT l3 ag)).
    move => l1 l2; case: (cltNge l1 l2).
  + move: (ae _ l3) ad'; rewrite /pL/pS (r3 _ (clt_leT l3 af)).
    move => l1 l2;case: (cltNge l1 l2).
exists g1;split; [exact | ue| by rewrite gc | ].
move => i /(cltSleP qN) isa; rewrite - sw.
case:(equal_or_not i q) => eqi; first by rewrite eqi.
move: (csum_Meqlt aa (conj isa eqi));rewrite /pL => /r3 <-. 
apply: (gd _ (conj isa eqi)).
Qed.

Lemma nds_fL_prop5 f:
  inc f (permutations n) -> exists K s1 s2,
  [/\ sub K k, inc s1 (permutations (cardinal K)), 
     inc s2 (permutations (n -c k)) &
     nds_sc X n f = nds_sc (fun z => X (k +c z))  (n-c k) s2 +o
       nds_sc_Ktau X K s1].
Proof.
move/nds_fL_prop4 => [g [gp -> _ p1]]; rewrite /nds_sc_Ktau.
move:(nds_fL_prop gp) => [qN p2 p3 p4 p5].
move/permutationsP:gp =>[[injg [fg sjg]] sg tg].
rewrite sg tg in sjg.
set q := (fL g); rewrite -/q in qN p1 p2 p3 p4 p5.
have nkN:=(NS_diff k nN).
have le3:=(cdiff_pr3 nN p2 (proj1 kln)).
have eq2:=(cdiff_pr (proj1 p3)). 
have eq3:=(cdiff_pr le3).
have eq4:=(cdiff_pr (proj1 kln)).
have nqN:= (NS_diff q nN).
have qnkN:= (NS_sum qN nkN).
have kN:= (NS_lt_nat kln nN).
have lt1: q +c (n -c k) <=c n.
  move: (csum_Mleeq n p2); rewrite - {1} eq4 (csumC k) csumA (csumC _ k).
  by move/(csum_le2l kN qnkN nN).
have sK: sub q (source g) by rewrite sg; exact (proj33 (proj1 p3)).
move: (cardinal_image sK injg);set K := Vfs g q.
rewrite (card_nat qN) => cK.
have iKP: forall i, inc i K <-> exists2 j, inc j q & i = Vf g j.
  move => i; split; by move /(Vf_image_P fg sK). 
have h0:sub K k.
 by move => t /iKP [j jE ->]; apply/(NltP kN); apply: p5; apply/(NltP qN).
set E1:= (q +c (n -c k)) -s q.
set K1 := Vfs g E1.
have sK1: sub E1 (source g).
  move => t /setC_P [/(NltP qnkN) ha _]; rewrite sg; apply/(NltP nN).
  exact: (clt_leT ha lt1).
have iK1P: forall i, inc i K1 <-> exists2 j, inc j E1 & i = Vf g j.
  move => i; split; by move /(Vf_image_P fg sK1). 
have cK1: cardinal K1 = n -c k.
  move: (cardinal_image sK1 injg); rewrite -/K1.
  have ha:=(proj33 (Nsum_M0le (n-c k) qN)).
  rewrite  (cardinal_setC4 ha (finite_set_nat qnkN)).
  by rewrite (card_nat qnkN) (card_nat qN) csumC (cdiff_pr1 nkN qN).
have sK1': sub K1  (n -s k).
  move => t/iK1P [j ja ->]; apply/setC_P; split.
    by move: (Vf_target fg (sK1 _ ja)); rewrite tg.
  have jN: natp j by move:(sK1 j ja); rewrite sg => /(NS_inc_nat nN).  
  move/setC_P:ja => [/(NltP qnkN) ja jb]; dneg h.
  case: (cleT_el (CS_nat qN) (proj31_1 ja)); last by move/(NltP qN).
  move => le1; move:(cdiff_pr le1) => eqa.
  rewrite - eqa in ja.
  have jc := (csum_lt2l qN (NS_diff q jN) nkN ja).
  move: (p1 _ jc); rewrite eqa /pL => jd.
  by move/(NltP kN):h => /(cleNgt jd).
move: (proj33 (proj1 kln)) (finite_set_nat nN) => s1 fn.
move: (sub_finite_set (@sub_setC n k) fn) => ha.
have hb: K1 =c n -s k. 
  by rewrite  (cardinal_setC4 s1 fn)  (card_nat kN) (card_nat nN) cK1. 
move:(strict_sub_smaller_contra ha sK1' hb) => eq5.
clear s1 fn ha hb.
have p6: forall i, i<c n -> q +c (n -c k) <=c i -> pS g i.
  move => i li1 li2; rewrite /pS; ex_middle h.
  have isn: inc i (source g) by rewrite sg; apply/(NltP nN).
  have: inc (Vf g i) K1.
      rewrite eq5; apply/setC_P; split; [Wtac | by move/(NltP kN)].
  move/(iK1P) => [j /setC_P [/(NltP qnkN) ja jb] eqa].
  have jsg: inc j (source g).
    by move: (clt_ltT (clt_leT ja li2) li1) => /(NltP nN); rewrite sg.
  move: ((proj2 injg) i j isn jsg eqa) => eij; rewrite - eij in ja.
  case: (cltNge ja li2).
have sKb: sub K n by move => t /iKP [ u /sK usf ->]; Wtac.
have sKN:=(sub_trans sKb (NS_inc_nat nN)).
have fsK:=(sub_nat_finite nN sKb).
move:(nth_elt_bf sKN fsK) ; set FK:= Lf _ _ _; move => [pa pb].
have sFK: source FK = q by rewrite /FK cK; aw.
have tFK: target FK = K by rewrite /FK cK; aw.
have ax2: lf_axiom (nth_elt K) q K.
  move => t /(NltP qN) lt2; move:(lt2); rewrite - cK => lt3.
  by move:(nth_set7 (NS_lt_nat lt2 qN) sKN lt3) => [/setC_P []].
pose s1' i := (Vf (inverse_fun FK) (Vf g i)).
have ax1: lf_axiom s1' q q.
  move => t ta;rewrite - sFK; apply:(inverse_Vis pa); rewrite tFK.
  by apply /iKP; exists t. 
have pc: forall i, inc i q -> Vf FK (s1' i) = Vf g i. 
  move => i iE; rewrite /s1' (inverse_V pa) // tFK; apply/iKP; ex_tac.
set s1 := Lf s1' q q .
have s1fb: bijection s1.
   apply:lf_bijective; first by exact.
      move => u v uE vE eq6.
      move: (f_equal (Vf FK) eq6); rewrite (pc _ uE) (pc _ vE) => eq7.
      exact: (proj2 injg _ _ (sK _ uE) (sK _ vE) eq7).
   rewrite - sFK;move => y ye.
   move: (Vf_target (proj1(proj1 pa)) ye); rewrite tFK => /iKP [u us eq1].
   by rewrite - sFK in us; ex_tac; rewrite /s1'- eq1 (inverse_V2 pa ye).
have s1perm: inc s1 (permutations q).
apply/permutationsP; rewrite /s1; saw. 
set Ec:= (n -c k).
pose s2' z := (Vf g (q +c z) -c k).
have pd1: forall z, z <c n -c k -> inc (q +c z) (source g).
  move => z zi.
  move:(csum_Meqlt qN (clt_leT zi le3)).
  by rewrite eq2 => /(NltP nN);rewrite - sg => ha.
have ax3: lf_axiom s2' Ec Ec.
  move => z /(NltP nkN)  zi.
  move: (Vf_target fg (pd1 _ zi)); rewrite tg  => /(NltP nN) lt2.
  rewrite -/q - cK in lt2.
  move:(p1 _ zi);rewrite /pL /s2' - cK=> fzi.
  apply/(NltP nkN); exact(cdiff_pr7 fzi lt2 nN).
have pd: forall z, z <c n -c k -> (s2' z) +c k = Vf g (q +c z).
  move => z /p1;rewrite /pL /s2' - cK=> fzi.
  by rewrite csumC; apply:cdiff_pr. 
set s2 := Lf s2' Ec Ec.
have s2fb: bijection s2.
  apply:bijective_if_same_finite_c_inj.
  + by rewrite /s2; aw.
  + by rewrite /s2/Ec; aw; apply:finite_set_nat.
  + apply: lf_injective => // u v /(NltP nkN) ue /(NltP nkN) ve eq.
    move: (f_equal (fun z => z +c k) eq).
    rewrite (pd _ ue) (pd _ ve) => eq7.
    move:(proj2 injg _ _ (pd1 _ ue)(pd1 _ ve) eq7).
    exact:(csum_eq2l qN (NS_lt_nat ue nkN) (NS_lt_nat ve nkN)).
have s2perm: inc s2 (permutations (n -c k)).
  apply/permutationsP; rewrite /s2; saw.
exists K, s1, s2; rewrite cK;split => //. 
rewrite /nds_sc_Ktau.
set X1:= osumf (fun z => X (nth_elt K (Vf s1 z))) q.
have r1: X1 = osumf (fun z => X (Vf g z)) q.
  apply: (osumf_exten qN) => i /(NltP qN) iE.
  have vK: inc (Vf g i) (target FK) by rewrite tFK;apply/iKP; ex_tac.
  rewrite /s1/s1' !LfV// -{2} (inverse_V pa vK) {2} /FK cK.
  rewrite LfV// - sFK; apply: (inverse_Vis pa vK).
set X2:= osumf (fun z=> X (Vf g (z +c q))) (n -c k).
have r2: X2 = osumf (fun z => X (k +c Vf s2 z)) (n -c k).
   apply:(osumf_exten nkN).
   move => z znk /=;rewrite (csumC z) (csumC k) - (pd _ znk) /s2 LfV//.
   by apply/(NltP nkN).
move: Xax => [ [hw _] oe  hu hv].
have aX: nds_ax (fun z => X (Vf g z)) n. 
   move => z /(NltP nN) zi. 
   rewrite - sg in zi.
   by move:(Vf_target fg zi); rewrite tg => /(NltP nN) /hw /proj32_1.
have aX2: nds_ax (fun z=> X (Vf g (z +c q))) (n -c q).
  move=> z zle1; apply: aX; move: (csum_Mlteq qN zle1).
  by rewrite (csumC (_ -c _)) eq2.
rewrite /nds_sc - {1} eq2;rewrite - eq2 in aX.
rewrite - eq3 in aX2.
rewrite (osum_fA qN nqN aX) -/X1 - r1 - eq3.
rewrite (osum_fA nkN (NS_diff (n -c k) nqN) aX2) - r2; congr (_ +o X1).
have knz1:= (cdiff_nz kln).
move: (cpred_pr nkN knz1) => [nk1N nk1v].
rewrite /X2 nk1v (osum_fS _ nk1N).
set X3:= osumf _ _.
set X4:= osumf _ _.
set a := X _.
move:(cltS nk1N); rewrite -nk1v => /p1; rewrite /pL csumC => le1.
have lt2: inc ((cpred (n -c k) +c q)) (source g).
  rewrite csumC;apply/pd1; rewrite {2} nk1v; apply:(cltS nk1N).
have lt3: Vf g (cpred (n -c k) +c q) <c n.
  by apply/(NltP nN); rewrite - {2}tg; Wtac.
move: (hw _ lt3) (hv _ le1 lt3); rewrite -/a => ap da.
have oa:= proj32_1 ap.
have oX4: ordinalp X4. 
  apply:(OS_osumf nk1N) => t ta;apply: aX2.
  move: (clt_leT ta (cleS nk1N)); rewrite - nk1v => sa.
  exact: (clt_leT sa (Nsum_M0le ((n -c q) -c (n -c k)) nkN)).
set wa:=((n -c q) -c csucc (cpred (n -c k))).
have wN: natp wa by rewrite /wa; fprops.
have wa1: (wa +c (n -c k)) =  (n -c q).
  by rewrite /wa -nk1v (csumC (_ -c _)) cdiff_pr. 
have oX3:ordinalp X3. 
  apply:(OS_osumf wN) => z zw;apply: aX2;rewrite eq3.
  by move: (csum_Mlteq nkN zw); rewrite  -nk1v wa1.
rewrite (osumA oX3 oa oX4); congr (_ +o X4).
rewrite /X3 -/wa - nk1v.
have eq7: ((wa +c (n -c k)) +c q) = n by rewrite  wa1 csumC eq2//.
have: wa +c ((n -c k) +c q) <=c n by rewrite csumA eq7; fprops.
clear eq7 wa1.
move: wa wN; apply: Nat_induction.
  by move => _ ; rewrite osum_f0 (osum0l oa).
move=> j jN Hrec.
have sN:= NS_sum jN (NS_sum nkN qN).
rewrite (csum_Sn _ jN) => /(cleSltP sN) ha.
have oS: ordinalp (osumf (fun z => X (Vf g ((z +c (n -c k))  +c q))) j).
  apply:(OS_osumf jN) => z zl; apply:aX2;rewrite eq3.
  move:(csum_Mlteq nkN zl) => hc.
  move:(Nsum_M0le (j +c (n -c k)) qN); rewrite csumC => hd.
  rewrite csumA in ha; move: (cdiff_pr7 hd ha nN).    
  rewrite (cdiff_pr1 (NS_sum jN nkN) qN) => he; exact: (clt_ltT hc he).
rewrite (osum_fS _ jN) - csumA.
set j0 := j +c ((n -c k) +c q).
have j0b: inc j0 (source g) by rewrite sg; apply/(NltP nN).
rewrite -/j0 in ha.
have hb:q +c (n -c k) <=c j0. 
  rewrite /j0 csumC (csumC j); apply:csum_M0le; fprops.
move:(Vf_target fg j0b); rewrite tg => /(NltP nN) => hc.
have ofp:= hw _ hc.
have oft:= proj32_1 ofp.
rewrite - (osumA oft oS oa) (Hrec (proj1 ha)).
move: (hu _ (p6 _ ha hb)) => hd.
rewrite - hd in da; exact: (ord_negl_p7 ofp ap da).
Qed.

Lemma nds_fL_prop6 v (X2:= (fun z => X (k +c z))):
  inc v (nds_sums X n) -> 
  exists v1 v2, [/\ inc v1 (nds_tn_S X k), inc v2 (nds_sums X2 (n -c k)) &
   v = v2 +o v1].
Proof. 
move => /funI_P [z zp ->].
move: (nds_fL_prop5 zp) => [K [s1 [s2 [/setP_P pa pb pc ->]]]].
set v1:=nds_sc (fun z0 => X (nth_elt K z0)) (cardinal K) s1.
set v2:=nds_sc (fun z => X (k +c z)) (n -c k) s2.
have v2p:inc v2 (nds_sums X2 (n -c k)) by apply/funI_P; ex_tac.
exists v1, v2; split => //;apply/setUf_P; ex_tac; apply/funI_P; ex_tac.
Qed.

Lemma nds_tg9 (X2:= (fun z => X (k +c z))):
  nds_sums X n = 
     unionf (nds_tn_S X k) (fun v1 => fun_image (nds_sums X2 (n -c k)) 
         (fun v2 => v2 +o v1)).
Proof.
set_extens v.
  move /nds_fL_prop6 => [v1 [v2 [va vb vc]]].
  apply/setUf_P; ex_tac; apply/funI_P; ex_tac.
move/setUf_P => [v1 /setUf_P [K /setP_P Kp/funI_P [s1 s1p va]]].
move => /funI_P [v2 /funI_P [s2 s2p ->]] => ->; rewrite va; apply/funI_P.
set K' := k -s K.
set q := cardinal K.
have kN:=(NS_lt_nat kln nN).
move:(sub_smaller Kp); rewrite (card_nat kN); rewrite -/q => leqk.
have lqn:=(cle_ltT leqk kln).
have qN:= NS_lt_nat lqn nN.
have nkN:=(NS_diff k nN).
have qnN:= (NS_sum qN nkN).
have sKN:= (sub_trans Kp (NS_inc_nat kN)).
have sK'N: sub K' Nat by exact: (sub_trans (@sub_setC k K) (NS_inc_nat kN)).
have cK': cardinal K' = k -c q.
  by rewrite (cardinal_setC4 Kp (finite_set_nat kN)) (card_nat kN).
have qqn:=(Nsum_M0le (n -c k) qN).
have kqN:= (NS_diff q kN).
have q'N: natp (cardinal K') by rewrite cK'.
have knk:= (cdiff_pr (proj1 kln)).
set qn := q +c (n -c k); rewrite -/qn in qnN qqn.
have qnkq: qn +c (k-c q) = n.
  by rewrite -knk /qn (csumC q) - csumA (cdiff_pr leqk) csumC.
have lqnn: qn <=c n by rewrite - qnkq; apply:(Nsum_M0le _ qnN).
have sBkBn:=(proj33 (proj1 kln)).
move/permutationsP: (s1p) => [bs1 ss1 ts1]; move: (proj1(proj1 bs1)) => fs1.
move/permutationsP: (s2p) => [bs2 ss2 ts2]; move: (proj1(proj1 bs2)) => fs2.
pose s i := Yo (i <c q) (nth_elt K (Vf s1 i)) 
     (Yo (i <c qn) (Vf s2 (i -c q) +c k) (nth_elt K' (i -c qn))). 
have pa: forall i, i<c q -> s i = (nth_elt K (Vf s1 i)).
   by move => i liq; rewrite /s; Ytac0.
have pb: forall i, i<c q -> inc (s i) K.
   move => i iq; rewrite (pa _ iq).
   have p1: inc (Vf s1 i) q by rewrite /q; Wtac; rewrite ss1; apply/(NltP qN).
   move/(NltP qN): p1 => ha. 
   apply:(nth_elt_inK (NS_lt_nat ha qN) sKN ha).
have pc: forall i, qn <=c i -> s i =  (nth_elt K' (i -c qn)).
   rewrite /s => i le1;Ytac h; first by case:(cleNgt qqn (cle_ltT le1 h)).
   by rewrite (Y_false (cleNgt le1)).
have pd: forall i, qn <=c i -> i <c n -> inc (s i) K'.
  move => i l1 l2; rewrite (pc _ l1); move:(NS_lt_nat l2 nN) => iN.
  apply:(nth_elt_inK (NS_diff qn iN) sK'N); rewrite cK'. 
  by apply:(cdiff_Mlt kqN iN l1); rewrite csumC qnkq.
have pe: forall i, q <=c i -> i <c qn -> s i = (Vf s2 (i -c q) +c k).
  by move => i l1 l2; rewrite /s (Y_true l2) (Y_false (cleNgt l1)). 
have pf: forall i, q <=c i -> i <c qn ->
  [/\ s i = (Vf s2 (i -c q) +c k), inc (Vf s2 (i -c q)) ((n -c k)) &
   inc (s i) (n -s k)].
  move => i l1 l2; rewrite (pe i l1 l2).
  have iN:= NS_lt_nat l2 qnN. 
  rewrite - {1}(cdiff_pr l1) /qn in l2.
  have sa:= (csum_lt2l qN (NS_diff q iN) nkN l2).
  have sb: inc (Vf s2 (i -c q)) (n -c k). 
    by Wtac; rewrite ss2; apply/NltP.
  move/(NltP nkN):(sb) => sc.
  move:(csum_Mlteq kN sc); rewrite (csumC (n -c k)) knk => sd.
  split => //; apply/setC_P; split; first by apply /(NltP nN).
  move/(NltP kN); move:(Nsum_Mle0 (Vf s2 (i -c q)) kN). 
  move =>  ua ub; case: (cltNge ub ua).
have ax: forall i, inc i n -> inc (s i) n.
  move => i /(NltP nN) lin.
  case: (cleT_el  (CS_nat qN) (proj31_1 lin)) => le1.
    case: (cleT_el (CS_nat qnN) (proj31_1 lin)) => le2.
      by move: (pd i le2 lin) => /setC_P [/sBkBn ha _].
    by move:(pf _ le1 le2) =>[_ _ /setC_P []].
  by move: (pb i le1) =>  /Kp /sBkBn.
have sjs: forall j, inc j n -> exists2 i, inc i n &  j = s i. 
  move => j /(NltP nN) ljn.
  have jN:= (NS_lt_nat ljn nN).
  case:(cleT_el (CS_nat kN) (proj31_1 ljn)) => lkj.
    have l1: (j -c k)  <c (n-c k).
      rewrite - (cdiff_pr lkj) - knk in ljn.
      exact: (csum_lt2l kN (NS_diff k jN) nkN ljn).
    move: (perm_int_surj nkN s2p l1) => [i1 l2 iv].
    have i1N := NS_lt_nat l2 nkN.
    have l3:=(csum_Meqlt qN l2).
    move:(proj31 (pf _ (Nsum_M0le i1 qN) l3)).
    rewrite {2} csumC (cdiff_pr1 i1N qN) iv (csumC _ k) (cdiff_pr lkj) => <-.
    exists (q +c i1) => //; apply/(NltP nN); exact:(clt_leT l3 lqnn).
  case: (inc_or_not j K) => jK.
      move:(nth_elt_surj sKN qN jK) => [i ia ->].
      move:(perm_int_surj qN s1p ia) => [i1 ib <-].
      rewrite - (pa _ ib); exists i1 => //; apply/(NltP nN). 
      exact:(clt_ltT ib lqn).
  have jK': inc j K' by apply/setC_P; split => //; apply/(NltP kN).
  move:(nth_elt_surj sK'N q'N jK') => [i ia ->].
  rewrite cK' in ia.
  move: (csum_Meqlt qnN ia); rewrite qnkq => /(NltP nN) ic; ex_tac.
  rewrite (pc _ (Nsum_M0le i qnN)) csumC cdiff_pr1 //.
  apply:(NS_lt_nat ia kqN).
set sigma := Lf s n n.
have sp: inc sigma (permutations n).
   rewrite /sigma; apply/permutationsP; hnf; saw.
   apply:bijective_if_same_finite_c_surj; aw; trivial.
     by apply:finite_set_nat.
   by apply: lf_surjective.
ex_tac.
move: Xax => [[qa _] qb qd qe].
have: nds_ax (fun z => X (Vf sigma z)) n.
  rewrite /sigma;move => y /(NltP nN) ys; rewrite LfV//.
  by move:(ax _ ys) => /(NltP nN) /qa/proj32_1.
rewrite /nds_sc - {1 3}qnkq => ax2.
have ax3: nds_ax (fun z=> X (Vf sigma z)) (q +c (n -c k)).
  move => z z1; apply: ax2; rewrite qnkq;  exact:(clt_leT z1 lqnn).
rewrite (osum_fA qnN kqN ax2) (osum_fA qN nkN ax3) /nds_sc_Ktau/nds_sc.
set A := osumf _ _; set B := osumf _ _; set C' := osumf _ _.
set A' := osumf _ _; set B' := osumf _ _.
have ea: A = A'. 
  apply: (osumf_exten nkN) => i l1.
  have iB:= NS_lt_nat l1 nkN.
  move: (csum_Mlteq qN l1) ; rewrite (csumC (n -c k))- /qn => l2.
  have ha: inc (i +c q) n by apply /(NltP nN); exact:(clt_leT l2 lqnn).
  move:(Nsum_M0le i qN); rewrite csumC => hb.
  by rewrite /sigma LfV// (pe _ hb l2) /X2 csumC cdiff_pr1.
have eb: B = B'. 
  apply: (osumf_exten qN) => i l1.
  have ib:inc i n by apply /(NltP nN); exact:(clt_ltT l1 lqn).
    by rewrite /sigma LfV// - ( pa _ l1).
have oa: ordinalp A'.
   apply:(OS_osumf nkN) => i l1; apply: ax3.
   by move: (csum_Mlteq qN l1);rewrite (csumC q).
have ob: ordinalp B'.
   apply:(OS_osumf qN) => i l1; apply: ax2; rewrite qnkq.
   exact:(clt_ltT l1 lqn).
have oc: ordinalp C'.
   apply:(OS_osumf kqN) => i l1; apply: ax2. 
   by rewrite (csumC qn);apply:csum_Mlteq. 
rewrite (osumA oc oa ob) - ea; apply: (f_equal2 _ _ eb).
have knz1:= (cdiff_nz kln).
move: (cpred_pr nkN knz1) => [nk1N nk1v].
rewrite /A nk1v (osum_fS _ nk1N) /X2.
set C:= osumf _ _ .
move: (cltS nk1N); rewrite - nk1v => eq1.
have oc': ordinalp C.
  apply:(OS_osumf nk1N) => i lin.
  have ha:inc i (source s2). 
    rewrite ss2; apply/(NltP nkN); exact (clt_ltT lin eq1).
  move:(Vf_target fs2 ha); rewrite ts2 => /(NltP nkN) lt1.
  by move:(csum_Meqlt kN lt1); rewrite knk => /qa /proj32_1.
have ha: inc (cpred (n -c k)) (source s2).
   by rewrite ss2; apply/(NltP nkN); rewrite {2} nk1v; apply: cltS.
move:(Vf_target fs2 ha); rewrite ts2 => /(NltP nkN) lt1.
move:(csum_Meqlt kN lt1); rewrite knk => hb.
move:(Nsum_M0le (Vf s2 (cpred (n -c k))) kN) => hc.
move: (qa _ hb) (qe _ hc hb);set a:= X _ => ap da.
rewrite (osumA oc (proj32_1 ap) oc'); congr (_ +o C).
rewrite /C'.
have hd: forall i, i<c k -c q ->  (Vf sigma (i +c qn)) <c k.
  move => i lik.
  move:(csum_Meqlt qnN lik); rewrite qnkq => l1.
  move: (Nsum_M0le i  qnN) => l2.
  move/(NltP nN):(l1) => iN.
  by rewrite csumC /sigma LfV//; move: (pd _ l2 l1) => /setC_P []/(NltP kN).
have he: forall i, i<c k -c q -> let b := X (Vf sigma (i +c qn)) in
  \0o <o b /\  odegree b = e.
  move => i l1; move:(hd _ l1) => sa; split.
   exact: (qa _ (clt_ltT sa kln)).
   exact:(qd _ sa).
symmetry.
move:kqN (cleR (CS_nat kqN)).
have oa':=(proj32_1 ap).
move: {-3} (k -c q); apply: Nat_induction.
  by rewrite osum_f0 (osum0l oa').
move => i iN Hrec le1.
rewrite (osum_fS _ iN).
move/(cleSltP iN): (le1) => /he [].
set b :=  (X (Vf sigma (i +c qn)))  => bp db.
have ikq:=(cleT (cleS iN) le1).
have oc'': ordinalp (osumf (fun z : Set => X (Vf sigma (z +c qn))) i).
   apply: (OS_osumf iN) => j jli.
   exact: (proj32_1(proj1 (he _ (clt_leT jli ikq)))).
rewrite - db in da.
rewrite - (osumA (proj32_1 bp) oc'' oa').
by rewrite (Hrec ikq) (ord_negl_p7  bp ap da).
Qed.

End NdsStudy.

Lemma nds_alt_prop1 n: natp n ->  \1c <c n ->
   exists k, [/\ \0c <c k, k <c n & nds_F n <=c ndsC k *c nds_F (n -c k)].
Proof.
move => nN np.
have np2: \2c <=c n by rewrite - succ_one; apply/(cleSltP NS1).
move: (nds_F_FA_def nN np2) => [_ [k [kp kln <-]]].
exists k; split => //.
move: (nds_FA_def nN kp (proj1 kln)).
move=> [pa _ _ [X [pb pc <-]]].
move:(nds_type_nor_ex nN kp (proj1 kln) pc)=> [Y [e [ ya <-]]].
rewrite /nds_card (@nds_tg9 Y n k e nN kln ya).
clear pa pb pc X.
set F:= (fun v1 : Set => _).
set E :=  (nds_tn_S Y k).
move:(csum_pr1_bis E F).
set g1:= (Lg E (fun a => cardinal (Vg (Lg E F) a))).
have <-: csum g1 = csumb E  (fun a => cardinal (F a)).  
  apply:csumb_exten => t tx; rewrite LgV //.
set g2 := cst_graph E (nds_F (n -c k)).
have sd: domain g1 = domain g2 by rewrite /g1/g2; aw.
have kN:= NS_lt_nat kln nN.
have nkN:= (NS_diff k nN).
move: (nds_f_def nkN) => [pe _ pf pg].
move: ya => [[pa _] pc pd _].
suff le1:forall x, inc x (domain g1) -> Vg g1 x <=c Vg g2 x.
  move:(csum_increasing sd le1).
  rewrite [csum g2]csum_of_same cprodC - cprod2cl /E -/(nds_tn_C _ _) => ha hb.
  have ax:  nds_tn_ax Y k.  
    by split; [move => i ik; apply: pa (clt_ltT ik kln) | exists e].
  move: (cprod_Mlele (nds_tn_max kN kp ax) (cleR (CS_nat pe))) => hc.
  exact:(cleT (cleT hb ha) hc).
rewrite /g1 /g2; aw => a abn; rewrite !LgV//. 
have /pg:nds_ax(fun z => Y (k +c z))  (n -c k).
  move => i ink; move:(csum_Meqlt kN ink).
  by rewrite(cdiff_pr (proj1 kln)) => /pa /proj32_1.
apply:cleT; apply:fun_image_smaller.
Qed.

Definition nds_shift X := (oopow \2o) *o X.
Definition nds_small_nz x :=  \0o <o x /\ x <o oopow omega0.
Definition nds_small_ax (X:fterm) n := forall k, k <c n -> nds_small_nz (X k).
Definition nds_merge k X :=
  fun i => Yo (i <c k) (nds_base i) (nds_shift (X (i -c k))).


Lemma nds_small_nz_shift x: nds_small_nz x -> nds_small_nz (nds_shift x).
Proof.
move => [ha hb]; split; first by apply: (oprod2_pos (oopow_pos OS2) ha).
move: (oprod_Meqlt hb (oopow_pos OS2)).
by rewrite - (opow_sum OS_omega OS2 OS_omega) (osum_int_omega olt_2omega).
Qed.

Lemma nds_small_base i: natp i -> nds_small_nz (nds_base i).
Proof.
move => iN.
move: (proj31 (nds_base_prop iN)) => dx.
move: (proj1 (nds_tn_ex_ax (NS_succ iN)) i (cltS iN)) => bp; split => //.
move: (proj2 (the_cnf_p4 bp)); rewrite dx => h; apply: (olt_leT h).
apply: (opow_Mo_le); rewrite osucc_one; apply: ole_2omega.
Qed.

Definition nds_binomp x := x <o oopow \2o.

Lemma nds_binomp_base i: natp i -> nds_binomp (nds_base i).
Proof.
move => iN.
move: (proj31 (nds_base_prop iN)) => dx.
move: (proj1 (nds_tn_ex_ax (NS_succ iN)) i (cltS iN)) => bp.
move: (proj2 (the_cnf_p4 bp)); rewrite dx => h; apply: (olt_leT h).
rewrite osucc_one; apply: oleR; apply: (OS_oopow OS2).
Qed.

Lemma nds_binomp_add u v: nds_binomp u -> nds_binomp v ->
  nds_binomp (u +o v).
Proof.
by move => ha hb; apply: indecomp_prop2 (indecomp_prop4 OS2).
Qed.

Lemma nds_add_sb_inj x y u v: ordinalp x -> ordinalp y ->
  nds_binomp u -> nds_binomp v ->
  (nds_shift x) +o u = (nds_shift y) +o v -> x = y /\ u = v.               
Proof.
move => ox oy bu bv eq.
set a := oopow \2o *o x +o u; set b := oopow \2o *o y +o v. 
set c := oopow \2o.
have ou:= proj31_1 bu.
have ov:= proj31_1 bv.
have oc := OS_oopow OS2.
have oa := OS_sum2 (OS_prod2 oc ox) ou.
have ra:  odiv_pr0 a c x u by  split.
have rb:  odiv_pr0 a c y v by  rewrite /a -/(nds_shift _) eq; split => //.
exact: (odivision_unique oa oc ra rb).
Qed.

Lemma nds_merge_prop1 k X n:
  natp k -> natp n -> opos_below X n -> 
  opos_below (nds_merge k X)  (k +c n).
Proof.
move => kN nN hX i lin.
rewrite/nds_merge.
move:(NS_lt_nat lin (NS_sum kN nN)) => iN.
case:(NleT_el kN iN) => lik; last by Ytac0; exact:(proj1 (nds_small_base iN)).
rewrite (Y_false (cleNgt lik)).  move: (cdiff_pr lik) => iv.
have lt2: i -c k <c n by apply:(csum_lt2l kN (NS_diff k iN) nN); ue.
apply: (oprod2_pos (oopow_pos OS2) (hX _ lt2)).
Qed.

Lemma nds_merge_prop2 k X n:
  natp k -> natp n -> opos_below X n ->
  (forall i, i <c k -> odegree (nds_merge k X i) = \1c) /\
  (forall i, k <=c i -> i <c (k +c n) -> 
     \1c <o (odegree (nds_merge k X i))).
Proof.
move => kN nN hX; rewrite /nds_merge; split.
  move => i lik; Ytac0;exact:(proj31 (nds_base_prop (NS_lt_nat lik kN))) => dx.
move => i lik lin.
move:(NS_lt_nat lin (NS_sum kN nN)) => iN.
rewrite (Y_false (cleNgt lik)).
move: (cdiff_pr lik) => iv.
have lt2: i -c k <c n by apply:(csum_lt2l kN (NS_diff k iN) nN); ue.
move: (hX _ lt2) => xp.
rewrite (odegree_prod (oopow_pos OS2) xp) (odegree_opow OS2).
apply:(olt_leT  olt_12); apply: (osum_Mle0 OS2 (OS_degree (proj32_1 xp))).
Qed.


Lemma osum_shift n X: natp n -> nds_ax X n ->
  ordinalp (osumf X n) /\
  osumf (fun i => (nds_shift (X i))) n = nds_shift (osumf X n).
Proof.
move:n; apply: Nat_induction.
   rewrite !osum_f0 /nds_shift oprod0r; split; fprops.
move => n nN Hrec /(true_below_rec nN) [/Hrec [qa qb] ov].
rewrite !(osum_fS _ nN); split; first by apply: (OS_sum2 ov qa).
by rewrite qb /nds_shift (oprodD ov qa (OS_oopow OS2)).
Qed.

Lemma nds_card_shift n X:
  natp n -> nds_ax X n -> 
  nds_card X n = nds_card  (fun i => nds_shift (X i)) n.
Proof.
move => nN ax.
rewrite /nds_card /nds_sums.
set E := permutations n; set A := fun_image _ _;set B := fun_image _ _.
apply /card_eqP; exists (Lf nds_shift A B).
have aux f: inc f E ->
   ordinalp (nds_sc X n f) /\
    nds_sc (fun i => nds_shift (X i)) n f = nds_shift(nds_sc X n f).
  move => /permutationsP[bf sf tf]; apply:(osum_shift nN).
  move => i /(NltP nN) tn; apply: ax;apply/(NltP nN); Wtac; fct_tac.
saw;apply:lf_bijective.
+ move => z /funI_P [f fp ->]; apply /funI_P; exists f => //.
  by rewrite (proj2 (aux _ fp)).
+ move => u v /funI_P [a az ->] /funI_P [b bz ->].
  move:(proj1 (aux _ az)) (proj1 (aux _ bz)) => sa sb.
  apply: (oprod2_simpl sa sb (oopow_pos OS2)).
+ move => z /funI_P [f fp ->]; exists(nds_sc X n f). 
  apply /funI_P; exists f => //.
  by apply: (proj2 (aux _ fp)).
Qed.

Lemma nds_card_merge n k Y: natp n ->  k <c n ->
  opos_below Y (n -c k) ->
  nds_card (nds_merge k Y) n = ndsC k *c nds_card Y (n -c k).
Proof.
move => nN kln Yp.
have kN := NS_lt_nat kln nN.
have nkN := NS_diff k nN.
move: (cdiff_pr (proj1 kln)) => dv.
have Xpb:= OS1. 
set X :=  (nds_merge k Y).
have xsi i: i <c k -> X i = nds_base i by rewrite /X /nds_merge=> h; Ytac0.
have gxi i: i <c n -c k -> X (k +c i) = nds_shift (Y i).
  move => /proj31_1 ic.
  rewrite /X /nds_merge (Y_false (cleNgt (csum_M0le i (CS_nat kN)))). 
  by rewrite csumC (cdiff_pr1' ic kN). 
move: (nds_merge_prop2 kN nkN Yp) => [Xpc Xpd]; rewrite dv in Xpd.
rewrite - (nds_tn_ex_val kN).
have <-: nds_tn_C (nds_merge k Y) k = nds_tn_C nds_base k.
  by apply: (nds_tn_C_exten kN) => i /xsi.
set E := (nds_sums  (fun z => X (k +c z)) (n -c k)) .
have aux: forall i, inc i (nds_tn_S X k) -> nds_binomp i.
  move => i  /setUf_P [K /setP_P K1 /funI_P [s sp] ->].
  have sKN:= (sub_trans K1 (NS_inc_nat kN)).
  have fsk:= (sub_finite_set K1 (finite_set_nat kN)).
  have cKN: natp (cardinal K) by apply /NatP.
  have : forall i, i <c (cardinal K) -> nds_binomp (X (nth_elt K (Vf s i))).
    move => j jk.
    have r0: (Vf s j) <c cardinal K.
      move /permutationsP: sp => [[[fs _] _] ss ts].
      by apply/(NltP cKN); Wtac; rewrite ss; apply/(NltP cKN).
    have r1:(nth_elt K (Vf s j)) <c k.
      apply /(NltP kN); apply:K1; apply: nth_elt_inK => //.
      apply: (NS_lt_nat r0 cKN).
   rewrite (xsi _ r1); exact: (nds_binomp_base (NS_lt_nat r1 kN)).
  rewrite /nds_sc_Ktau/nds_sc.
  move: (cardinal K) cKN; apply: Nat_induction. 
    by move => _; rewrite osum_f0; apply: (oopow_pos OS2).
  move => m mN Hrec /(true_below_rec mN) [a1 a2].
  rewrite /nds_sc (osum_fS _ mN); apply: (nds_binomp_add a2 (Hrec a1)).
have aux2: forall i j u v, inc i (nds_tn_S X k) -> inc j (nds_tn_S X k) ->
   inc u E -> inc v E ->   u +o i = v +o j -> (u = v /\ i = j).
  move => i j u v ia ja /funI_P  [s1 s1p v1p] /funI_P [s2 s2p v2p].
  move/permutationsP:s1p => [[[fs1 _] _] sf1 tf1].
  move/permutationsP:s2p => [[[fs2 _] _] sf2 tf2].
  have ha: forall q, q<c n -c k -> (Vf s1 q)  <c n -c k.  
    by move => q qa;apply /(NltP nkN); Wtac; rewrite sf1; apply/(NltP nkN).
  have hb: forall q, q<c n -c k -> (Vf s2 q)  <c n -c k.  
    by move => q qa;apply /(NltP nkN); Wtac; rewrite sf2; apply/(NltP nkN).
  have v1a: u =  nds_sc  (fun z => nds_shift (Y z)) (n -c k) s1.
    by rewrite v1p; apply:(osumf_exten nkN) => q /ha /gxi. 
  have v2a: v =  nds_sc  (fun z => (nds_shift (Y z))) (n -c k) s2.
    by rewrite v2p; apply:(osumf_exten nkN) => q /hb/gxi.
  have ax1: nds_ax (fun z => Y (Vf s1 z)) (n -c k).
    by move => z /ha/Yp /proj32_1.
  have ax2: nds_ax (fun z => Y (Vf s2 z)) (n -c k).
    by move => z /hb/Yp /proj32_1.
  move:(osum_shift  nkN ax1) (osum_shift  nkN ax2) => [qa qb][qc qd].
  rewrite v1a v2a /nds_sc qb qd => eq1;
  move:(nds_add_sb_inj qa qc(aux  i ia) (aux  j ja) eq1).
  move => [-> ->]; split; reflexivity.
pose F a :=(fun_image E (osum2^~ a)).
have H: forall a, inc a (nds_tn_S X k) -> cardinal (F a) = nds_card Y (n -c k).
  move => a ias.
  have xx: nds_ax Y (n -c k) by move => t /Yp /proj32_1.
  rewrite cardinal_fun_image. rewrite  (nds_card_shift nkN xx).
    by apply:(nds_card_exten nkN) => i /gxi.
  move => u v ua va /= eq; exact: (proj1 (aux2 _ _ _ _ ias ias ua va eq)).
have hu: nds_type_nor X n k \1c.
  move:(nds_merge_prop1 kN nkN Yp); rewrite dv => hu.
  split => //; split; first by move => i /hu [qa  qb].
  exists \1c; split => //.
     move => i lin; case:(cleT_el (CS_nat kN) (proj31_1 lin)) => cp.
       exact: (proj1(Xpd i cp lin)).
     by rewrite (Xpc i cp); apply: oleR.
  set Z := Zo _ _.
  suff: Z = k by move ->; apply: card_nat.
  set_extens t.
    move=> /Zo_P [/(NltP nN) ltn dt1].
      case:(cleT_el (CS_nat kN) (proj31_1 ltn)) => cp; last by apply/(NltP kN).
      by move:(proj2(Xpd t cp ltn)); rewrite dt1.
    move/(NltP kN) => ltk; apply: Zo_i (Xpc _ ltk).
    by move/(NltP nN): (clt_ltT ltk kln).
rewrite /nds_card  (nds_tg9 nN kln hu) csum_pr4_bis.
  rewrite cprodC /nds_tn_C cprod2cr - csum_of_same /csumb.
  by apply: f_equal; apply: Lg_exten => i ib; apply: H.
move => i j ia ja; case (equal_or_not i j) => eij; [by left | right].
  apply:disjoint_pr => u /funI_P [v1 va vb] /funI_P [v2 vc vd].
  rewrite vb in vd; case eij; exact: (proj2 (aux2 _ _ _ _ ia ja va vc vd)).
Qed.

Definition nds_induction a b (T: fterm2) :=
  transfinite_defined Nat_order
     (fun u => Yo (source u = \0c) a (Yo (source u = \1c) b  
     (T (nds_k_of (source u)) (Vf u ((source u) -c (nds_k_of (source u))))))).

Lemma nds_induction_prop a b T (f := nds_induction a b T) :
  [/\ Vf f \0c = a, Vf f \1c = b &
      forall n, natp n -> \1c <c n -> 
         Vf f n = T (nds_k_of n) (Vf f (n -c (nds_k_of n)))].
Proof.
rewrite /f/nds_induction.
set p :=  (fun u : Set => _).
have [wo sr] := Nat_order_wor.
move: (transfinite_defined_pr p wo) => [].
set g := (transfinite_defined Nat_order p) => pa pb pc.
have p1: forall a, natp a -> 
   source (restriction1 f (segment Nat_order a))= a.
  by move=> c cN; rewrite /restriction1 corresp_s segment_Nat_order1. 
rewrite sr in pb pc; split.
- by rewrite (pc _ NS0) /p (p1 _ NS0); Ytac0.
- rewrite (pc _ NS1) /p (p1 _ NS1); Ytac0; rewrite (Y_false); fprops.
- move => n nN ln2; rewrite (pc _ nN) /p (p1 _ nN).
  move: (nesym (proj2 ln2)) => nn1.
  have nn0: n <> \0c by move => bad; move: ln2; rewrite bad => /clt0.
  move:(nds_k_of_bd nN ln2) => [qa qb].
  have qc: inc (n -c nds_k_of n) n.
    apply/(NltP nN); apply: (cdiff_ltb nN (proj1 qb) (nesym (proj2 qa))).
  have sng: sub n (source g) by rewrite pb; exact :(NS_inc_nat nN).
  Ytac0; Ytac0; rewrite (segment_Nat_order1 nN).
  by rewrite (restriction1_V (proj1 pa) sng qc).
Qed.

Definition nds_example_set :=  
  (nds_induction (Lg Nat (fun i => \1o))
                (Lg Nat (fun i => \1o))
                (fun k t => (Lg Nat (nds_merge k (Vg t))))).

Definition nds_example n := fun i => (Vg (Vf nds_example_set n) i).

Lemma nds_induction_prop2 (f := nds_example) :
  [/\ forall i, natp i -> f \0c i = \1o,
     forall i, natp i -> f \1c i = \1o &
      forall n, natp n -> \1c <c n -> let k := nds_k_of n in
      same_below (f n) (nds_merge k (f (n -c k)))  n].
Proof.
rewrite /f/nds_example /nds_example_set.
set cstf := Lg Nat (fun _ : Set => \1o).
set T := (fun k t : Set => Lg Nat (nds_merge k (Vg t))).
move: (nds_induction_prop cstf cstf T).
set g := nds_induction cstf cstf T.
move => [p1 p2 p3]; rewrite p1 p2; split.
    by rewrite /cstf => i iN; rewrite LgV.
  by rewrite /cstf => i iN; rewrite LgV.
move => n nN ln2 i lin; move: (NS_lt_nat  lin nN) => iN.
by rewrite (p3 _ nN ln2) /T !LgV.
Qed.

Lemma nds_example_small_ax n: 
  natp n -> nds_small_ax (nds_example n) n.
Proof.
move: nds_induction_prop2 => [qa qb qc]. 
move => nN; move: {1 3 4}(n) (cleR (CS_nat nN)).
move: n nN; apply:Nat_induction.
  by move => m /cle0 -> i /clt0.
move => m mN Hrec q /cle_eqVlt; case => qv; last first.
  by move /(cltSleP mN):qv => /Hrec.
rewrite qv; case: (czero_dichot (CS_nat mN)) => mz.
  rewrite mz succ_zero => i iN; rewrite (qb _ (NS_lt_nat iN NS1)).
  split; first by apply: olt_01.
  by rewrite - oopow0; apply: opow_Mo_lt; apply: olt_0omega.
have sp: \1c <c csucc m by rewrite - succ_zero; exact: (cltSS mz).
move: (NS_succ mN) => sN i lin.
move: (NS_lt_nat lin sN) => iN.
move: (nds_k_of_bd sN sp).
rewrite (qc _ sN sp i lin); set k := nds_k_of  _; move => [kp lkm].
move: (NS_lt_nat lkm sN) => kN.
rewrite/nds_merge.
case: (NleT_el kN iN) => cik; last by Ytac0; apply:nds_small_base.
have ha: (csucc m -c k) <=c m.
   apply/(cltSleP mN);apply: (cdiff_ltb sN (proj1 lkm) (nesym (proj2 kp))).
have hb:=(cdiff_pr7  cik  lin sN).
rewrite (Y_false (cleNgt cik)); exact:(nds_small_nz_shift (Hrec _ ha _ hb)).
Qed.

Lemma nds_card_sol (X:= nds_example) n: natp n -> \1c <=c n ->
  nds_ax (X n) n /\ nds_sol n = nds_card (X n) n.
Proof.
move => nN np.
split.
   by move => i lin;  move: (nds_example_small_ax  nN  lin) => [/proj32_1].
symmetry; clear np; move: n nN; apply:  nds_k_of_prop.
- by rewrite(@nds_card_0 (X \0c)).
- by rewrite(@nds_card_1 (X \1c)).
- move => n nN ng1.
  move: (proj33 nds_induction_prop2 _ nN ng1); simpl.
  move: (nds_k_of_bd nN ng1).
  set k := (nds_k_of n); move => [lk0 kln] hr.
  move: (NS_diff k nN) => dkN.
  have w: opos_below (X (n -c k)) (n -c k).
     by move => i  /(nds_example_small_ax dkN) /proj1.
  rewrite - (nds_card_merge nN kln w).
  by apply: (nds_card_exten nN).
Qed.

Theorem nds_alt_som n: natp n ->  nds_F n = nds_sol n.
Proof.
have F0: nds_F \0c = \1c. 
  by move: (proj43 (nds_f_def NS0)) => [X _ <-]; rewrite (nds_card_0 X).
have F1: nds_F \1c = \1c. 
  by move: (proj43 (nds_f_def NS1)) => [X _ <-]; rewrite (nds_card_1 X).
move:n; apply: nds_alt => //.
  apply: nds_alt_prop1.
move => n nN.  
have sp:  (\1c <=c csucc n) by rewrite - succ_zero; apply/cleSS; apply: cle0n.
move: (nds_card_sol (NS_succ nN) sp) => [xa xn].
by move: (proj44 (nds_f_def (NS_succ nN)) _ xa); rewrite xn.
Qed.


  
End SmallOrdinals.

