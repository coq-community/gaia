(** * Theory of Sets : two type of ordinals
  Copyright INRIA (2013-2013) Marelle Team (Jose Grimm).
*)
(* $Id: ssete10.v,v 1.3 2018/09/04 07:58:00 grimm Exp $ *)

From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Export sset14 ssete9.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Ordinals9.

Fixpoint T1toB (x: T1) : Set :=
  if x is cons a n b then 
     omega0 ^o (T1toB a) *o (nat_to_B n.+1) +o  (T1toB b)
  else \0o.

Lemma OS_succN n : ordinalp (nat_to_B n.+1).
Proof.  exact: (OS_nat (nat_to_B_Nat n.+1)). Qed.

Lemma OS_T1toB x : ordinalp (T1toB x).
Proof.
elim:x; first by apply:OS0.
move => a oa n b; apply:OS_sum2. 
apply:(OS_prod2 (OS_pow OS_omega oa) (@OS_succN n)).
Qed.

Lemma T1toB_small x : T1toB x <o epsilon0.
Proof.
move: (ord_eps_p3 epsilon0p) => H.
elim:x.
   exact: (olt_ltT olt_0omega H).
move => a ha n b hb.
apply: (sum_lt_eps0 (prod_lt_eps0 (pow_lt_eps0 ha) (nat_to_B_Nat n.+1)) hb).
Qed.


Lemma T1toB_surjective x: x <o epsilon0 -> exists y, x = T1toB y.
Proof.
move => xo; move:(proj31_1 xo) => ox; move: xo.
case:(least_ordinal6 (fun z => z <o epsilon0 -> exists y, z = T1toB y) ox) =>//.
set z := least_ordinal _ _.
move => [oz Hz []] zo.
case: (ozero_dichot oz); first by move => ->; exists zero.
move => h; move: (CNF_simple_bdn2 h zo).
move:(the_CNF_simplP h).
set a := (P (the_CNF_simpl z)).
set b:= (P (Q (the_CNF_simpl z))).
set c:=(Q (Q (the_CNF_simpl z))).
move => ax [ha hb].
have ae:= olt_ltT ha zo.
have ce:=olt_ltT hb zo.  
move/(oltP oz): ha => az.
move/(oltP oz): hb => cz.
move: (Hz _ az ae) => [a' a'v].
move: (Hz _ cz ce) => [c' c'v].
move: ax => [qa qb qc qd qe].
move: (nat_to_B_surjective qc) => [n' n'v].
by exists (cons a' n' c'); simpl; rewrite - n'v - a'v - c'v.
Qed.

Lemma T1toB_mon1 x y: T1nf x -> T1nf y ->
   x < y -> T1toB x <o T1toB y.
Proof.
have qa: forall n u v, ordinalp n -> 
   u <o omega0^o n ->v <o  omega0^o n -> u +o v <o  omega0^o n.
    move => n u v on ux vx; apply: (indecomp_prop2 ux vx  (indecomp_prop4 on)).
have qb: forall n u m,  ordinalp n ->  
  u <o  omega0^o n -> natp m -> u *o m <o  omega0^o n.
  move => n u m on ux nN; move:(proj31_1 ux) => ou.
  move: m nN; apply:Nat_induction.
    rewrite oprod0r; exact:(ole_ltT (ole0x ou) ux).
  move => m mN Hrec. 
  rewrite (succ_of_nat mN) (oprod2_succ ou (OS_nat mN)).
  apply: (qa _ _ _ on Hrec ux).
move => nx ny; move:  (T1lenn y) ny (ny) nx.
move: {2 3} (y) => z zy nz; move: z nz x y zy.
apply:T1transfinite_induction.
case; first by move => _ _ x y; rewrite T1len0 => /eqP ->; rewrite T1ltn0.
move => za m zb nz Hrec.
case.
  case => // a n b _ _ _ _ /=.
  move:(@OS_T1toB a)(@OS_T1toB b) => oa ob.
  move: (OS_pow OS_omega oa) => op.
  move: (@succ_nz (nat_to_B n)) => snz.
  move:(NS_succ (nat_to_B_Nat n)) => n1.
  move:(OS_prod2 op (OS_nat n1)) => o2.
  apply: (ord_ne0_pos (OS_sum2 o2 ob)) => h.
  move: (proj1 (osum2_zero o2 ob h)).
  by move: (oprod2_nz op (OS_nat n1) (oopow_nz oa) snz).
move => a' n' b'; case => // a n b ha /=.
move => /and3P [na nb etc] /and3P [na' nb' etc'].
have ob := (@OS_T1toB b).
have oa:=(@OS_T1toB a).
have ox:= OS_pow OS_omega oa.
set x := omega0 ^o T1toB a.
have hb:=(T1lt_le_trans (head_lt_cons a n b) ha).
have l1: x <=o x *o csucc(nat_to_B n) +o T1toB b.
  have nN:=nat_to_B_Nat n.
  have on := (OS_nat nN).
  rewrite (Nsucc_rw nN)  csumC - (osum2_2int NS1 nN) (oprodD OS1 on ox).
  rewrite -/x (oprod1r ox) - (osumA ox (OS_prod2 ox on) ob).
  apply: (osum_Mle0 ox (OS_sum2  (OS_prod2 ox on) ob)).
have rb: phi0 za <= cons za m zb. 
  rewrite T1le_consE eqxx T1le0n T1ltnn; case m => //.
have : a' <= a -> T1toB b' <o (omega0 ^o T1toB a').
  move:nb' etc' ha.
  case: b'; first by move => _ _ _ _;apply:oopow_pos; apply:OS_T1toB.
  move => a'' n'' b'' nb''; rewrite phi0_lt1 /= => ha hc aa'.
  move: nb'' => /= /and3P [na'' nb'' etc''].
  move: (T1le_lt_trans aa' hb) => ra.
  move: (Hrec a' na' ra a'' a' (T1lenn a') na' na'' ha) => l2.
  have nx:natp (csucc (nat_to_B n'')) by apply:NS_succ; apply:nat_to_B_Nat.
  have rc: phi0 a'' < cons za m zb.
    move:(T1lt_le_trans ha (T1le_trans aa' (T1le_cons_le hc))). 
    rewrite -phi0_lt => rc; exact: (T1lt_le_trans rc rb).
  have l3: T1toB b'' <o omega0 ^o T1toB a''.
     move:na''; rewrite -nf_phi0 => nsa''.
     have op:= (OS_pow OS_omega (proj31_1 l2)).
     move: (Hrec _ nsa'' rc _ _  (T1lenn (phi0 a'')) nsa'' nb'' etc'').
     by rewrite /phi0 /= succ_zero (oprod1r op) (osum0r op).
  have l4:= (opow_Mo_lt l2).
  move: (olt_ltT l3 l4) => l5.
  apply: (qa _ _ _ (@OS_T1toB a') (qb _ _ _ (@OS_T1toB a') l4 nx) l5).
case: (T1ltgtP a' a) => //.
  move => aa' HR _; apply:olt_leT l1.
  move: (Hrec a na hb a' a (T1lenn a) na na' aa') => /opow_Mo_lt l2.
  have ns: natp (csucc (nat_to_B n')) by apply:NS_succ; apply:nat_to_B_Nat.
  move: (HR (T1ltW aa')) => hr1.
  apply: qa; [exact oa | by apply: qb  |  exact: (olt_ltT hr1 l2)].
move => -> HR; case:(ltngtP n' n) => //.
  move => nn _; rewrite -/x - (subnKC nn) (nat_to_B_sum).
  have hc: natp (csucc (nat_to_B n')) by  apply:NS_succ; apply:nat_to_B_Nat.
  have hd:= (NS_succ hc).
  have he: natp (nat_to_B (n - n'.+1)) by apply:nat_to_B_Nat.
  have o1 := (OS_nat hd).
  have o2 := (OS_nat he).
  have o3:= (OS_nat hc).
  set u := x *o csucc (csucc (nat_to_B n')). 
  set v := (x *o nat_to_B (n - n'.+1) +o T1toB b).
  have ou := (OS_prod2 ox o1).
  have ov1:= (OS_prod2 ox o2).
  have hf:= (osum_Mle0 ou (OS_sum2 ov1 ob)).
  rewrite - nat_to_B_succ - (csum_Sn _ hc) - (osum2_2int hd he).
  rewrite (oprodD o1 o2 ox)- (osumA ou (OS_prod2 ox o2) ob).
  apply: (olt_leT _ hf).
  move:(osum_Meqlt (HR (T1lenn a)) (OS_prod2 ox o3)). 
  by rewrite -(oprod2_succ ox o3) - (succ_of_nat hc).
move => -> lbb.
move:(T1le_cons_le ha); rewrite - phi0_le => h; move:(T1le_trans h rb) => rc.
move:(Hrec b nb (T1lt_le_trans etc rc) b' b (T1lenn b) nb nb' lbb) => h2.
apply:(osum_Meqlt h2); apply:(OS_prod2 ox (@OS_succN n)).
Qed.

Lemma T1toB_mon2 x y: T1nf x -> T1nf y ->
   (x < y <-> T1toB x <o T1toB y).
Proof.
move => ha hb.
case:T1ltgtP => h. 
  by split =>//; move:(T1toB_mon1 hb ha h) => [hc _] /(oleNgt hc).
  split =>// _; exact:(T1toB_mon1 ha hb h). 
by rewrite h; split => // [] [_]. 
Qed.

Lemma T1toB_injective x y: T1nf x -> T1nf y ->
 T1toB x = T1toB y -> x = y.
Proof.
move => ha hb.
case /or3P: (T1lt_trichotomy x y). 
+ by move/(T1toB_mon1 ha hb) => [].
+ by move /eqP.
+ by move/(T1toB_mon1 hb ha) => [_ /nesym].
Qed.

Export Gamma0.


Fixpoint T2toB (x: T2) : Set :=
  if x is cons a b n c then 
    Spsi (T2toB a) (T2toB b)  *o (nat_to_B n.+1) +o  (T2toB c)
  else \0o.


Lemma T2toB_small x : T2toB x <o Gamma_0.
Proof.
elim:x.
  rewrite /= - Gamma0_epsilon; apply:(oopow_pos OS_Gamma_0).
by move => a ha b hb n c hc; apply:T2_to_bourbaki_small. 
Qed.

Lemma OS_T2toB x : ordinalp (T2toB x).
Proof.  exact: (proj31_1 (T2toB_small x)). Qed.


Lemma T2le_cons_le a b n c a' b' n' c':
   (cons a b n c <= cons a' b' n' c') -> [a,b] <= [a',b'].
Proof.
rewrite T2le_consE - T2lt_psi.
case h: ([a, b] < [a', b']); first by  move => _; exact :(T2ltW h).
case h1: ((a == a') && (b == b')) => // _.
by move/andP:h1 => [/eqP -> /eqP ->]; apply: T2lenn.
Qed.

Lemma T2toB_mon1 x y: T2nf x -> T2nf y ->
   x < y -> T2toB x <o T2toB y.
Proof.
have HS:forall a b, Spsi (T2toB a) (T2toB b) = T2toB [a, b]. 
  move => a b.
  have ox :=(OS_Spsi (@OS_T2toB a) (@OS_T2toB b)).
  by rewrite /= succ_zero (oprod1r ox) (osum0r ox).
set n := (size x + size y).+1.
move: (leqnn n); rewrite {1}/n; move: n.
move => n; elim: n x y; first by move  => a b//;rewrite ltn0.
move => m Hrec [].
  move=> y _ _ _; case:y => // a b n c _ /=.
  move: (@Cardinal.succ_nz (nat_to_B n)) => snz.
  move:(NS_succ (nat_to_B_Nat n)) => n1.
  move:(@OS_T2toB a)(@OS_T2toB b) (@OS_T2toB c) => oa ob oc.
  move: (OS_Spsi oa ob) => ozx.
  move:(OS_prod2 ozx (OS_nat n1)) => o2.
  apply: (ord_ne0_pos (OS_sum2 o2 oc)) => h.
  move: (proj1 (osum2_zero o2 oc h)).
  by move: (oprod2_nz ozx (OS_nat n1) (Spsi_nz oa ob) snz).
move => a b n c; case => // a' b' n' c' sz /=.
move: sz; rewrite ltnS => la.
move => /and4P[na nb nc etc] /and4P[na' nb' nc' etc']. 
move:(@OS_T2toB a) (@OS_T2toB b) (@OS_T2toB c) => oa ob oc.
move:(@OS_T2toB a') (@OS_T2toB b') (@OS_T2toB c') => oa' ob' oc'.
set x := Spsi (T2toB a) (T2toB b).
set x' := Spsi (T2toB a') (T2toB b').
have ox':=(OS_Spsi oa' ob').
have nN':=nat_to_B_Nat n'.
have oxsn: ordinalp (x' *o csucc (nat_to_B n')).
  by apply:(OS_prod2 ox'); apply:OS_nat; apply:NS_succ.
have l1: x' <=o x' *o csucc(nat_to_B n') +o T2toB c'.
  have on := (OS_nat nN').
  rewrite (Nsucc_rw nN')  csumC - (osum2_2int NS1 nN') (oprodD OS1 on ox').
  rewrite -/x' (oprod1r ox') - (osumA ox' (OS_prod2 ox' on) oc').
  apply: (osum_Mle0 ox' (OS_sum2 (OS_prod2 ox' on) oc')).
move => leb.
have lew1:= (T2le_cons_le (T2ltW leb)).
move: (size_prop1 a b n c) => [pa pb pc pd].
move: (size_prop1 a' b' n' c') => [pa' pb' pc' pd'].
have nab': T2nf [a', b'] by rewrite nf_psi na' nb'.
have nab: T2nf [a, b] by rewrite nf_psi na nb.
have HR: T2toB c <o x'.
  move: (T2lt_le_trans etc lew1);rewrite /x' HS; apply: Hrec => //. 
  apply:leq_trans la; rewrite ltn_add_le //.
move: leb;rewrite T2lt_consE /x'/x. 
case h1: (lt_psi a b a' b'); last first.
  case h2: ((a == a') && (b == b')) => //.
  rewrite /x;move/andP: h2 => [/eqP -> /eqP ->];rewrite -/x'.
  case:(ltngtP n n') => //; last first.
    move => -> cc; apply:(osum_Meqlt _ oxsn).
    move:cc; apply: Hrec=> //; apply:leq_trans la; rewrite ltn_add_le //.
    exact:(ltnW pc').
  move => nn _; rewrite  - (subnKC nn) (nat_to_B_sum).
  have hc: natp (csucc (nat_to_B n)) by  apply:NS_succ; apply:nat_to_B_Nat.
  have hd:= (NS_succ hc).
  have he: natp (nat_to_B (n' - n.+1)) by apply:nat_to_B_Nat.
  have o1 := (OS_nat hd).
  have o2 := (OS_nat he).
  have o3:= (OS_nat hc). 
  rewrite - (csum_Sn _ hc) - (osum2_2int hd he) (oprodD o1 o2 ox').
  rewrite - (osumA (OS_prod2 ox' o1) (OS_prod2 ox' o2) oc').
  rewrite -/x';set u := x' *o csucc (csucc (nat_to_B n)). 
  have ou: ordinalp u by apply: OS_prod2 => //.
  have res1: x' *o csucc (nat_to_B n) +o T2toB c <o u.
    rewrite /u (succ_of_nat hc) (oprod2_succ ox' o3).
    by apply:(osum_Meqlt HR); apply: OS_prod2.
  apply:(olt_leT res1); apply:osum_Mle0 => //.
  by apply: OS_sum2 => //; apply:OS_prod2.
move => _; apply:(olt_leT _ l1).
suff: x <o x'. 
   move => w3; apply: Spsi_indecomp_rec => //.
have HR1: a' < a -> T2toB a' <o T2toB a.
    apply: Hrec => //; apply:leq_trans la. 
    rewrite addnC ltn_add_le //; exact:(ltnW pa').
move:h1; case/orP; last first.
  move /andP => [/HR1 ha /eqP hb].
  apply:(Spsi_cpc ob ha);rewrite HS hb; fprops.
case /orP; last first.  
  move => /andP [/HR1 ha hb].
  have [Rb _]: T2toB [a,b] <o T2toB b'. 
    apply: Hrec => //; apply:leq_trans la; rewrite ltn_add_el //.
  by apply:(Spsi_cpc ob ha); rewrite HS.
case /orP; last first.
  rewrite /x/x';move /andP => [/eqP -> qb];apply:Spsi_cpb => //.
  apply:Hrec => //;apply:leq_trans la; rewrite ltn_add_le //; exact:(ltnW pb').
move => /andP [ha hb].
have hc:T2toB a <o T2toB a'. 
  apply: Hrec => //; apply:leq_trans la;rewrite ltn_add_le //;exact:(ltnW pa').
apply: Spsi_cpa => //; rewrite HS; apply: Hrec => //.
apply:leq_trans la; rewrite ltn_add_le //.
Qed.



Lemma T2toB_mon2 x y: T2nf x -> T2nf y ->
   (x < y <-> T2toB x <o T2toB y).
Proof.
move => ha hb.
case:T2ltgtP => h. 
  by split =>//; move:(T2toB_mon1 hb ha h) => [hc _] => /(oleNgt hc).
  split =>// _; exact:(T2toB_mon1 ha hb h). 
by rewrite h; split => // [] [_]. 
Qed.

Lemma T2toB_injective x y: T2nf x -> T2nf y ->
 T2toB x = T2toB y -> x = y.
Proof.
move => ha hb.
case /or3P: (T2lt_trichotomy x y). 
+ by move/(T2toB_mon1 ha hb) => [].
+ by move /eqP.
+ by move/(T2toB_mon1 hb ha) => [_ /nesym].
Qed.


Lemma T2toB_surjective x: x <o Gamma_0 -> exists2 y, T2nf y & x = T2toB y.
Proof.
move => xo; move:(proj31_1 xo) => ox; move: xo.
case:(least_ordinal6 (fun z => z <o Gamma_0 -> exists2 y, T2nf y  &z = T2toB y) ox) =>//.
set z := least_ordinal _ _.
move => [oz Hz []] zo.
case: (ozero_dichot oz); first by move => ->; exists zero.
move => zp.
move: (the_CNF_simplP zp) (CNF_simple_bdn3 zp zo). 
set aa := (P (the_CNF_simpl z)); set n := (P (Q (the_CNF_simpl z)));
set c := (Q (Q (the_CNF_simpl z))); set w := inv_psi_omega _.
move => h1  [ra rb rc rd].
move:(CNF_simple_p2 h1) =>[_ cz _].
move: h1 => [qa qb qc qd qe].
move: (nat_to_B_surjective qc) => [n' n'v].
have h: forall t, t <o z -> exists2 y : T2, T2nf y & t = T2toB y.
   move => t ta; apply: Hz; [by apply/(oltP oz) |  exact: (olt_ltT ta zo) ].
move: (h _ rb) => [A an ap].
move: (h _ rc) => [B bn bp].
move: (h _ cz) => [C cn cp].
exists (cons A B n' C); last by rewrite /= - ap -bp - cp - n'v rd qd.
have ha: T2nf [A, B] by rewrite nf_psi an bn.
have hb:= (OS_pow OS_omega qa).
rewrite /= an bn cn /=; apply /(T2toB_mon2 cn ha).
move: qe; rewrite {2} /T2toB -/T2toB - ap - bp - cp rd /nat_to_B succ_zero.
by rewrite oprod1r // osum0r.
Qed.





(** first try *)

(* demo 

Lemma Ex1: forall a:T1, inc (Ro a) T1.
Proof. by move => a; apply:R_inc. Qed.

Lemma Ex2: forall a b:T1, Ro a = Ro b -> a = b.
Proof. by move => a b ; apply:R_inj. Qed.

Lemma Ex3: forall (b:Set)(Ha:inc b T1), Ro (Bo Ha) = b.
Proof. by move => b; apply:B_eq. Qed.

Lemma Ex4: forall (a:T1)(Ha:inc (Ro a) T1), (Bo Ha) = a.
Proof. by move => a; apply:B_back. Qed.

*)


Definition  set_to_T1 x := match  (ixm (inc x T1) )  with
 | inl hx => Bo hx 
 | inr _ => CantorOrdinal.zero end.

Lemma set_to_T1_pr x (Hx: inc x T1) : set_to_T1 x = Bo Hx.
Proof.
rewrite /set_to_T1;case: (ixm (inc x T1)) => // Hy; apply: R_inj.
by rewrite (B_eq Hx) (B_eq Hy).
Qed.

Lemma set_to_T1_inj x y: inc x T1 -> inc y T1 -> 
   set_to_T1 x = set_to_T1 y -> x = y.
Proof.
move => ha hb.
by rewrite !set_to_T1_pr - {2} (B_eq ha) - {2} (B_eq hb) => ->.
Qed.

Definition ST1_le x y := 
  [/\ inc x T1, inc y T1 & set_to_T1 x <=  set_to_T1 y] %ca.

Definition ST1_order := graph_on ST1_le T1.

Lemma ST1_osr: order_on ST1_order T1.
Proof.
have rr: forall a, inc a T1 -> (ST1_le a a) by move => h; split => //.
move: (graph_on_sr rr); rewrite -/ ST1_order => st; split => //.
apply:order_from_rel; split.
+ move => y x t [xE yE ha] [_ zE /(T1le_trans ha) hb]; split => //.
+ move => x y [xE yE ha][_ _ hb].
  by apply:set_to_T1_inj=> //; apply/eqP; rewrite T1eq_le ha hb.
+ by move =>  u v [uE vE _]; split; fprops.
Qed.

Lemma ST1_leP x y: gle ST1_order x y <->   ST1_le x y.
Proof.
split; first by  move/graph_on_P1 => [].
by move => h; move:(h) =>[ha hb _]; apply/graph_on_P1. 
Qed.

Definition T1N := Zo T1 (fun z => T1nf (set_to_T1 z)).

Definition STN_order:= induced_order  ST1_order T1N.

Lemma STN_osr: order_on STN_order T1N.
Proof.
move: ST1_osr => [ha hb].
apply:iorder_osr => //; rewrite hb; apply:Zo_S.
Qed.

Lemma STN_tor: total_order STN_order.
Proof.
move: STN_osr => [ha hb]; split => //; rewrite hb => x y xE yE.
have s1: sub T1N T1 by apply: Zo_S.
move:(s1 _ xE)(s1 _ yE) => x1 y1.
case /orP: (T1le_total(set_to_T1 x)(set_to_T1 y)) => h.
+ left; apply/iorder_gle0P => //; apply/ ST1_leP; split => //.
+ right; apply/iorder_gle0P => //; apply/ ST1_leP; split => //.
Qed.


Lemma STN_wosr: worder_on STN_order T1N.
Proof.
move: STN_osr => [ha hb]; split => //.
case: (total_order_worder_dichot STN_tor) => // [] [f [fgf df rf fd]].
case:(not_decreasing nf_Wf).
rewrite hb in rf.
have hc: forall n, natp n -> inc (Vg f n) T1N.
   move => n nN; apply:rf; apply/(range_gP fgf); exists n => //; ue.
pose g n := (set_to_T1 (Vg f (nat_to_B n))).
exists g; move => i; rewrite /restrict.
have sT: sub T1N T1 by apply:Zo_S.
move:  (nat_to_B_Nat i)  (nat_to_B_Nat i.+1) => aN bN.
have lt1: (nat_to_B i) <c (nat_to_B i.+1). 
  by rewrite - nat_to_B_succ; apply:cltS.
move:(hc _ aN) (hc _ bN) => hu hv.
move:(hu)(hv)=> /Zo_P [aT1 Na] /Zo_P [bT1 Nb]; split => //.
move:(fd _ _ aN bN lt1) => [].
move/(iorder_gle0P _ hv hu) /ST1_leP => [_ _ sa] sb.
rewrite T1lt_neAle /g sa andbT; apply/eqP => h; case sb.
by apply:set_to_T1_inj.
Qed.


Definition STN_iso:= (the_ordinal_iso STN_order).
Definition ord_T1:= (ordinal STN_order).

Lemma  STN_iso_pr:  order_isomorphism STN_iso (ordinal_o ord_T1) STN_order.
Proof. exact: (the_ordinal_iso1 (proj1 STN_wosr)).  Qed.


Parameter T1graph_aux: Set.
Axiom T1graph_o1 :
   (forall a b (Ha: inc a T1) (Hb: inc b T1), inc (J a b)  T1graph_aux <->
      (Bo Ha) <= (Bo  Hb))%ca.

Definition T1graph := T1graph_aux \cap (coarse T1).

Lemma T1graph_p1 a b: (a <= b)%ca -> inc (J (Ro a) (Ro b)) T1graph.
Proof.
move => lab.
apply/setI2_P; split.
  by apply/(T1graph_o1 (R_inc a) (R_inc b)); rewrite !B_back.
by apply: setXp_i; apply: R_inc.
Qed.

Lemma T1graph_p2 x: inc x T1graph -> [/\ pairp x, inc (P x) T1 & inc (Q x) T1].
Proof. by move /setI2_P => [_ /setX_P]. Qed.

Lemma T1graph_p3 x (H:inc x T1graph) 
     (Ha:= proj32 (T1graph_p2 H)) (Hb:= proj33 (T1graph_p2 H)):
     ((Bo Ha) <= (Bo Hb))%ca.
Proof.
apply/(T1graph_o1 Ha Hb); rewrite ( proj31 (T1graph_p2 H)).
by move /setI2_P : (H) => [].
Qed.

Lemma T1graph_o: order_on  T1graph T1.
Proof.
have ha: sgraph T1graph.
  by move => t /setI2_P [_ /setX_P []].
have rr: forall t, inc t T1 -> related T1graph t t.
  by move => t h;  move:(T1graph_p1(T1lenn (Bo h)));  rewrite B_eq. 
have hb: substrate T1graph = T1.
   set_extens t.
     by case/(substrate_P ha) => [] [y /T1graph_p2 []]; aw.
   move => /rr; apply:arg1_sr.
have hc: reflexivep T1graph by move => t; rewrite hb; apply: rr.
have hd: antisymmetricp T1graph.
  move => u v hu hv; move:(T1graph_p3 hu) (T1graph_p3 hv) => /=.
  set a := Bo _; set b := Bo _. 
  set a' := Bo _; set b' := Bo _.
  have ea: u = Ro a by rewrite (B_eq (proj32 (T1graph_p2 hu))); aw.
  have eb: v = Ro b by rewrite (B_eq (proj33 (T1graph_p2 hu))); aw.
  have : v = Ro a' by rewrite (B_eq (proj32 (T1graph_p2 hv))); aw.
  have : u = Ro b' by rewrite (B_eq (proj33 (T1graph_p2 hv))); aw.
  rewrite ea eb => ec ed; rewrite - (R_inj ec)  - (R_inj ed) => l1 l2.
  have -> // : a = b by apply/eqP; rewrite T1eq_le l1 l2.
have he:transitivep T1graph.
  move => v u w hu hv.
  move:(T1graph_p3 hu) (T1graph_p3 hv) => /=.
  set a := Bo _; set b := Bo _; set c := Bo _; set d := Bo _.
  have ea: u = Ro a by rewrite (B_eq (proj32 (T1graph_p2 hu))); aw.
  have eb: v = Ro b by rewrite (B_eq (proj33 (T1graph_p2 hu))); aw.
  have: v = Ro c by rewrite (B_eq (proj32 (T1graph_p2 hv))); aw.
  have ed: w = Ro d by rewrite (B_eq (proj33 (T1graph_p2 hv))); aw.
  rewrite eb => ec;  rewrite - (R_inj ec) => ab bd.
  by move:(T1graph_p1 (T1le_trans ab bd)); rewrite - ea - ed.
by split.
Qed.



End  Ordinals9.
