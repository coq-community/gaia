(** * Theory of Sets : Ordinals
  Copyright INRIA (2009-2013 3108) Apics, Marelle Team (Jose Grimm).
*)

(* $Id: sset13a.v,v 1.4 2018/09/04 07:57:59 grimm Exp $ *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From gaia Require Export sset12.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Ordinals3a.

(** **  Cantor normal form *)


(** Any ordinal is uniquely a sum of decreasing powers of omega *)

Definition CNFrv (f:fterm) n := osumf (fun i => oopow (f i)) n.
Definition CNFr_ax (f:fterm) n :=
  ord_below f n 
  /\ (forall i, natp i -> (csucc i) <c n -> (f i) <=o (f (csucc i))).

Lemma CNFr_ax_s f n: natp n -> CNFr_ax f (csucc n) -> CNFr_ax f n.
Proof.
move => nN [ax1 ax2]; move: (cltS nN) => pa;split=> //.
  by move=> i lin; apply: ax1; apply:clt_ltT lin pa.
move => i iN si; apply: ax2 => //;apply:clt_ltT si pa.
Qed.

Lemma OS_CNFr_t f n i: CNFr_ax f n -> i <c n ->  ordinalp (oopow (f i)).
Proof.
move => ax lin.
exact: (OS_oopow ((proj1 ax) _ lin)).
Qed.

Lemma OS_CNFr0 f n: natp n -> CNFr_ax f n -> ordinalp (CNFrv f n).
Proof.
by move => nN ax;apply: (OS_osumf nN) => i /(OS_CNFr_t ax).
Qed.

Lemma CNFr_rec f n: natp n ->
  CNFrv f (csucc n) = oopow (f n) +o CNFrv f n. 
Proof.
by move => nN; rewrite /CNFrv (osum_fS _ nN).
Qed.

Lemma CNFr_p2 f n: natp n -> CNFr_ax f (csucc n) ->
  oopow (f n) <=o CNFrv f (csucc n).
Proof.
move => nN ax; move:(CNFr_ax_s nN ax) => axr.
rewrite (CNFr_rec _ nN).
exact: osum_Mle0 (OS_CNFr_t ax (cltS nN)) (OS_CNFr0 nN axr).
Qed.

Lemma CNFr_p3 f n i: 
  natp n -> CNFr_ax f n -> i <c n -> oopow (f i) <=o CNFrv f n.
Proof.
move => nN ax lin;move: n nN ax i lin.
apply:Nat_induction; first by move => _ u /clt0.
move => n nN Hrec axr i /(cltSleP nN)/(cle_eqVlt);case => lin.
  by rewrite lin; apply:CNFr_p2.
have ax0:=(CNFr_ax_s nN axr).
apply: (oleT (Hrec ax0 i lin)).
rewrite (CNFr_rec _ nN).
exact:(osum_M0le (OS_CNFr_t axr (cltS nN)) (OS_CNFr0 nN ax0)).
Qed.

Lemma CNFr_p4 f n: natp n -> CNFr_ax f (csucc n) ->
  CNFrv f (csucc n) <o oopow (osucc (f n)).
Proof.
have Hi i: ordinalp i -> oopow i <o oopow (osucc i).
  move => oi; apply:(opow_Mo_lt (oltS oi)).
move:n; apply:Nat_induction.
  move=> ax; move: (proj1 ax \0c (cltS NS0)) => of0.
  rewrite succ_zero /CNFrv (osum_f1 (f:= oopow \o f) (OS_oopow  of0)).
  by apply:Hi.
move => n nN Hrec ax.
move:(proj2 ax n nN (cltS (NS_succ nN))) => le1; move: (proj32 le1) => of0.
move/(oleSSP): le1 => /opow_Mo_le le2.
move:(olt_leT (Hrec (CNFr_ax_s (NS_succ nN) ax)) le2)=> ww.
rewrite (CNFr_rec _ (NS_succ nN)).
apply: (indecomp_prop2 (Hi _ of0) ww (indecomp_prop4 (OS_succ of0))).
Qed.

Lemma CNFr_p4' f n m: natp n -> CNFr_ax f (csucc n) ->
  f n <o m -> CNFrv f (csucc n) <o oopow m.
Proof.
move => nN ax /oleSltP lt1; apply: (olt_leT (CNFr_p4 nN ax)). 
by apply:opow_Mo_le. 
Qed.

Lemma CNFr_p5 f: CNFrv f \0c = \0o.
Proof. by rewrite /CNFrv osum_f0.  Qed.

Lemma CNFr_p6 f n: natp n -> CNFr_ax f n ->  n  <> \0c -> 
    CNFrv f n <> \0o.
Proof. 
move => nN ax nz rz.
move: (cpred_pr nN nz) => [sa sb].
rewrite sb in ax rz.
move:(CNFr_p2 sa ax); rewrite rz => /oleNgt; apply.
exact: (oopow_pos (proj1 ax _ (cltS sa))).
Qed.


Lemma CNFr_unique f g n m: CNFr_ax f n -> CNFr_ax g m ->
   natp n -> natp m -> CNFrv f n = CNFrv g m ->
   (n = m /\ same_below f g n).
Proof.
move => p1 p2 p3 p4; move: n p3 m p1 p2 p4; apply: Nat_induction.
  move => m af ag mN sv; split; last by move => i /clt0 h; case h.
  symmetry;ex_middle bad.
  by move: (CNFr_p6 mN ag bad); rewrite - sv CNFr_p5; case.
move => n nN Hrec m af ag mN sv.
case: (equal_or_not m \0c) => mz.
  by move: (CNFr_p6 (NS_succ nN) af (@succ_nz n)); rewrite sv mz CNFr_p5; case.
move: (cpred_pr mN mz); set m':= (cpred m); move => [m'N mv].
rewrite mv in ag sv.
move: (CNFr_ax_s nN af) (CNFr_ax_s m'N ag) => ax1 ax2.
move: sv (CNFr_p4' nN af (m:= g m')) (CNFr_p4' m'N ag (m:= f n)).
move:(CNFr_p2 nN af) (CNFr_p2 m'N ag). 
rewrite (CNFr_rec _ nN)  (CNFr_rec _ m'N).
move => le1 le2 eq1 lt1 lt2.
move: (cltS nN) (cltS m'N) => ns1 ns2.
case (oleT_ell (proj1 af _ ns1) (proj1 ag _ ns2)).
+ move => eq2.
  rewrite eq2 in eq1.
  move: (osum2_simpl (OS_CNFr0 nN ax1) (OS_CNFr0 m'N ax2) (proj31 le2) eq1).
  move / (Hrec m' ax1 ax2 m'N)=> [ra rb].
  rewrite mv -ra; split; [ reflexivity | move  => i /(cltSleP nN) li].
  case (equal_or_not i n); first by move => ->; rewrite eq2 ra.
  by move => ni; apply:rb; split.
+ move /lt1; rewrite eq1 => /(oleNgt le2); case.
+ by move /lt2; rewrite - eq1 =>  /(oleNgt le1); case.
Qed.

Lemma CNFr_exists_aux x: \0o <o x ->
   exists n y, [/\ ordinalp n, y <o x , y <o oopow n *o omega0  &
                   x = oopow n +o y].
Proof.
move => xp.
move: (ord_ext_div_exists ole_2omega xp)
   =>[e1 [c1 [rm [oe1 oc1 or [eq1 lt1 lt2 lt3]]]]].
move: (ord_rev_pred  lt3); set c2 := (c1 -o \1o); move => [oc2 eql].
have eql2: c1 =  c2 +o \1o.
  move: (osum_M0le OS1 oc2);rewrite - eql => h; move: (ole_ltT h lt2) => aa.
  have c2N: natp c2 by apply:(olt_i aa).
  by move: eql; rewrite (osum2_2int NS1 c2N) csumC - (osum2_2int c2N NS1). 
set q := (omega0 ^o e1); set rm1 :=  ((q *o c2) +o rm).
have oq:= proj32_1 lt1.
have op2: ordinalp (q *o c2) by fprops.
have orm1: ordinalp rm1 by rewrite /rm1; fprops.
move: OS_omega OS1 => oo o1.
have yv1: x = q +o rm1 by rewrite eq1 eql oprodD // oprod1r // /rm1 osumA.
have pv2: q *o c1 = (q *o c2) +o q by rewrite eql2 oprodD // oprod1r //.
have yv2: x = (q *o c2) +o (q +o rm) by rewrite eq1  pv2 osumA //.
have rmy: rm1 <o x.
  split; first by rewrite yv1; apply: osum_M0le. 
  rewrite /rm1 yv2 => eq3.
  move: (osum_Mle0 oq or);rewrite - (osum2_simpl or (OS_sum2 oq or) op2 eq3).
  by move => /(oleNgt) [].
have lt: rm1 <o omega0 ^o e1 *o omega0.
  apply: olt_leT (oprod_Meqle (proj1 lt2) oq).
  rewrite pv2; exact: (osum_Meqlt lt1 op2). 
by exists e1, rm1.
Qed.

Lemma CNFr_exists x: ordinalp x -> 
   exists f n, [/\ natp n, CNFr_ax f n & x = CNFrv f n].
Proof.
pose p := fun x => exists f n, [/\ natp n, CNFr_ax f n & x = CNFrv f n].
move:x; apply:(least_ordinal2) => y oy p2.
case: (ozero_dichot oy) => yp.
  exists (@id Set), \0c; split; [ exact: NS0 | | by rewrite CNFr_p5 yp].
  split => i; [ move /clt0; case | move => _ /clt0; case].
move: (CNFr_exists_aux yp) => [e1 [z [oe zly lt1 yv]]].
move:(p2 _ zly) => [f [n [nN p4 p5]]].
have snb:= (NS_succ nN).
pose g z:= (Yo (z = n) e1 (f z)).
have yv3: y = CNFrv g (csucc n).
  rewrite /CNFrv (osum_fS _ nN) /g yv; Ytac0; congr (osum2).
  by rewrite p5;apply: (osumf_exten nN) => i [_ lin]; Ytac0.
exists g,(csucc n); split => //.
split.
  move => i; rewrite /g; Ytac ein => //.
  by move/(cltSleP nN) => lin; apply:(proj1 p4).
move => i iN h; rewrite /g.
move/(cltSleP nN): h => sin.
Ytac ein; first by move: (cltS nN); rewrite - {2} ein => /(cleNgt sin).
Ytac sein; last by apply:(proj2 p4). 
move: (cltS iN); rewrite sein => lin.
apply/oltSleP; apply/(opow_Mo_ltP  (proj1 p4 _ lin) (OS_succ oe)). 
apply: (ole_ltT (CNFr_p3 nN p4 lin)).
by rewrite - p5 (oopow_succ  oe).
Qed.



Definition ord_negl a b := a +o b = b.
Notation "x <<o y" := (ord_negl x y) (at level 60).

Lemma ord_negl_lt a b: ordinalp a -> ordinalp b -> 
  a <<o b -> ((a = \0o /\ b = \0o) \/ (a <o b)).
Proof.
rewrite /ord_negl;move=> oa ob abz.
move: (osum_Mle0 oa ob); rewrite abz => /ole_eqVlt; case; last by right.
by move => ab; move: abz; rewrite ab =>  /(osum2_a_ab ob ob) -> ; left.
Qed.

Lemma ord_negl_trans a b c : ordinalp a -> ordinalp b -> ordinalp c ->
  a <<o b -> b <<o c -> a <<o c.
Proof.
by move => oa ob oc; rewrite /ord_negl => ab <-; rewrite osumA // ab.
Qed.

Lemma ord_negl_sum a b c: ordinalp a -> ordinalp b -> ordinalp c ->
  a <<o b -> a <<o (b +o c).
Proof.
by rewrite /ord_negl => oa ob oc h; rewrite  osumA // h.
Qed.

Lemma ord_negl_sum' a b c:
  ordinalp a -> a <<o b -> b <=o c -> a <<o c.
Proof. 
move => oa lab h1; move: (h1) => [ob oc _].
move: (odiff_pr h1) => [od -> ]; apply: (ord_negl_sum oa ob od lab).
Qed.

Lemma ord_negl_sum1 a b c:
  ordinalp a -> ordinalp b -> ordinalp c ->
  (a <<o c /\ b <<o c <-> (a +o b) <<o c).
Proof.
move => oa ob oc; rewrite /ord_negl - (osumA oa ob oc).
split; first  by move =>[h ->].
move => h.
suff: b +o c = c by move => h1; rewrite -{2} h h1.
apply:oleA (osum_M0le ob oc).
by move: (osum_M0le oa (OS_sum2 ob oc)); rewrite h.
Qed.

Lemma ord_negl_sum3 a b c:
  ordinalp c -> a <=o b -> b <<o c -> a <<o c.
Proof. 
move => oc h1; move: (h1) => [oa _ _].
by  move: (odiff_pr h1) => [od -> /(ord_negl_sum1 oa od oc) []].
Qed.

Lemma ord_neg_sum4 a b: ordinalp a -> ordinalp b -> 
  a <<o (a +o b) -> a <<o b.
Proof. move => oa ob; apply: osum2_simpl; fprops. Qed.

Lemma ord_negl_prod a b c: ordinalp a -> ordinalp b -> 
   \0o <o c -> a <<o b ->  a <<o (b *o c).
Proof.
move=> oa ob  cnz lab. 
move: (ord_rev_pred cnz) => [oy ->].
rewrite (oprodD OS1 oy ob) (oprod1r ob).
apply: ord_negl_sum; fprops.
Qed.

Lemma ord_negl_prodr a b c: ordinalp a -> ordinalp b -> ordinalp c ->
   a <<o b ->  c *o a <<o (c *o b).
Proof.
by move => oa ob oc; rewrite /ord_negl - (oprodD oa ob oc) => ->.
Qed.


Lemma ord_negl_pint a b n : natp n -> ordinalp a -> ordinalp b -> 
  a <<o b -> a *o n <<o b.
Proof.
move => nN oa ob H; move: n nN.
apply:Nat_induction; first by rewrite oprod0r /ord_negl (osum0l ob).
move => n nN Hr; rewrite (succ_of_nat nN) (oprod2_succ oa (OS_nat nN)).
by apply/(ord_negl_sum1 (OS_prod2 oa (OS_nat nN)) oa ob). 
Qed.


Lemma ord_negl_alt a b: ordinalp a -> ordinalp b ->
  (a <<o b <-> a *o omega0 <=o b).
Proof.
move => oa ob.
split => lab.  
  case: (ozero_dichot oa);first by move ->; rewrite oprod0l; apply:ole0x.
  move /oprod_normal=> pn; rewrite(proj2 pn _ omega_limit). 
  apply:(ord_ub_sup ob) => t /funI_P [n nN ->].
  case:(ord_negl_lt (OS_prod2 oa (OS_nat nN)) ob (ord_negl_pint nN oa ob lab)).
    by move => [-> _]; apply:ole0x.
  by case.
suff hh: a <<o a *o omega0 by exact:(ord_negl_sum' oa hh lab). 
by rewrite /ord_negl (oprod2_nsucc oa OS_omega) (osum_int_omega olt_1omega).
Qed.

Lemma ofinite_plus_infinite x y:
  finite_o x -> ordinalp y -> infinite_o y -> x +o y = y.
Proof.
move: OS_omega=> oo ha hb /(omega_P1 hb) hc. 
move /omega_P2: (ha) => /(oltP oo) /osum_int_omega hd.
by apply: (ord_negl_sum' (proj1 ha) hd).
Qed.

Lemma ord_negl_p1 b:  b <o omega0 -> b <<o omega0.
Proof. apply:osum_int_omega. Qed.

Lemma  ord_negl_opow a b: a <o omega0 ^o b -> ordinalp b -> a <<o  omega0 ^o b.
Proof. move => lta ob; exact:(indecomp_prop1 (indecomp_prop4 ob) lta). Qed.

Lemma ord_negl_p2 b e:
  b <o omega0 -> \0o <o e ->  b <<o (oopow e).
Proof.
move => bo /oge1P ne0.
move:(opow_Mo_le ne0); rewrite oopow1 => bb.
exact:(ord_negl_sum' (proj31_1 bo) (osum_int_omega bo) bb).
Qed.

  
Lemma ord_negl_p4 a b: a <o b -> (oopow a) <<o (oopow b).
Proof.
move => ltab; move:(ltab) => [[oa ob _] _].
apply/(ord_negl_alt (OS_oopow oa) (OS_oopow ob)).
by rewrite  - (oopow_succ oa); apply:opow_Mo_le;apply/oleSltP.
Qed.


Lemma ord_negl_p5 e c e' c':
  c <o omega0  -> e <o e' -> \0o <o c' ->
  ((oopow e) *o c) <<o ((oopow e') *o c').
Proof.
move /(oltP OS_omega) => cN  ltee' cnz.
have oc:= (OS_nat cN).
have oc':= proj32_1 cnz.
move:(OS_oopow (proj31_1 ltee')) (OS_oopow (proj32_1 ltee')) => ooe ooe'.
apply:(ord_negl_prod (OS_prod2 ooe oc) ooe' cnz). 
exact:(ord_negl_pint cN ooe ooe' (ord_negl_p4 ltee')). 
Qed.


Lemma ord_negl_p6 e f n:
  natp n ->  CNFr_ax f (csucc n) ->  
  e <o (f n) -> (oopow e) <<o (CNFrv f (csucc n)).
Proof.
move: OS_omega => oo nN h ef.
have [[oe op _] _] :=ef.
have o1:= OS_pow oo oe.
have o2:= OS_pow oo op.
have lt1:= (ord_negl_p4 ef).
rewrite /CNFrv (osum_fS _ nN); apply: ord_negl_sum => //.
exact:(OS_CNFr0 nN (CNFr_ax_s nN h)).
Qed.

Lemma ord_negl_pg (f:fterm) n (g:fterm) m:
  natp n ->  CNFr_ax f (csucc n) ->  
  natp m ->  CNFr_ax g (csucc m) ->  
  (g m <o f n <->  CNFrv g (csucc m) <<o CNFrv f (csucc n)).
Proof.
move=> nN cf mN cg; split.
  rewrite (CNFr_rec _ nN) => t2.
  have p2: ordinalp (omega0 ^o f n) by apply:(OS_pow OS_omega (proj32_1 t2)).
  have p3 := (OS_CNFr0 nN (CNFr_ax_s nN cf)). 
  apply: (ord_negl_sum (OS_CNFr0 (NS_succ mN) cg) p2 p3).
  move: m mN cg t2;apply: Nat_induction.
    rewrite succ_zero => ax1 lt1.
    have h0:= (OS_pow  OS_omega(proj31_1 lt1)).
    by rewrite /CNFrv (osum_f1 (f:= oopow \o g) h0);apply:ord_negl_p4.
  move => m mN Hrec cdg ltspd.
  move: OS_omega (NS_succ mN) => oo smN.
  rewrite (CNFr_rec _ smN).
  have ax2:= (CNFr_ax_s smN cdg).
  have o1:= (OS_pow oo (proj31_1 ltspd)).
  apply/(ord_negl_sum1 o1 (OS_CNFr0 smN ax2) p2); split.
    by apply: (ord_negl_p4).
  apply: Hrec => //.
  exact : (ole_ltT (proj2 cdg m mN (cltS smN)) ltspd).
rewrite (CNFr_rec _ mN) => t2.
have ax2:= (CNFr_ax_s mN cg).
have o0:=  (proj1 cg _ (cltS mN)).
have o2:=  (proj1 cf _ (cltS nN)).
have o1:= (OS_pow OS_omega o0).
have o4:=(OS_CNFr0 (NS_succ nN) cf).
move:(ord_negl_sum1 o1 (OS_CNFr0 mN ax2) o4).
move/(ord_negl_sum1 o1 (OS_CNFr0 mN ax2) o4):t2 => [/(ord_negl_alt o1 o4)].
rewrite - (opow_succ OS_omega o0) => ha _.
move:(ole_ltT ha (CNFr_p4 nN cf)).
by move/(opow_Meqltr ole_2omega (OS_succ o0) (OS_succ o2))=>/oltSSP.
Qed.


Lemma cantor_of_limit x: limit_ordinal x ->
  exists a n, [/\ ordinalp a, ordinalp n, n <> \0o,
   x = a +o (oopow n) 
   & (a = \0o \/ 
      [/\ limit_ordinal a, (oopow n) <=o a 
       & cardinal x = cardinal a])].
Proof.
move/limit_ordinal_P => [xnz lx].
move: (CNFr_exists (proj32_1 xnz))=> [f [n [nN ax xv]]].
case: (equal_or_not n \0c) => nz.
  by case: xnz; rewrite xv /CNFrv -/n nz osum_f0.
have ax0 := proj1 ax.
have cn1: \1c <=c n by apply: cge1; fprops.
move : (cdiff_pr cn1) (NS_diff \1c nN); set m := _ -c _ => nv mN.
set f1 :=  (fun i => oopow (f i)).
have ha: ord_below f1 (\1c +c m).
   move => i; rewrite nv => lin; apply:(OS_oopow  (ax0 _ lin)).
have hb:  ordinalp (f \0c) by apply:ax0; apply/strict_pos_P1. 
have hc:= (OS_pow OS_omega hb).
move: xv; rewrite /CNFrv -/n -nv.
rewrite (osum_fA NS1 mN ha) (osum_f1 (f := f1) hc) {2} /f1.
rewrite -/(CNFrv _ _); set f2:= (fun i : Set => f (i +c \1c)).
have ax3: CNFr_ax f2 m.
  split. 
    move => i im; apply: ax0; rewrite - nv (csumC \1c). 
    apply:csum_Mlteq; fprops.
  move => i iN sim.
  have eq:  (csucc i +c \1c) = csucc (i +c \1c) by rewrite (csum_Sn _ iN).
  rewrite /f2 eq; apply:(proj2 ax); first by apply:(NS_sum iN NS1).
  rewrite - nv (csumC \1c) - eq; apply:csum_Mlteq; fprops.
move:(OS_CNFr0 mN ax3); set a := CNFrv f2 m => oa.
case (equal_or_not (f \0o) \0o)=> ez.
  rewrite ez oopow0 (osucc_pr oa) => xsa.
  by move:(oltS oa); rewrite -xsa; move/lx => []; rewrite - xsa.
exists a,(f \0c);split => //.
case: (equal_or_not m \0c) => mz.
  by left;  rewrite /a mz /CNFrv osum_f0.
have cm1: \1c <=c m by apply: cge1; fprops.
move : (cdiff_pr cm1) (NS_diff \1c mN); set m' := _ -c _ => mv m'N.
set f1' :=  (fun i => oopow (f2 i)).
have oo1:ordinalp (f1' \0c).  
  by apply: OS_oopow;apply:(proj1 ax3); apply/strict_pos_P1.
have ha': ord_below f1' (\1c +c m').
  move => i il; apply: OS_oopow; apply: (proj1 ax3); ue.
have sn0:csucc \0c <c n by rewrite - nv succ_zero;apply:csum_M0lt; fprops.
have ez0: f \0c <=o f \1c. 
  by move: (proj2 ax _ NS0 sn0); rewrite succ_zero. 
have ez': \0o <o  f \1c.
  split; first by  move: (ez0) => [_ /ole0x h2 _].
  move => b; case ez;rewrite - b in ez0; exact: (ole0 ez0).
move:(osum_fA NS1 m'N ha'); rewrite mv -/(CNFrv _ _) -/a.
rewrite (osum_f1 oo1); rewrite /f1' /f2 (csum0l CS1) => eq2.
have ax4: CNFr_ax  (fun z : Set => f ((z +c \1c) +c \1c)) m'. 
  split. 
    move => i im; apply: (proj1 ax3); rewrite - mv (csumC \1c). 
    apply:csum_Mlteq; fprops.
  move => i iN sim.
  have eq:  (csucc i +c \1c) = csucc (i +c \1c) by rewrite (csum_Sn _ iN).
  rewrite /f2 eq; apply:(proj2 ax3); first by apply:(NS_sum iN NS1).
  rewrite - mv (csumC \1c) - eq; apply:csum_Mlteq; fprops.
have sa:= (OS_CNFr0 m'N ax4).
have sb:= (opow_Mo_le ez0).
have la: limit_ordinal a.
  rewrite eq2;exact:(osum_limit sa (indecomp_limit2 ez')).
have le3: omega0 ^o f \0c <=o a.
  rewrite eq2; apply: (oleT sb); apply: (osum_M0le sa (proj32 sb)).
right; split => //.
rewrite xv (osum_cardinal oa hc).
move: (ocle1 le3) => pc.
have pb: omega0 <=o oopow (f \0c).
   rewrite - oopow1; apply: opow_Mo_le; fprops.
move: (ocle1 (oleT pb le3)).
rewrite (card_card CS_omega) => pd.
by apply: csum_inf => //; apply: (cle_inf_inf CIS_omega).
Qed.

Lemma finite_rems_aux f n a b:  natp n ->  CNFr_ax f (csucc n) ->
   ordinalp a -> ordinalp b -> CNFrv f (csucc n) = a +o b ->
   (CNFrv f (csucc n) = b /\ a <o oopow (f n))
   \/ (exists a', [/\  ordinalp a', a = oopow (f n) +o a' &
                       CNFrv f n = a' +o b ]).
Proof.
move => nN axn oa ob sab.
move:(proj1 axn n (cltS nN)) => ofn.
move: (OS_pow OS_omega ofn) => op1.
have eq1:= (CNFr_rec f nN).
have ops := (OS_CNFr0 nN (CNFr_ax_s nN axn)).
case: (oleT_el op1 oa)=> lta; [right | left].
  move:(odiff_pr lta); set a' := _ -o _; move => [oa' eq2].
  exists a'; split => //.
  move: sab; rewrite eq1 eq2 - osumA //. 
  by move/(osum2_simpl ops (OS_sum2 oa' ob) op1).
split=>//;move:(ord_negl_opow  lta ofn) => na.
move:(ord_negl_sum oa (proj32_1 lta) ops na).
by rewrite -eq1 sab => /(ord_neg_sum4 oa ob);rewrite/ord_negl - sab. 
Qed.


Lemma finite_rems2 f n b:  natp n ->  CNFr_ax f n -> ordinalp b ->
  ((exists2 a, ordinalp a & (CNFrv f n)= a +o b) <->
   (exists2 k, k<=c n & b = CNFrv f k)).
Proof.
move => nN ax ob; split.
  move:n nN ax; apply:Nat_induction. 
    move => ax [a oa] /esym; rewrite /CNFrv osum_f0.
    move/(osum2_zero oa ob) => [ _ ->]; exists \0c; fprops.
    by rewrite osum_f0.
  move => n nN Hrec axn [a oa bv].
  case:(finite_rems_aux nN axn oa ob bv).
    move =>[ bc _ ]; exists (csucc n); fprops.
  move => [a' [oa' av asum]].
  have h':exists2 a, ordinalp a & CNFrv f n = a +o b by exists a'.
  move: (Hrec (CNFr_ax_s nN axn) h') =>[k lkn kv]; exists k => //.
  exact:(cleT lkn (cleS nN)).
move=> [k lkn ->].
have kN:= (NS_le_nat lkn nN).
move:(cdiff_pr lkn); move: (NS_diff k nN); set m:= _ -c _=> mN dv.
have ax2: ord_below (fun i => oopow (f i)) (k +c m).
  rewrite dv => i /(proj1 ax) ofi; apply: (OS_oopow ofi).
rewrite/CNFrv - dv (osum_fA kN  mN ax2).
have op: ordinalp (CNFrv (fun z => f (z +c k)) m).
  apply:(OS_CNFr0 mN); split.
    by move => i /(csum_Meqlt kN); rewrite csumC dv => /(proj1 ax).
  move => i iN /(csum_Meqlt kN);rewrite csumC dv (csum_Sn _ iN) => lt.
  exact:(proj2 ax _ (NS_sum iN kN) lt). 
by exists (CNFrv (fun z => f (z +c k)) m).  
Qed.


Lemma finite_rems3 f n (c := (CNFrv f n)):  natp n ->  CNFr_ax f n ->
  cardinal (Zo (osucc c) (fun b => exists2 a, ordinalp a & c = a +o b)) =
  csucc n.
Proof.
move => nN ax; set E := Zo _ _.
have smon k: k <=c n ->  CNFrv f k <=o CNFrv f n.
  clear c E; move: n nN ax; apply: Nat_induction.
    move => ax /cle0 ->; exact:(oleR (OS_CNFr0 NS0 ax)).
  move => n nN Hrec ax; case /cle_eqVlt.
    by move ->; exact:(oleR (OS_CNFr0 (NS_succ nN) ax)).
  move/(cltSleP nN) => lkn.
  have le1 := (Hrec (CNFr_ax_s nN ax) lkn).
  have oo := (OS_pow OS_omega(proj1 ax n (cltS nN))).
 rewrite (CNFr_rec _ nN).
 exact: (oleT le1  (osum_M0le oo (proj32 le1))).
have oc:=(OS_CNFr0 nN ax).
have ->: E = fun_image  (Nintc n) (CNFrv f).
  set_extens b.
    move => /Zo_P [/(oleP oc) /proj31 ob]. 
    move /(finite_rems2 nN ax ob) => [k /(NintcP nN) kI ->].
    apply/funI_P;ex_tac.
  move => /funI_P [k /(NintcP nN) kI ->].
  move:(smon _ kI) => sm1.
  have sm: inc (CNFrv f k) (osucc c) by apply/(oleP oc). 
  by apply:(Zo_i sm);apply/(finite_rems2 nN ax (proj31 sm1)); exists k.
rewrite cardinal_fun_image ?(card_Nintc nN) //.
have axr k: k<=c n -> CNFr_ax f k.
  move => lkn;split.
    by move => i lik; exact:(proj1 ax _ (clt_leT lik lkn)).
  move => i iN lik; exact:(proj2 ax _ iN (clt_leT lik lkn)).
move => i j  /(NintcP nN) lin  /(NintcP nN) ljn /= sv.
by case: (CNFr_unique (axr _ lin) (axr _ ljn)
            (NS_le_nat lin nN)(NS_le_nat ljn nN) sv).
Qed.

Lemma finite_rems4 f n k a (b := CNFrv f k) (c := CNFrv f n)
  (a1:= CNFrv (fun i => f (i +c k)) (n -c k)):
  natp n ->  CNFr_ax f n ->  k <=c n -> k <> \0c-> ordinalp a ->
  (c = a +o b <->
   exists d, [/\ ordinalp d, d <o (oopow (f(cpred k))) & a = a1 +o d]).
Proof. 
move => nN axn lkn kp oa.
have kN:= (NS_le_nat lkn nN).
have axk: CNFr_ax f k.
  split; first by move => i lik;exact: (proj1 axn _ (clt_leT lik lkn)).
  move => i iN lik;exact: (proj2 axn _ iN (clt_leT lik lkn)).
have ob: ordinalp b by apply:(OS_CNFr0 kN axk).
have H m : CNFr_ax f m -> k <=c m -> natp m ->
           ordinalp (CNFrv (fun i => f (i +c k)) (m -c k)).
  move => ax' lkn' nN'.
  apply:(OS_osumf (NS_diff k nN')); move => i lik.
  move:(csum_Mlteq kN lik);rewrite (cdiff_rpr lkn') => ll.
  exact:(OS_pow OS_omega (proj1 ax' _ ll)).
have ofb:=(proj1 axk _ (cpred_lt kN kp)).
have pltb : omega0 ^o (f (cpred k)) <=o b.
  move:(cpred_pr kN kp)=> [sa sb]; rewrite sb in axk.
  rewrite /b {2} sb; exact:(CNFr_p2 sa axk). 
split; last first.
  have eq2: c = a1 +o b.
    move:(cdiff_pr lkn); move: (NS_diff k nN); set m:= _ -c _=> mN dv.
    have ax2: ord_below (fun i => omega0 ^o f i) (k +c m).
      rewrite dv => i /(proj1 axn) ofi; apply: (OS_pow OS_omega ofi).
    by move:(osum_fA kN  mN ax2); rewrite  dv.
  move => [d [od ds dv]].
  rewrite eq2 dv - (osumA (H n axn lkn nN) od ob).
  move:(ord_negl_opow ds ofb) => na.
  by rewrite (ord_negl_sum' od na pltb).
rewrite /c /a1; clear c a1.
move: n nN axn lkn a oa.
apply: Nat_induction.
   by move => _ /cle0 k0; case: kp.
move => n nN Hrec axn lkn a oa eq.
case:(finite_rems_aux nN axn oa ob eq).
  move => [bv asmall].
  move:(proj1 (CNFr_unique axn axk (NS_succ nN) kN bv)) => nk.
  rewrite nk cdiff_nn /CNFrv osum_f0 - nk (cpred_pr2 nN).
  by exists a; split => //;rewrite osum0l.
move =>[a' [oa' av eq']].
move:(cltS nN) => ltcpn.
have ax := (CNFr_ax_s nN axn).
have ofn :=(proj1 axn n ltcpn).
have op1:= (OS_pow OS_omega ofn).
case:(cle_eqVlt lkn) => lekn.
  have ops := (OS_CNFr0 nN (CNFr_ax_s nN axn)).
   move:(esym eq'); rewrite  /b lekn (CNFr_rec _ nN) (osumA oa' op1 ops).
   move/(ord_negl_sum1 oa' op1 ops) =>[_].
   rewrite /(ord_negl _ _) - (CNFr_rec f nN). rewrite -/b.
  move/(CNFr_unique axn ax (NS_succ nN) nN).
  by move => [bad _ ]; case: (proj2 ltcpn).
move/(cltSleP nN):lekn => lekn.  
move: (Hrec ax lekn a' oa' eq') => [d [od ds ww]].
exists d; split => //.
rewrite  (cdiffSn nN lekn) (CNFr_rec _ (NS_diff k nN)) (cdiff_rpr lekn).
by rewrite -(osumA op1 (H n ax lekn nN) od) - ww.
Qed.

                                   
(** ** General Cantor Normal Form *)


Definition cnf_s (f: fterm) k := (fun z  => f (z +c k)).
Definition cnf_m (f1 f2:fterm) k := (fun z => Yo (z <c k) (f1 z) (f2 (z -c k))).
Definition cnf_c (f:fterm) n x := (fun z => Yo (z=n) x (f z)).
Definition cnf_nr x k := restr x k.
Definition cnf_ns x k := Lg ((domain x) -c k) (cnf_s (Vg x) k).
Definition cnf_nm x y :=
  Lg ((domain x) +c (domain y)) (cnf_m (Vg x) (Vg y) (domain x)).

Definition posnatp x := natp x /\ \0c <c x.

Lemma PN1: posnatp \1c.
Proof. by split; fprops. Qed.

Lemma PN2: posnatp \2c.
Proof. by split; fprops; apply: clt_02. Qed.

Lemma posnat_prop n: natp n -> n <> \0c -> posnatp n.
Proof.
by move => nN; split => //; apply/(strict_pos_P1 nN). 
Qed.  


Lemma posnat_ordinalp x : posnatp x <-> (\0o <o x /\ x <o omega0).
Proof.
split; move => [ha hb].
  split;[ apply:(oclt hb) | by apply/olt_omegaP].
apply:posnat_prop; [ by apply /olt_omegaP |exact (nesym (proj2 ha))].
Qed.

Lemma posnat_add m n: natp m -> posnatp n -> posnatp (m +c n).
Proof.
move =>  mN [nN /proj2/nesym np];apply:(posnat_prop (NS_sum  mN nN)).
by case/csum_nz.
Qed.
  
Lemma posnat_csum2 m n: posnatp m -> posnatp n -> posnatp (m +c n).
Proof.
by move => [ha _] hb; apply:posnat_add.
Qed.

Lemma PN_prod a b: posnatp a -> posnatp b -> posnatp (a *c b).
Proof.
move => [aN /proj2/nesym az] [nN /proj2/nesym bz].
by apply:posnat_prop; fprops; apply: cprod2_nz.
Qed.

Section CNFQ.
Variable gamma: Set.
  

Definition cantor_mon  (e c: fterm) i := (gamma ^o (e i)) *o (c i).
Definition CNFbv  (e c:fterm) n := osumf (cantor_mon e c) n.

Definition CNFq_ax (e c: fterm) n :=
  [/\ \2o <=o gamma, 
    ord_below e n,
    (forall i, i <c n -> c i <o gamma) &
    (forall i, natp i -> (csucc i) <c n -> (e i) <o (e (csucc i)))].


Definition CNFb_ax  (e c:fterm) n :=
  CNFq_ax e c n /\ (forall i, i<c n -> \0o <o c i).

Lemma CNFq_ax_exten e1 c1 e2 c2 n:
  same_below e1 e2 n -> same_below c1 c2 n -> 
  CNFq_ax e1 c1 n -> CNFq_ax e2 c2 n.
Proof.
move => h1 h2 [a1 a2 a3 a4]; split => //.
+ by move => i lin; rewrite - (h1 _ lin);apply: a2.
+ by move => i lin; rewrite - (h2 _ lin);apply: a3.
+ move => i iN lin; rewrite - (h1 _ lin). 
  by rewrite -(h1 _ (cle_ltT (cleS iN) lin)); apply:a4.
Qed.

Lemma CNFb_ax_exten e1 c1 e2 c2 n:
  same_below e1 e2 n -> same_below c1 c2 n -> 
  CNFb_ax e1 c1 n -> CNFb_ax e2 c2 n.
Proof.
move => h1 h2 [ax1 ax2]; split; first by apply:(CNFq_ax_exten h1 h2 ax1).
by move => i lin; rewrite - (h2 _ lin);apply: ax2.
Qed.

Lemma CNFq_exten e1 c1 e2 c2 n:
  same_below e1 e2 n -> same_below c1 c2 n -> 
  CNFq_ax e1 c1 n -> natp n ->
  (CNFq_ax e2 c2 n /\ CNFbv e1 c1 n = CNFbv e2 c2 n). 
Proof.
move => h1 h2 ax nN; split; first by apply: (CNFq_ax_exten h1 h2 ax).
apply: (osumf_exten nN) => i lin.
by rewrite /cantor_mon (h1 _ lin) (h2 _ lin).
Qed.

Lemma CNFb_exten e1 c1 e2 c2 n:
  same_below e1 e2 n -> same_below c1 c2 n -> 
  CNFb_ax e1 c1 n -> natp n ->
  (CNFb_ax e2 c2 n /\ CNFbv e1 c1 n = CNFbv e2 c2 n). 
Proof.
move => h1 h2 [ax1 ax2] nN.
move: (CNFq_exten h1 h2 ax1 nN) => [ax3 ->]; split => //; split => //.
by move => i lin; rewrite - (h2 _ lin);apply: ax2.
Qed.

Lemma CNFq_p0 e c n i:  CNFq_ax e c n  -> i <c n -> 
  ordinalp (cantor_mon e c i).
Proof.
move => [pa pb pc pd] lin.
apply:OS_prod2; first by apply:(OS_pow (proj32 pa) (pb _ lin)).
exact:(proj31_1 (pc _ lin)).
Qed.

Lemma OS_CNFq e c n : natp n -> CNFq_ax e c n ->
  ordinalp (CNFbv e c n).
Proof.
by move => nb h; apply:(OS_osumf nb) => i /(CNFq_p0  h).
Qed.

Lemma OS_CNFb e c n : natp n -> CNFb_ax e c n ->
  ordinalp (CNFbv e c n).
Proof. by move => nN [/(OS_CNFq nN) h _]. Qed.

Lemma CNFq_p1 e c n: natp n -> 
  CNFbv e c (csucc n) = cantor_mon e c n +o (CNFbv e c n).
Proof.
by move => nN; rewrite /CNFbv (osum_fS _ nN).
Qed.

Lemma CNFq_p2 e c: CNFbv e c \0c = \0o.
Proof. apply: osum_f0. Qed.

Lemma CNFq_p3 e c n : CNFq_ax e c n -> \0o <c n ->
   CNFbv e c \1c = cantor_mon e c \0c.
Proof. move => h np;apply: osum_f1; apply: (CNFq_p0 h np). Qed.

Lemma CNFq_p4 e c n i: CNFb_ax e c n -> i <c n ->
  \0o <o  cantor_mon e c i.
Proof.
move => [[pa pb pc pd] pe] lin.
apply: oprod2_pos; last by exact(pe _ lin).
exact:(opow_pos (olt_leT (olt_02) pa) (pb _ lin)).
Qed.

Lemma CNFq_r_ax e c n m: CNFq_ax e c n -> m <=c n -> CNFq_ax e c m.
Proof.
move => [p1 p2 p3 p4] mn; split.
+ done.
+ move => i im; apply: p2;exact: (clt_leT im mn).
+ move => i im; apply: p3;exact: (clt_leT im mn).
+ move => i iN im; apply: p4 => //; exact(clt_leT im mn).
Qed.

Lemma CNFb_r_ax e c n m: CNFb_ax e c n -> m <=c n -> CNFb_ax e c m.
Proof.
move => [p1 p2] mn; split; first by exact: (CNFq_r_ax p1 mn).
move => i im; apply: p2; exact:(clt_leT im mn).
Qed.

Lemma CNFq_p5 e c n: natp n ->  CNFq_ax e c (csucc n) ->
  CNFq_ax e c n.
Proof. by move => nN ax; apply:(CNFq_r_ax ax  (cleS nN)). Qed.

Lemma CNFb_p5 e c n: natp n ->  CNFb_ax e c (csucc n)  ->
  CNFb_ax e c n.
Proof. by move => nN ax; apply:(CNFb_r_ax ax  (cleS nN)). Qed.

Lemma CNF_exponents_M e c n: natp n -> CNFq_ax e c n ->
  forall i j, i <=c j -> j <c n -> e i <=o e j.
Proof.
move => nN [_ pb _ pc] i j lij ljn.
have lin:=(cle_ltT lij ljn).
have iN := (NS_lt_nat lin nN).
pose r j := e i <=o e j.
have ri:=(oleR (pb _ lin)).
case: (equal_or_not n \0c) => nz.
  by move: lin; rewrite nz; move /clt0.
move: (cpred_pr nN nz) => [mN mv].
have jcn: j <=c cpred n by apply /(cltSleP mN); rewrite -mv.
move: (Nat_induction3 (r := r) iN mN ri)=> h.
apply: (h _ j lij jcn) => k ik kn; rewrite /r => le1.
have kN:= (NS_lt_nat kn mN).
have skn : csucc k <c n. 
  by rewrite mv; apply/(cltSleP mN) /(cleSltP kN).
by move:(pc k kN skn) => [ /(oleT le1) ].
Qed.

Lemma CNF_exponents_sM e c n: natp n -> CNFq_ax e c n ->
  forall i j, i <c j -> j <c n -> e i <o e j.
Proof.
move => nN ax i j lij ljn.
have iN := (NS_lt_nat (clt_ltT lij ljn) nN).
move /(cleSltP iN) :lij => leij.
have sa:=(CNF_exponents_M nN ax leij ljn).
move: ax => [_ _ _ ax]; exact: (olt_leT (ax i iN (cle_ltT leij ljn)) sa).
Qed.

Lemma CNF_exponents_I e c n: natp n -> CNFq_ax e c n ->
  forall i j, i <c n -> j <c n -> e i = e j -> i = j.
Proof.
move => nN /(CNF_exponents_sM nN) => m i j lin ljn eq.
case: (cleT_ell (proj31_1 lin) (proj31_1 ljn)) => cp. 
+ exact.
+ by move: (proj2 (m i j cp ljn)); rewrite eq.
+ by move: (proj2 (m j i cp lin)); rewrite eq.
Qed.

Lemma CNFq_p6 e c n: natp n -> CNFq_ax e c (csucc n) ->
  forall i, i <c n -> e i <o e n.
Proof.
move => nN ax i lin.
exact:(CNF_exponents_sM (NS_succ nN) ax lin (cltS nN)).
Qed.

Lemma CNFq_p7 e c n : CNFq_ax e c n -> \1c <c n ->
   CNFbv e c \2c = cantor_mon e c \1c +o cantor_mon e c \0c.
Proof.
move=> ax n1; move:(cle_ltT cle_01 n1) => ha.
by rewrite - succ_one (CNFq_p1 _ _ NS1) (CNFq_p3 (n:=n) ax).
Qed.

Lemma CNFb_p8 e c n : CNFb_ax e c (csucc n) -> natp n ->
  ordinalp (e n).
Proof. move => [[_ h _ _] _] nN; exact: (h _ (cltS nN)). Qed.

Lemma CNFq_s_ax e c n k m:
  CNFq_ax e c m -> (n +c k) <=c m -> natp k -> natp n ->
  CNFq_ax (cnf_s e k) (cnf_s c k) n.
Proof.
move => [p1 p2 p3 p4] mn kN nN.
have aux: forall i,  i <c n -> i +c k <c m.
  by move => i lin; move:(clt_leT(csum_Mlteq kN lin) mn).
split.
+ done.
+ by move => i /aux /p2.
+ by move => i /aux /p3.
+ move => i iN /aux; rewrite /cnf_s (csum_Sn _ iN); apply: p4; fprops.
Qed.

Lemma CNFb_s_ax e c n k m:
  CNFb_ax e c m -> (n +c k) <=c m -> natp k -> natp n ->
  CNFb_ax (cnf_s e k) (cnf_s c k) n.
Proof.
move => [p1 p2] mn kN nN; split; first by apply: (CNFq_s_ax p1 mn kN nN).
by move => i lin; apply: p2; move:(clt_leT (csum_Mlteq kN lin) mn).
Qed.

Lemma CNFq_m_ax e1 c1 e2 c2 k m:
   natp k -> natp m ->
   CNFq_ax e1 c1 k -> CNFq_ax e2 c2 m ->
   (m = \0c \/ e1 (cpred k) <o e2 \0o) ->
   (CNFq_ax (cnf_m e1 e2 k)  (cnf_m c1 c2 k) (k +c m)). 
Proof.
move => kN mN [p1 p2 p3 p4] [q1 q2 q3 q4] hs.
have aux: forall i, i <c k +c m -> i <c k \/ (~ (i <c k) /\ (i -c k) <c m).
  move => i lik.
  move:(NS_lt_nat lik (NS_sum kN mN))=> iN.
  case: (cleT_el (CS_nat kN) (CS_nat iN)); last by left.
  move => ki; move: (cdiff_pr ki) => s1. 
  right; split; first by move=> /(cleNgt ki).
  apply: (csum_lt2l kN (NS_diff k iN) mN); ue.
rewrite/cnf_m; split.
+ done.
+ move => i /aux []; first by move => ik;by Ytac0; apply: p2.
  by move => [nik likm]; Ytac0; apply: q2.
+ move => i /aux []; first by move => ik;by  Ytac0; apply: p3.
  by move => [nik likm]; Ytac0; apply: q3.
+ move => i iN lis; case:(aux _ lis). 
    move => lt1; move: (cle_ltT (cleS iN) lt1) => li1.
    by Ytac0; Ytac0; apply:p4.
  move => [pa pb]; Ytac0.
  case: hs => hs; first by move: pb; rewrite hs => /clt0.
  have ci:= (CS_nat iN).
  have ck:= (CS_nat kN).
  case: (cleT_ell ck (CS_succ i)) => //.
    move:(cltS iN) => lt1 sa; rewrite sa cdiff_nn; Ytac0.
    have -> //: i = cpred k by rewrite sa cpred_pr1.
  move => /(cltSleP iN) ki.
  case: (aux _ (cle_ltT (cleS iN) lis)); first by move => /(cleNgt ki).  
  move => [pc pd]; Ytac0. 
  have sa: csucc i -c k  = csucc (i-c k).
    move: (cdiff_pr4 kN iN NS0 NS1 ki cle_01).
    rewrite (csucc_pr4 ci) (csum0r ck) (cdiff_n0 NS1) csucc_pr4 //.
    exact: (proj31_1 pd).
  rewrite sa; apply: (q4 _ (NS_diff k iN)); ue.
Qed.

Lemma CNFb_m_ax e1 c1 e2 c2 k m:
   natp k -> natp m ->
   CNFb_ax e1 c1 k -> CNFb_ax e2 c2 m ->
   (m = \0c \/ e1 (cpred k) <o e2 \0o) ->
   (CNFb_ax (cnf_m e1 e2 k)  (cnf_m c1 c2 k) (k +c m)). 
Proof.
move => kN mN [p1 p2] [p3 p4] h1.
split; first by apply:CNFq_m_ax. 
have aux: forall i, i <c k +c m -> i <c k \/ (~ (i <c k) /\ (i -c k) <c m).
  move => i lik.
  move:(NS_lt_nat lik (NS_sum kN mN))=> iN.
  case: (NleT_el kN iN); last by left.
  move => ki; move: (cdiff_pr ki) => s1. 
  right; split; first by move=> /(cleNgt ki).
  apply: (csum_lt2l kN (NS_diff k iN) mN); ue.
move => i /aux []; first by move => ik;by rewrite /cnf_m; Ytac0; apply: p2.
  by move => [nik likm]; rewrite /cnf_m; Ytac0; apply: p4.
Qed.

Lemma CNF_c_ax e c n c0 k:
   \0o <o c0 -> c0 <o gamma -> 
   CNFb_ax e c n -> CNFb_ax e (cnf_c c k c0) n.
Proof.
move => c1 c2 [[p1 p2 p3 p4] p5]; rewrite/cnf_c. 
split; [split => // |]; move => i lin; Ytac cc => //; fprops.
Qed.


Lemma CNFq_A  e c n m:
   natp n -> natp m -> 
   CNFq_ax  e c (n +c m) ->
   [/\  CNFq_ax e c n,  CNFq_ax (cnf_s e n) (cnf_s c n) m &
    CNFbv e c (n +c m) = CNFbv (cnf_s e n) (cnf_s c n) m +o CNFbv e c n].
Proof.
move => nN mN ax.
have pa: ord_below (cantor_mon e c) (n +c m).
  by move => i; apply:CNFq_p0.
rewrite /CNFbv (osum_fA nN mN pa). 
have lt1: n <=c n +c m by apply:Nsum_M0le.
have hb: CNFq_ax e c n by apply:(CNFq_r_ax ax lt1).
have hc //: CNFq_ax  (cnf_s e n) (cnf_s c n) m.
have hh:m +c n <=c n +c m by rewrite csumC; exact: (cleR (proj32 lt1)).
exact:(CNFq_s_ax ax hh nN mN).
Qed.


Lemma CNFq_Al e c n (e1 := fun z => e (csucc z)) (c1 := fun z => c (csucc z)):
   natp n -> 
   CNFq_ax e c (csucc n) ->
   [/\  ordinalp(cantor_mon e c \0c),  CNFq_ax e1 c1 n &
    CNFbv e c (csucc n) = CNFbv e1 c1 n +o (cantor_mon e c \0c)].
Proof.
move => nN ax.
have h1: forall i, i<c n -> (cnf_s e \1c) i = e1 i.
  move => i lin; rewrite /cnf_s /e1 csucc_pr4 //; exact (proj31_1 lin).
have h2: forall i, i<c n -> (cnf_s c \1c) i = c1 i.
  move => i lin; rewrite /cnf_s /c1 csucc_pr4 //; exact (proj31_1 lin).
have eq1: csucc n = \1c +c n by rewrite csumC; exact:(Nsucc_rw nN). 
rewrite eq1 in ax; move: (CNFq_A NS1 nN ax) => [sa sb sc].
have lt1: \0c  <c (\1c +c n) by rewrite - eq1; apply: succ_positive.
rewrite eq1 sc (CNFq_p3 ax lt1).
move:(CNFq_exten h1 h2 sb nN) => [ax1 ->]; split => //.
by apply:(CNFq_p0 ax lt1).
Qed.


Lemma CNFq_pg0 e c n:  CNFq_ax e c n  -> \0o <o gamma.
Proof. move => [pb _ _ _]; exact:(olt_leT olt_02 pb). Qed.

Lemma CNFq_pg1 e c n: natp n -> CNFq_ax e c (csucc n) ->
  CNFbv e c (csucc n) <o (gamma ^o (osucc (e n))).
Proof.
move: n;apply: Nat_induction.
   move => h; rewrite succ_zero (CNFq_p3 h (succ_positive \0c)).
   move: (h) => [bo ax1 ax2 _ ].
   have szp:=(succ_positive \0c).
   move:  (CNFq_pg0 h) (ax1 _ szp) (ax2 _ szp) => bp eo cb.
   rewrite /cantor_mon (opow_succ (proj32_1 bp) eo).
   exact:(oprod_Meqlt cb (opow_pos bp eo)).
move=> n nN Hrec ax1.
have sa:= (Hrec (CNFq_p5 (NS_succ nN) ax1)).
move: (ax1) => [b2 _ ax3 ax2]. 
have snn:= (cltS (NS_succ nN)).
move:(ax2 n nN snn) (CNFq_p0 ax1 snn) => /oleSltP lt1 o1.
move:(olt_leT sa (opow_Meqle (CNFq_pg0 ax1) lt1)) => lt2.
have ha:=proj32_1 lt2.
have cm1:=(ax3 _ snn).
have [[hb bb _] _]:=  cm1. have oee := proj32 lt1.
have lt3: gamma ^o e (csucc n) *o osucc (c (csucc n)) <=o   
    gamma ^o osucc (e (csucc n)).
  by rewrite opow_succ //; apply: oprod_Meqle => //;move /oleSltP: cm1. 
move: (osum_Meqlt lt2 o1).
rewrite (CNFq_p1 _ _ (NS_succ nN)) {2}/cantor_mon - (oprod2_succ ha hb) => h1.
exact: (olt_leT h1 lt3).
Qed.

Lemma CNFq_pg2  e c n a: natp n -> CNFq_ax e c (csucc n) ->
  (e n) <o a -> CNFbv e c (csucc n) <o (gamma ^o a).
Proof.
move => pa pb pc; move: (CNFq_pg1 pa pb) => h. 
move/oleSltP: pc => pc.
exact: (olt_leT h (opow_Meqle (CNFq_pg0 pb) pc)). 
Qed.

Lemma CNFq_pg3 e c n a: natp n -> CNFq_ax e c n ->  ordinalp a ->
  (forall i, i <c n ->  e i <o a) ->
  CNFbv e c n <o (gamma ^o a).
Proof.
move => nN ax oa h; move: (CNFq_pg0 ax) => bp.
case: (equal_or_not n \0c) => nz.
  rewrite nz CNFq_p2 //; apply: opow_pos; fprops.
move: (cpred_pr nN nz) => [qa qb].
rewrite qb in h ax.
have sa: (e (cpred n)) <o a by apply: h; apply: (cltS qa).
rewrite qb; exact:(CNFq_pg2 qa ax).
Qed.

Lemma CNFq_pg e c n: natp n -> CNFq_ax e c (csucc n) ->
  CNFbv e c n <o (gamma ^o (e n)).
move => nN ax.
move: (ax) => [_ ax2 _ _].
exact:(CNFq_pg3 nN (CNFq_p5 nN ax) (ax2 _ (cltS nN)) (CNFq_p6 nN ax)).
Qed.

Lemma CNFq_pg4 e c n: natp n -> CNFb_ax  e c (csucc n) ->
  (gamma ^o (e n)) <=o CNFbv e c (csucc n).
Proof.
move => nN [ax ax2]; move: (ax) => [b2 ax3 _ _].
have nn:= (cltS nN).
have pa:= (oprod_Mle1 (OS_pow (proj32 b2) (ax3 _ nn))  (ax2 _ nn)).
rewrite (CNFq_p1  _ _ nN).
exact: (oleT pa (osum_Mle0 (proj32 pa) (OS_CNFq nN (CNFq_p5 nN ax)))).
Qed.

Lemma CNFq_pg5 e c n: natp n -> CNFb_ax e c (csucc n) ->
  \0o <o CNFbv e c (csucc n).
Proof.
move => nN ax.
move: (opow_pos (CNFq_pg0 (proj1 ax)) (CNFb_p8 ax nN)) => cp.
exact:(olt_leT cp (CNFq_pg4 nN ax)). 
Qed.

Lemma CNFb_unique (e1 c1:fterm) n1 (e2 c2:fterm) n2:
  natp n1 -> natp n2 -> CNFb_ax e1 c1 n1 ->  CNFb_ax e2 c2 n2 -> 
  CNFbv e1 c1 n1 = CNFbv e2 c2 n2 ->
  (n1 = n2 /\ forall i, i <c n1 -> e1 i = e2 i /\ c1 i = c2 i).
Proof.
move => n1N n2N; move: n1 n1N n2 n2N; apply: Nat_induction.
  move=> n2 n2N ax1 ax2.
  case: (equal_or_not n2 \0c) => n2z.
    by rewrite n2z => _; split => // i /clt0.
  move: (cpred_pr n2N n2z) => [mb mv] eq.
  rewrite mv in ax2 eq. 
    by move: (proj2 (CNFq_pg5 mb ax2)); rewrite - eq CNFq_p2;case.
move =>n1 n1N Hrec n2' n2'N ax1s ax2s sv.
case: (equal_or_not n2' \0c) => n2z.
  by move: (proj2 (CNFq_pg5 n1N ax1s)); rewrite sv n2z CNFq_p2; case.
move: (cpred_pr n2'N n2z) => []; set n2 := (cpred n2'); move => n2N n2v.
rewrite n2v in ax2s sv.
move: (cltS n1N) (cltS n2N) => lt1 lt2.
move: (ax1s) (ax2s) => [[u1 u2 u3 u4] u5] [[v1 v2 v3 v4] v5].
move: (u2 n1 lt1) (v2 n2 lt2) (u3 n1 lt1) (v3 n2 lt2) => oa1 oa2 of1 of2.
move: (u5 n1 lt1) (v5 n2 lt2) => ob1 ob2.
move: (proj32_1 ob1) (proj32_1 ob2) => oc1 oc2.
move: (CNFb_p5 n1N ax1s)(CNFb_p5 n2N ax2s) => ax1 ax2.
move: (OS_CNFq n1N (proj1 ax1)) (OS_CNFq n2N (proj1 ax2)) => oe1 oe2.
set a1 := CNFbv e1 c1 (csucc n1). 
set a2 := CNFbv e2 c2 (csucc n2). 
move: (erefl a1); rewrite {2} /a1  (CNFq_p1 _ _ n1N) => ha1.
move: (erefl a2); rewrite {2} /a2  (CNFq_p1 _ _ n2N) => ha2.
move: (CNFq_pg n1N (proj1 ax1s)) (CNFq_pg n2N (proj1 ax2s)) => hb1 hb2.
have og1:=(OS_CNFq (NS_succ n1N) (proj1 ax1s)).
have ox1: (ord_ext_div_pr gamma a1 (e1 n1) (c1 n1) (CNFbv e1 c1 n1)).
  split;[ exact | exact| exact |  split; [exact: ha1 | exact | exact | exact]].
have ox2: (ord_ext_div_pr gamma a1 (e2 n2) (c2 n2) (CNFbv e2 c2 n2)).
  rewrite /a1 sv -/a2.
  split;[ exact | exact| exact |  split; [exact: ha2 | exact | exact | exact]].
move: (ord_ext_div_unique u1 og1 ox1 ox2) => [se1 sc1 sr1].
move: (Hrec _ n2N ax1 ax2 sr1) => [n12 etc]; split. 
   by rewrite n2v - n12.
move => i /(cltSleP n1N); case: (equal_or_not i n1) => in1.
   by rewrite in1 {4 6} n12 => _; split. 
by move => nin1; move: (etc _ (conj nin1 in1)).
Qed.

Lemma CNF_singleton c0 e0 (c:= fun _: Set => c0)(e:= fun _: Set => e0):
  ordinalp e0 -> c0 <o gamma ->  \2c <=o  gamma ->
  [/\ CNFq_ax e c \1c, CNFbv  e c \1c = gamma ^o e0 *o c0 &
    (\0o <o c0 -> CNFb_ax e c \1c)].
Proof.
move=> oe co b2.
have aux: CNFq_ax e c \1c.
  rewrite /e/c;split => // i ib. 
  by rewrite - succ_zero;move/(cltSleP NS0)=> /(cltNge (@succ_positive i)).
by rewrite (CNFq_p3 aux clt_01).
Qed.

Lemma CNF_exp_bnd e c n e0:
  \2c <=o gamma -> ordinalp e0 -> natp n ->
  CNFb_ax e c n -> CNFbv e c n <o gamma ^o e0 ->
  (forall i, i <c n -> e i <o e0).
Proof.
move => le1 oe nN ax lt1 i id.
case: (equal_or_not n \0c) => nz.
  by move: id; rewrite nz => /clt0.
move: (cpred_pr nN nz) => [mN mv].
rewrite mv in ax id.
move/(cltSleP mN): id => ipn.
move:(CNF_exponents_M (NS_succ mN) (proj1 ax) ipn (cltS mN)) => ha.
case (oleT_el oe (proj31 ha)) => // hb.
move:(CNFq_pg4 mN ax); rewrite - mv => h1; move:(ole_ltT h1 lt1) => hc.
by move: (opow_Meqle (olt_leT olt_02 le1) (oleT hb ha)) => /(oltNge hc).
Qed.

Lemma CNFb_exists a:
  ordinalp a -> \2c <=o gamma ->
  exists e c n, [/\ CNFb_ax e c n, natp n & a = CNFbv e c n].
Proof.
move=> oa oeb. 
pose p a := exists e c n, [/\ CNFb_ax e c n, natp n & a = CNFbv e c n].
apply: (least_ordinal2 (p := p)) oa => y oy p2.
case: (equal_or_not y \0o) => ynz.
  exists (@id Set), (@id Set), \0c; split; first split.
  + split =>  // i; try move /clt0 => //.
    by move => _ /clt0.
  + by move => i /clt0.
  + fprops.
  + by rewrite CNFq_p2.
move: OS2 => o2.
have cpy1:=(ord_ne0_pos oy ynz).
move: (ord_ext_div_exists oeb cpy1) 
  => [e1 [c1 [rm [oe1 oc1 or [eq1 lt1 lt2 lt3]]]]].
have rmy: rm <o y.
  have p5:=(OS_pow (proj32_1 lt2) oe1).
  have p3: (gamma ^o e1) <=o ((gamma ^o e1) *o c1) by apply: oprod_Mle1.
  move: (osum_Mle0 (proj32 p3) or); rewrite - eq1 => p4.
  exact : (olt_leT  lt1 (oleT p3 p4)).
move: (p2 _ rmy) => [e [c [n [ax nN rv]]]].
have snN:= (NS_succ nN).
pose e' i :=  Yo (i = n) e1 (e i).
pose c' i :=  Yo (i = n) c1 (c i).
exists e', c', (csucc n).
have ha: CNFbv e' c' n = CNFbv e c n.
   rewrite /CNFbv; apply: osumf_exten => // i [ _ lin].
   by rewrite /e' /c' /cantor_mon; Ytac0; Ytac0.
have hb: cantor_mon e' c' n = gamma ^o e1 *o c1.
  by rewrite /cantor_mon /e' /c'; Ytac0; Ytac0.
rewrite (CNFq_p1 _ _ nN) ha - rv hb - eq1.
suff: CNFb_ax e' c' (csucc n) by move => hc; split. 
move: (CNF_exp_bnd oeb oe1 nN ax); rewrite - rv => hx.
move: ax => [[a1 a2 a3 a4] a5]; split; last first.
  rewrite /c';move => i /(cltSleP nN); case (equal_or_not i n).
    by move => -> _; Ytac0.
  move => i1 i2; Ytac0; exact: (a5 _ (conj i2 i1)).
split; first done.
+ rewrite /e';move => i /(cltSleP nN); case (equal_or_not i n).
    by move => -> _; Ytac0.
  move => i1 i2; Ytac0; exact: (a2 _ (conj i2 i1)).
+ rewrite /c';move => i /(cltSleP nN); case (equal_or_not i n).
    by move => -> _; Ytac0.
  move => i1 i2; Ytac0; exact: (a3 _ (conj i2 i1)).
+ rewrite /e';move => i iN /(cltSleP nN) sin.
  have isi:= (clt_leT (cltS iN) sin).
  move: (proj2 isi) => nin; Ytac0.
  case (equal_or_not (csucc i) n) => ne1; Ytac0; first by exact: (hx lt1 _ isi).
  exact:(a4 i iN (conj sin ne1)).    
Qed.


End CNFQ.

Definition CNFb_axo := CNFb_ax omega0. 
Definition CNFbvo := CNFbv omega0. 

Lemma CNFb_change_nv e c n m (c':= (cnf_c c n (m +o (c n)))):
  natp n ->  CNFb_axo e c (csucc n) -> m <o omega0 ->
  (CNFb_axo e c' (csucc n) /\
    CNFbvo e c' (csucc n)  = omega0 ^o (e n) *o m +o CNFbvo e c (csucc n)).
Proof.
move => nN ax mo.
have nn:= cltS nN.
have om:=proj31_1 mo.
move: (ax) => [ [_ a0 a1 _] a2]. 
move: (a2 _ nn) => [[_ ocn _] nnz].
have pa:= (osum2_lt_omega mo (a1 _ nn)).
have pb: \0o <o m +o c n.
  apply: (ord_ne0_pos (proj31_1 pa)).
  by move => h; move:(osum2_zero om ocn h) => [_ ]; apply: nesym.
move: (CNF_c_ax n pb pa ax); rewrite -/c' => ax2; split; first by exact.
have pc:= (OS_pow OS_omega (a0 _ nn)).
have pd:= CNFq_p0 (proj1 ax) nn.
have pe:=(OS_CNFq nN (CNFq_p5 nN (proj1 ax))).
rewrite /CNFbvo.
rewrite ! (CNFq_p1 _ _ _ nN) (osumA (OS_prod2 pc om) pd pe); apply: f_equal2.
  rewrite /cantor_mon /c' /cnf_c; Ytac0.
  by rewrite (oprodD om ocn pc).
apply: (osumf_exten nN) => i [_ lin].
by rewrite /cantor_mon /c' /cnf_c; Ytac0.
Qed.


Lemma CNFb_A e c n m:
   natp n -> natp m -> 
   CNFb_axo e c (n +c m) ->
   [/\  CNFb_axo e c n,  CNFb_axo (cnf_s e n) (cnf_s c n) m &
    CNFbvo e c (n +c m) = CNFbvo (cnf_s e n) (cnf_s c n) m +o CNFbvo e c n].
Proof.
move => nN mN ax.
rewrite /CNFb_axo /CNFbvo.
have pa: ord_below (cantor_mon omega0 e c) (n +c m).
  by move:ax => [ax _] i; apply:CNFq_p0.
rewrite /CNFbv (osum_fA nN mN pa). 
have lt1: n <=c n +c m by apply:Nsum_M0le.
have hb: CNFb_ax omega0 e c n by apply:(CNFb_r_ax ax lt1).
rewrite csumC in pa.
have hc //: CNFb_ax omega0  (cnf_s e n) (cnf_s c n) m.
have hh:m +c n <=c n +c m. rewrite csumC;apply: (cleR (proj32 lt1)).
exact:(CNFb_s_ax ax hh nN mN).
Qed.


Lemma CNFb_Al e c n (e1 := fun z => e (csucc z)) (c1 := fun z => c (csucc z)):
   natp n -> 
   CNFb_axo e c (csucc n) ->
   [/\  ordinalp(cantor_mon omega0 e c \0o),  CNFb_axo e1 c1 n &
    CNFbvo e c (csucc n) = CNFbvo e1 c1 n +o (cantor_mon omega0 e c \0o)].
Proof.
move => nN [ax1 ax2]; move:(CNFq_Al nN ax1) => [sa sb sc]; split => //.
split => // i lin; apply: ax2; apply:(cltSS lin).
Qed.


Lemma fgraph_bd x A: fgraph x -> natp (domain x) ->
  (forall i, inc i (domain x) -> inc (Vg x i) A) ->
  inc x (\Po (Nat \times A)).
Proof.    
move => fgx dx vx; apply/setP_P => t tx.
move: (domain_i1 tx) => tdx.
rewrite (in_graph_V fgx tx); exact:(setXp_i (NS_inc_nat dx tdx) (vx _ tdx)).
Qed.

Definition ocoef x i := Q (Vg x i).
Definition oexp x i :=  P (Vg x i).
Definition cnf_size x := (cpred (domain x)).



Section CNF_baseb.
Variable (gamma: Set).
Hypothesis bg2: \2o <=o gamma.


Definition CNFB_ax x :=
  [/\ fgraph x, natp (domain x),
   forall i, inc i (domain x) -> pairp (Vg x i) &
   CNFb_ax gamma (oexp x) (ocoef x) (domain x)].

Definition CNFBv X := CNFbv gamma (oexp X) (ocoef X) (domain X).

Definition CNFB_bound x:= 
  \Po(Nat \times ((osucc x) \times gamma)).

Definition the_CNFB x := 
  select (fun X => CNFB_ax X /\ CNFBv X = x) (CNFB_bound x).

Lemma props_of_b: [/\ ordinalp gamma, gamma <> \0o & \0o <o gamma].
Proof.
move: bg2 => [_ ob _].
have bp:= (olt_leT (olt_02) bg2).
move: (bp) => [_ /nesym bne] //.
Qed.


Lemma CNFB_unique X1 X2: CNFB_ax X1 -> CNFB_ax X2 -> 
   CNFBv X1 = CNFBv X2 -> X1 = X2.
Proof.
move => [p1 p2 p3 p4] [q1 q2 q3 q4] sv.
move:(CNFb_unique p2 q2 p4 q4 sv) =>[sa sb].
apply: (fgraph_exten p1 q1 sa) => i idx.
move/(NltP p2): (idx) => /sb [e1 e2]. 
rewrite - (p3 _ idx).         
by rewrite sa in idx; rewrite - (q3 _ idx) -/(oexp _ _) -/(ocoef _ _)e1 e2.
Qed.

Lemma CNFB_bound_p X: CNFB_ax X -> inc X (CNFB_bound (CNFBv X)).
Proof.
move => [p1 p2 p3 p4].
apply:(fgraph_bd p1 p2) => i idx.
move: (props_of_b) => [ob bnz bp].
move: (p4) => [[p11 p12 p13 p14] p15].
move/(NltP p2): (idx) => lt1.
have la: inc (ocoef X i) gamma  by move:(p13 i lt1) => /(oltP ob).
rewrite - (p3 _ idx) -/(oexp _ _) -/(ocoef _ _); apply: (setXp_i) la.
move: (OS_CNFq p2 (proj1 p4))  => osx.
apply/(oleP osx).
have ot:= (p12 _ lt1).
apply: (oleT (oleT (oprod_M1le bp ot)(opow_Mspec2 ot bg2))).
case: (equal_or_not (domain X) \0c) => nz. 
    by move: lt1; rewrite nz => /clt0.
move: (cpred_pr p2 nz) => [mN mv].
rewrite mv in p4 lt1. 
move:(CNFq_pg4 mN p4); rewrite - mv => eq1.
have aa: i <=c (cpred (domain X)) by apply /(cltSleP mN).
have bb:=(cltS mN).
move: (CNF_exponents_M (NS_succ mN) (proj1 p4) aa bb) => /(opow_Meqle bp).
by move => hc; apply: (oleT hc eq1).
Qed.

Lemma CNFbB_prop n e c (X :=  Lg n (fun i => J (e i) (c i))):
  CNFb_ax gamma e c n -> natp n ->
   CNFB_ax X /\ CNFBv X = CNFbv gamma e c n.
Proof.
move => ax nN.
move:(ax) => [[a1 a2 a3 a4] a5]; rewrite /X.
rewrite /CNFB_ax /CNFBv Lgd.
set e1:= oexp _; set c1:= ocoef _ . 
have h1: same_below e e1 n.
 by move => i /(NltP nN) lin; rewrite /e1/oexp LgV//; aw.
have h2: same_below c c1 n.
  by move => i /(NltP nN) lin; rewrite /c1/ocoef LgV//; aw.
move: (CNFb_exten h1 h2 ax nN) => [sa <-].
split;  [split; [fprops | done | | exact ] | exact].
by move => i iin; rewrite LgV//; fprops.
Qed.

Lemma CNFB_exists x: ordinalp x -> 
   exists2 X, CNFB_ax X &  CNFBv X = x.
Proof.
move => ox.
move: (CNFb_exists ox bg2) => [e [c [n [ax nN ->]]]].
move: (CNFbB_prop ax nN); set X := Lg _ _; move => [sa sb].
by exists X.
Qed.

Lemma the_CNF_p0 x (X:= the_CNFB x): ordinalp x ->  CNFB_ax X /\ CNFBv X = x.
Proof.
move => ox.
suff: (CNFB_ax X /\ CNFBv X = x) /\ inc X (CNFB_bound x) by move => [].
apply: select_pr.
  move: (CNFB_exists ox) => [z za zb]; exists z => //. 
  by rewrite - zb ; apply:CNFB_bound_p.
move => a b' _ [p1 p2] _ [p3 p4].
rewrite - p4 in p2;exact:(CNFB_unique p1 p3 p2).
Qed.

Lemma the_CNF_p1: the_CNFB \0o = emptyset.
Proof.
move:(the_CNF_p0 OS0) => [[p1 p2 p3 p4] p5].
ex_middle nz.
move /domain_set0_P: nz => nz.
move: (cpred_pr p2 nz) => [mN mv].
rewrite /CNFBv mv in p4 p5.
by case: (nesym (proj2 (CNFq_pg5 mN  p4))). 
Qed.

Lemma the_CNF_p2 x (m := (cnf_size (the_CNFB x))): \0o <o x -> 
  natp m /\ domain (the_CNFB x) = csucc m.
Proof.
move => [[ _ ox _] xnz].
move:(the_CNF_p0 ox) => [[_ nN _ ax] sb].
case (equal_or_not (domain (the_CNFB x)) \0c) => nz.
  by move:xnz; rewrite - sb /CNFBv nz /CNFbvo CNFq_p2.
exact: (cpred_pr nN nz). 
Qed.

Lemma the_CNF_p3 e c n: CNFb_ax gamma e c n -> natp n ->
  the_CNFB (CNFbv gamma e c n) = Lg n (fun i => J (e i) (c i)).
Proof.
move => ax nN.
have ox:=(OS_CNFq nN (proj1 ax)).
move:(CNFbB_prop ax nN) (the_CNF_p0 ox) => [sa sb] [sc sd].
rewrite - sd in sb.
symmetry; exact: (CNFB_unique sa sc sb).
Qed.

Lemma OS_degree_aux x:  ordinalp x -> x <> \0o ->
     ordinalp (oexp (the_CNFB x) (cnf_size (the_CNFB x))).
Proof.
move => /the_CNF_p0 [sa sb] xnz.
move: sa => [p1 p2 p3 p4].
case (equal_or_not (domain (the_CNFB x)) \0c) => nz.
  by move:xnz; rewrite - sb /CNFBv nz /CNFbvo CNFq_p2.
move: (p4) => [[_ p12 _ _] _]; apply: p12.
rewrite /cnf_size.
move:(cpred_pr p2 nz) => [mN eq]; rewrite {2} eq; apply: (cltS mN).
Qed.

End CNF_baseb.


Definition cnfp x :=
  [/\ fgraph x, natp (domain x),
   forall i, inc i (domain x) -> pairp (Vg x i) &
   CNFb_axo (oexp x) (ocoef x) (domain x)].

Definition cnfp_nz x:= cnfp x /\ x <> emptyset.

Definition cnf_val X := CNFbvo (oexp X) (ocoef X) (domain X).

Definition cnf_bound x:= 
  \Po(Nat \times ((osucc x) \times omega0)).

Definition the_cnf x := 
  select (fun X => cnfp X /\ cnf_val X = x) (cnf_bound x).

Definition omonomp m := [/\ pairp m, ordinalp (P m) & posnatp (Q m)].

Definition cnf_degree X := oexp X (cnf_size X).
Definition cnf_lc X := ocoef X (cnf_size X).
Definition cnf_rem X := CNFbvo (oexp X) (ocoef X) (cnf_size X).

Definition odegree x :=
  Yo (x = \0o) \0o (cnf_degree (the_cnf x)).
Definition  the_cnf_lc x :=  cnf_lc (the_cnf x).

Definition the_cnf_rem x := cnf_rem (the_cnf x).

Lemma cnfpP x:  cnfp x <-> 
  [/\ fgraph x, natp (domain x),
   forall i, inc i  (domain x) -> omonomp (Vg x i) &
   forall i, natp i -> (csucc i) <c (domain x) -> 
             oexp x i <o oexp x (csucc i)].
Proof.
split; move => [ha hb hc hd].
  move: hd => [[qa qb qc qd] qe]; split => //.
  move => i idx; move/(NltP hb): (idx) => lin.
  split; [ by apply: hc | by apply: qb |  apply/ (posnat_ordinalp)].
  exact: (conj (qe _ lin) (qc _ lin)).
split => //; first by move => i /hc [].
split => //.
  split.
  - apply: ole_2omega.
  - by move => i /(NltP hb)  /hc[].
  - by move => i /(NltP hb)  /hc /proj33/posnat_ordinalp [].
  - exact.    
by move => i /(NltP hb)  /hc /proj33/posnat_ordinalp [].
Qed.

Lemma cnf_val_inj: {when cnfp &, injective cnf_val}.
Proof. by apply:CNFB_unique. Qed.

Lemma the_cnf_p0 x (X:= the_cnf x): ordinalp x -> cnfp X /\ cnf_val X = x.
Proof. exact: (the_CNF_p0 ole_2omega). Qed.

Lemma cnf_val0:  cnf_val emptyset = \0o.
Proof.
by rewrite /cnf_val domain_set0 /CNFbvo /CNFbv osum_f0.
Qed.    

Lemma the_cnf_p0_nz x (y:= the_cnf x): \0o  <o x -> cnfp_nz y /\ cnf_val y = x.
Proof.
move =>[/proj32 ox /nesym xz]; move: (the_cnf_p0 ox) => [ha hb]; split => //.
by split => // az; case: xz; rewrite -hb -/y az cnf_val0.
Qed.

Lemma the_CNF_0: the_cnf \0o = emptyset.
Proof. exact: (the_CNF_p1 ole_2omega). Qed.

Lemma the_cnf_p2 x (m := (cnf_size (the_cnf x))): \0o <o x -> 
  natp m /\ domain (the_cnf x) = csucc m.
Proof. exact: (the_CNF_p2 ole_2omega). Qed.

Lemma the_cnf_p3 e c n: CNFb_axo e c n -> natp n ->
  the_cnf (CNFbvo e c n) = Lg n (fun i => J (e i) (c i)).
Proof.  exact: (the_CNF_p3 ole_2omega). Qed.

Lemma odegree_of_nz x: x <> \0o ->
     odegree x = oexp (the_cnf x) (cnf_size (the_cnf x)).
Proof. by move => h; rewrite /odegree Y_false. Qed.

Lemma odegree_of_pos x: \0o <o x ->
     odegree x = oexp (the_cnf x) (cnf_size (the_cnf x)).
Proof. by move /proj2 /nesym/ odegree_of_nz. Qed.

Lemma OS_degree x:  ordinalp x -> ordinalp (odegree x).
Proof.
move => ox; rewrite /odegree; Ytac xz; first by apply: OS0.
apply:(OS_degree_aux ole_2omega ox xz).
Qed.


Lemma cnf_size_nz x (m:= cnf_size x): cnfp_nz x ->
   natp m /\ domain x = csucc m.
Proof.
move => [ox /domain_set0_P xnz]. 
exact: (cpred_pr (proj42 ox) xnz).
Qed.

Lemma cnf_size_nz_bis x: cnfp_nz x -> 
   inc (cnf_size x) (domain x).
Proof.
by move => ox; move:(cnf_size_nz ox) =>[ha ->]; apply: Nsucc_i.
Qed.


Lemma cnf_size_nz_ter x: cnfp_nz x ->  inc \0c (domain x) /\ \0c <c domain x. 
Proof.
move/cnf_size_nz =>[sN ->]; move:(succ_positive (cnf_size x)) => sp.
by split => //; apply/(NltP (NS_succ sN)).
Qed.



Lemma OS_cnf_val x: cnfp  x -> ordinalp(cnf_val x).
Proof.
move => ox; apply:(OS_CNFb (proj42 ox) (proj44 ox)).
Qed.


Lemma OS_cnf_rem x : cnfp x -> ordinalp (cnf_rem x).
Proof.
move => [_ nN _ [[pa pb pc pd] pe]].
move : (NS_pred nN) => pN.
move: (cpred_le (CS_nat nN)) => le1.
apply:  (OS_CNFb (NS_pred nN)); split.
  split.
  - exact: pa.
  - move => i lin;exact: (pb i (clt_leT lin le1)).
  - move => i lin;exact: (pc i (clt_leT lin le1)).
  - move => i iN lin; exact: (pd i iN (clt_leT lin le1)).  
move => i lin;exact: (pe i (clt_leT lin le1)).
Qed.


Lemma OS_cnf_valp x: cnfp_nz  x -> \0o <o (cnf_val x).
Proof.
move => ox.
move: (cnf_size_nz ox) => [qa qb].
move:(proj44 (proj1 ox)); rewrite /cnf_val qb => ax1.
exact: (CNFq_pg5 qa ax1).
Qed.


Definition cnf_and_val x y :=
  [/\ cnfp x, ordinalp y, the_cnf y =x & cnf_val x = y]. 

Lemma cnf_and_val_pa x: ordinalp x -> cnf_and_val (the_cnf x) x.
Proof.
by move => ox; hnf; move:(the_cnf_p0 ox) =>[ax ->].
Qed.

Lemma cnf_and_val_pb x: cnfp x -> cnf_and_val x (cnf_val x).
Proof.
move => h; hnf.
move:(h) => [ha hb hc hd].
move:  (OS_CNFb hb hd) => ot; split => //.
move: (the_cnf_p0 ot) => [qa qb]; exact (cnf_val_inj qa h qb).
Qed.


Lemma cnf_two_terms n1 c1 n2 c2 
      (x := (oopow n1 *o c1) +o (oopow n2 *o c2))
      (X := variantLc (J n2 c2) (J n1 c1)):
  n2 <o n1 ->  posnatp c1 -> posnatp c2  -> 
  cnf_and_val X x.
Proof.
move=> ha hb hc.
move:(ha) => [[oe2 oe1 _] _].
have <-: cnf_val X =  x.
  rewrite /X/cnf_val/CNFbvo/CNFbv; aw; rewrite - [C2] succ_one.
  rewrite (osum_fS _ NS1) /cantor_mon/ocoef/oexp LgV//; aww.
- rewrite - succ_zero  (osum_fS _ NS0) osum_f0 LgV//;aww.
  move/posnat_ordinalp: hc => [_ /proj31_1 oc2].
  by rewrite (osum0r (OS_prod2 (OS_oopow oe2) oc2)).
apply: cnf_and_val_pb;rewrite/X; apply/cnfpP; split.
- fprops.
- aw; apply: NS2.
- aw => i i2; try_lvariant i2; split; aww.
- aw => i iN; rewrite -[C2] succ_one; move/(cltSSP (CS_nat iN) CS1).
  by move/clt1 => ->; rewrite /oexp succ_zero; aw.
Qed.

Lemma cnf_one_term e c:
  ordinalp e -> posnatp c -> 
  cnf_and_val (Lg \1c (fun _: Set => (J e c)))  ((oopow e) *o c).
Proof.
move => oe pnc; set y := Lg _ _.
move/posnat_ordinalp: (pnc) => [_ /proj31_1 oc].
move: (OS_prod2 (OS_oopow oe) oc)=> om.
have eq1: cantor_mon omega0 (oexp y) (ocoef y) \0c =  ((oopow e) *o c).
  by  rewrite /y/cantor_mon /oexp/ocoef (LgV (set1_1 C0)); aw.
have <-: cnf_val y = ((oopow e) *o c).
  by rewrite /cnf_val /CNFbvo /CNFbv {3} /y Lgd osum_f1 eq1.
apply: cnf_and_val_pb; rewrite/y; apply/cnfpP; split.
- fprops.
- aww.
- aw => i i1; rewrite LgV//; split => //; aww; by apply: PN1.
- by aw; move => i /CS_nat iN; rewrite - succ_zero; move/(cltSSP iN CS0) /clt0.
Qed.



Lemma cnf_singleton1 e: ordinalp e ->
    cnf_and_val (Lg \1c (fun _: Set => (J e \1o))) (oopow e).
Proof.
move => oe; move: (cnf_one_term oe PN1).
by rewrite (oprod1r (OS_oopow oe)).
Qed.

Lemma the_cnf_p4 x (n := odegree x): \0o <o x ->
  oopow n <=o x /\ x <o oopow (osucc n).
Proof.
move => xp; rewrite /n (odegree_of_pos xp).
move: (the_cnf_p2 xp) => [];
set m := cnf_size _; move => mN mv.
move: xp => [[ _ ox _] xnz]. 
move:(the_cnf_p0 ox) => [[_ nN _ ax] sb].
rewrite mv in ax; split.
  by move:(CNFq_pg4 mN ax);rewrite -mv -/CNFbvo -/(cnf_val _) sb.
move:(CNFq_pg1 mN (proj1 ax));rewrite -mv -/CNFbvo -/(cnf_val _) sb //.
Qed.

Lemma the_cnf_p5 e c n (x:= CNFbvo e c (csucc n)):
  natp n -> CNFb_axo e c (csucc n) ->
  \0o <o x /\ odegree x = e n.
Proof.
move => nN ax.
move:(CNFq_pg5 nN ax) => xp.
split; first by exact.
rewrite (odegree_of_pos xp).
move:(the_cnf_p2 xp).
rewrite(the_cnf_p3  ax (NS_succ nN)).
set m := cnf_size _. rewrite  Lgd; move => [mN mm].
rewrite (csucc_inj (CS_nat nN) (CS_nat mN) mm) /oexp LgV//; aw; trivial.
exact (Nsucc_i mN).
Qed.

Lemma the_cnf_p6 a e: ordinalp e ->  \0o <o a -> a <o (oopow e) ->
  odegree a <o e.
Proof.
move => oe ap lta.
have lt2:= (ole_ltT (proj1 (the_cnf_p4 ap)) lta).
have od:= (OS_degree (proj32_1 ap)).
by rewrite (opow_Meqltr ole_2omega od oe). 
Qed.



Lemma odegree_opow n:ordinalp n -> odegree (oopow n) = n.
Proof.
move => oe; rewrite (odegree_of_pos (oopow_pos oe)).
rewrite (proj43 (cnf_singleton1 oe)) /oexp/cnf_size Lgd.
rewrite LgV// ?cpred1;aw; trivial; apply: (set1_1 \0c).
Qed.

Lemma odegree_one: odegree \1o = \0o.
Proof. by rewrite - (@opowx0  omega0) (odegree_opow OS0). Qed.

Lemma odegree_omega: odegree omega0 = \1o.
Proof. by rewrite - (opowx1  OS_omega) (odegree_opow OS1). Qed.

Lemma odegree_zero:  odegree \0o = \0c.
Proof. by rewrite /odegree; Ytac0. Qed.

Lemma odegree_of_monomial e c (x := oopow e *o c):
  ordinalp e -> posnatp c ->  
  \0o  <o x /\ odegree x = e.
Proof.
move => oe cp.
have xp: \0o <o x.
  move/posnat_ordinalp: cp => [cp _].
  apply: (oprod2_pos (oopow_pos oe) cp).
split => //.
rewrite (odegree_of_pos xp).
rewrite (proj43 (cnf_one_term oe cp)) /oexp/cnf_size Lgd.
rewrite LgV//; aw; trivial; rewrite cpred1; apply: (set1_1 \0c).
Qed.

  
Lemma odegree_finite x :  x <o omega0 -> odegree x = \0o.
Proof.
move => xo.
case: (ozero_dichot (proj31_1 xo)) => xp; first by rewrite xp odegree_zero.
case: (ozero_dichot (OS_degree (proj31_1 xo))) => dp //.
case: (oltNge (ole_ltT (proj1 (the_cnf_p4 xp)) xo)).
by move/oge1P: dp => /opow_Mo_le; rewrite oopow1.
Qed.

Lemma odegree_infinite x :  omega0 <=o x -> \0o <o odegree x.
Proof.
move => xo.
case: (ozero_dichot (OS_degree (proj32 xo))) => oz //.
move: (proj2(the_cnf_p4 (olt_leT olt_0omega xo)));rewrite oz osucc_zero oopow1.
by move/oltNge.
Qed.


Lemma the_cnf_split x (e:= odegree x)  (c:= the_cnf_lc x) (r := the_cnf_rem x):
  \0o <o x -> [/\ \0o <o c, c <o omega0, r <o oopow e & 
    x =  oopow e *o c +o r].
Proof.
move => xp.
move:(the_cnf_p2 xp); rewrite /e /c/r (odegree_of_pos xp).
set m := cnf_size _; move => [mN Pv].
move: (the_cnf_p0 (proj32_1 xp)) => [[_ nN _]].
rewrite /CNFBv Pv.
move => sb sc.
move: (sb) => [[a1 a2 a3 a4] a5].
split.
+ exact:(a5 _ (cltS mN)).
+ exact:(a3 _ (cltS mN)).
+ exact:(CNFq_pg mN (proj1 sb)).
+ by rewrite -{1} sc /cnf_val Pv - (CNFq_p1 _ _ _ mN).  
Qed.


Lemma the_cnf_omega_kj j k (X := omega0 *o j +o k):
  posnatp j  -> natp k -> 
  \0o <o X /\  [/\ odegree X = \1o,  the_cnf_lc X = j & the_cnf_rem X = k].
Proof.
move => pnj kN.
have ok :=  (OS_nat kN).
move/posnat_ordinalp: (pnj) => [jp jlo].
have lt0:= (oprod2_pos olt_0omega jp).
have xp: \0o <o X. 
  apply: (olt_leT lt0  (osum_Mle0 (proj32_1 lt0) ok)).
rewrite (odegree_of_pos xp).
split; first exact.
case: (czero_dichot (CS_nat kN)) => kz.
  have cp1:  inc (cpred \1c) \1c by rewrite cpred1; apply: (set1_1 \0c).
  rewrite /X kz(osum0r (proj32_1 lt0)) - oopow1.
  move: (cnf_one_term OS1 pnj)=> [qa qb qc qd].
  rewrite /the_cnf_lc /the_cnf_rem qc /cnf_lc /cnf_rem/cnf_size.
  aw; rewrite /oexp/ocoef ! LgV//; aw.
  by rewrite cpred1 /CNFbvo /CNFbv osum_f0.
have ->: X = oopow \1o *o j +o oopow \0c *o k.
   by rewrite oopow0 oopow1 (oprod1l ok).
move: (cnf_two_terms olt_01 pnj  (conj kN kz)) => [qa qb qc qd].
rewrite /the_cnf_lc /the_cnf_rem qc  /cnf_lc /cnf_rem/cnf_size; aw.
rewrite cpred2 /CNFbvo /CNFbv - {3} succ_zero  (osum_fS _ NS0) osum_f0.
rewrite /ocoef /oexp /cantor_mon; aw.
by rewrite opowx0 (oprod1l ok) (osum0r ok).
Qed.

Lemma the_cnf_omega_k k (X := omega0 +o k):
  natp k -> 
  [/\ \0o <o X, odegree X = \1o &  the_cnf_rem X = k]. 
Proof.
move => kN.
move:(the_cnf_omega_kj PN1 kN ).
by rewrite (oprod1r OS_omega); move => [ra [rb rc rd]].
Qed. 

(** Valuation *)

Definition ovaluation x := oexp (the_cnf x) \0c.

Lemma ovaluationE e c n (x:= CNFbvo e c (csucc n)):
  natp n -> CNFb_axo e c (csucc n) ->
  ovaluation x = e \0c.
Proof.
move => nN ax.
move:(CNFq_pg5 nN ax) => xp.
rewrite /x /ovaluation (the_cnf_p3  ax (NS_succ nN)).
by rewrite /oexp LgV //; aw;trivial;  apply/(NleP nN); apply: cle0n.
Qed.

Lemma OS_valuation x: \0o <o x -> ordinalp (ovaluation x).
Proof.
move => xp.
apply: (proj42(proj1 (proj44 (proj1 (the_cnf_p0 (proj32_1 xp)))))).
rewrite (proj2(the_cnf_p2 xp)); apply: succ_positive.
Qed.

Lemma ovaluation_opow n: ordinalp n -> ovaluation (oopow n) = n.
Proof.
move => on.
rewrite /ovaluation (proj43(cnf_singleton1 on)) /oexp LgV//; aw; trivial.
by apply: set1_1.
Qed.

Lemma ovaluation1 x: \0o <o x ->
   exists2 y, ordinalp y & x = y +o oopow (ovaluation x).
Proof.
move => xp.
move: (the_cnf_p0 (proj32_1 xp)) => [ax0 xv].
move: (ax0) (the_cnf_p2 xp) => [_ pb _ ax] [nN pc].
rewrite /ovaluation -{1} xv /CNFBv.
rewrite pc in ax.
move:(CNFb_Al nN ax)=> [oc3 ax3]; rewrite - pc /cnf_val => ->. 
set y := CNFbvo _ _ _.
rewrite /cantor_mon.
set a := oexp _ _; set b := ocoef _ _.
have oy: ordinalp y by apply:OS_CNFb.
move:ax => [[_ h1 h2 _] h3].
have lt0:=(succ_positive (cnf_size (the_cnf x))).
move:(h1 _ lt0) (h2 _ lt0)(h3 _ lt0); rewrite -/a -/b => oa /olt_omegaP bN bp.
have [/proj32 ob /nesym bnz]:= bp.
have ooa:ordinalp (omega0 ^o a). by fprops.
move: (cpred_pr bN bnz) =>[np ->]; move:(OS_nat np) => op.
have ooc:= (OS_prod2 ooa op).
rewrite (succ_of_nat np) (oprod2_succ ooa op) (osumA oy ooc ooa).
exists (y +o omega0 ^o a *o cpred b) => //; fprops.
Qed.

Lemma ovaluation2 x: \0o <o x -> ovaluation x = \0o -> osuccp x.
Proof.
move => xp vz; move: (ovaluation1 xp) => [y oy ->].
rewrite vz oopow0 (osucc_pr oy); exists y => //. 
Qed.

Lemma ovaluation3 x: \0o <o x -> \0o <o ovaluation x ->
  limit_ordinal x.
Proof.
move => xp vz; move: (ovaluation1 xp) => [y oy ->]; apply:(osum_limit oy).
by apply:indecomp_limit2.
Qed.

Lemma ovaluation2_rev x: osuccp x -> ovaluation x = \0o.
Proof.
move => osx.
move:(osx) =>[a oa av].
move:(olt0S oa); rewrite - av => xp.
case: (ozero_dichot (OS_valuation xp)) => // vp.
case:(limit_nonsucc' (ovaluation3 xp vp) osx).
Qed.

Lemma ovaluation3_rev x: limit_ordinal x ->  \0o <o x /\ \0o <o ovaluation x.
Proof.
move => lx; move:(limit_pos lx) => xp; split => //.
case: (ozero_dichot (OS_valuation xp)) => vp //.
case: (limit_nonsucc' lx (ovaluation2 xp vp)). 
Qed.


Lemma ord_negl_p8 ep cp p en cn n:
  CNFb_axo ep cp (csucc p) -> CNFb_axo en cn (csucc n) ->
  natp p -> natp n -> ep p <o en n ->
  (CNFbvo ep cp (csucc p)) <<o (CNFbvo en cn (csucc n)).
Proof.
move => axp axn pN nN ln.
have snN:= NS_succ nN.
set x := CNFbvo en cn (csucc n).
have aux: forall e c, 
   c <o omega0 -> e <o (en n) -> ((omega0 ^o e) *o c)  <<o x.
  move => e c cb ef; rewrite /x.
  move: (proj31_1 ef) (proj31_1 cb) => oe oc.
  have om:=(CNFq_p0 (proj1 axn) (cltS nN)).  
  rewrite /CNFbvo  (CNFq_p1 _ _ _ nN).
  apply: (ord_negl_sum (OS_prod2 (OS_pow OS_omega oe) oc) om).
     exact: (OS_CNFq nN (CNFq_p5 nN (proj1 axn))).
   apply: (ord_negl_p5 cb ef) (proj2 axn  _ (cltS nN)).
move:p pN axp ln; apply: Nat_induction.
  move => ax1 lt1; move:(ax1) => [[_ _ hc _] _].
  rewrite /CNFbvo succ_zero (CNFq_p3 (proj1 ax1) (succ_positive  \0c)).
  exact: (aux _ _  (hc _ (succ_positive  \0c)) lt1). 
move => p pN Hrec ax1 l1.
have spN:= (NS_succ pN).
have axr:=(CNFb_p5 spN ax1).
have spp:=  (cltS spN).
move:(proj1 ax1) => [_ _ hc ha].
have h0:= (olt_leT (ha p pN spp) (proj1 l1)).
have h1 :=(CNFq_p0  (proj1 ax1) spp).
have h6: cp (csucc p) <o omega0 by apply: (hc _ spp).
have ox: ordinalp x by apply:OS_CNFb.
rewrite /CNFbvo (CNFq_p1 _ _ _ spN).
apply/(ord_negl_sum1 h1 (OS_CNFb spN axr) ox).
split; [  exact: (aux _ _  h6 l1) | exact: (Hrec axr h0)].
Qed.

Lemma ord_negl_p7 x y: \0o <o x -> \0o <o y ->
  odegree x <o odegree y -> x <<o y.
Proof.
move => xp yp.
rewrite (odegree_of_pos xp) (odegree_of_pos yp).
move: (the_cnf_p0 (proj32_1 xp))(the_cnf_p0 (proj32_1 yp)).
move:(the_cnf_p2 xp)(the_cnf_p2 yp).
set p:=  (cnf_size _); set q :=  (cnf_size _).
move => [pN sp][nN sn] [ax1 {2} <- ] [ax2 {2} <-]  h.
move: (proj44 ax1) (proj44 ax2); rewrite /cnf_val sp sn => qa qb.
exact: (ord_negl_p8 qa qb pN nN h). 
Qed.



(* study of the CNF *)

Lemma cnf_monomial_inj x: cnfp x ->
  {when inc ^~ (domain x) & , injective (oexp x)}.
Proof.
move => ox i j idx jdx sv; move:(proj42 ox) => nN.
move:  (CNF_exponents_sM (proj42 ox) (proj1(proj44 ox))) => M.
case: (NleT_ell (NS_inc_nat nN idx) (NS_inc_nat nN jdx)).
- by move ->.
- move => lij; move/(NltP nN): jdx  => jdx.
  by case:(proj2(M _ _  lij jdx)).
- move => lij; move/(NltP nN): idx  => idx.
  by case:(proj2(M _ _  lij idx)).
Qed.

Lemma cnf_range_fgraph x: cnfp x -> fgraph (range x).
Proof.
move => ax; move: (ax) => [fgx nN ha hb].
split.
  by move => i /(range_gP fgx) [n /ha px -> ].  
move => i j /(range_gP fgx) [n nds ->] /(range_gP fgx) [m mds ->] sp.
by rewrite (cnf_monomial_inj ax nds mds sp).
Qed.

Lemma cnf_card_range z: cnfp z ->  domain z = cardinal (range z).
Proof.
move => ox; move: (ox) => [ha nN hc hd].
set f := Lf (Vg z) (domain z) (range z).
rewrite - (card_nat nN).
suff: bijection f by move/equipotent_aux => /card_eqP.
apply: lf_bijective.
- by move => t/(inc_V_range ha).
- move => u v udx vdx sv; apply: (cnf_monomial_inj ox udx vdx).
  by rewrite/oexp sv.
- by move => t /(range_gP ha). 
Qed.

Lemma cnf_same_range: {when cnfp &, injective range}.
Proof.
move => x y ox oy sr.
have sd: domain x = domain y by rewrite !cnf_card_range // sr.
move:(ox) (oy) => [fgx nN hax hbx] [fgy _ hay hby].
apply:(fgraph_exten fgx fgy sd) => t tdz.
move: (NS_inc_nat nN tdz) => tN; move: t tN tdz.
apply: least_cardinal2 => i iN Hrec idx.
have: inc (Vg y i) (range x) by rewrite sr; apply: (inc_V_range fgy); ue.
move/(range_gP fgx) => [j jdx pv].
have jN:= (NS_inc_nat nN jdx).
case: (NleT_ell jN iN) => lji; first by rewrite pv lji.
  move: (Hrec _ lji jdx); rewrite - pv => sv.
  rewrite sd in idx jdx.
  by rewrite pv (cnf_monomial_inj oy idx jdx (f_equal P sv)).
move/(NltP nN): jdx => jdx.
have ra: oexp x i <o oexp y i.
  move:  (CNF_exponents_sM (proj42 ox) (proj1(proj44 ox)) lji jdx).
  by rewrite /oexp - pv.
clear j jN pv lji jdx.
have: inc (Vg x i) (range y) by rewrite - sr; apply: (inc_V_range fgx).
move/(range_gP fgy) => [j jdx pv].
rewrite - sd in jdx.
have jN:= (NS_inc_nat nN jdx).
case: (NleT_ell jN iN) => lji; first by rewrite pv lji.
  move: (Hrec _ lji jdx); rewrite - pv => sv.
  by rewrite pv (cnf_monomial_inj ox jdx idx (f_equal P sv)).
move/(NltP nN): jdx; rewrite sd  => jdx.
have rb: oexp y i <o oexp x i. 
  move:  (CNF_exponents_sM (proj42 oy) (proj1 (proj44 oy)) lji jdx).
  by rewrite /oexp - pv.
case: (oltNge ra (proj1 rb)).
Qed.


Notation "\0f" := emptyset (only parsing).

Lemma cnfp0: cnfp \0f.
Proof.
apply/cnfpP; hnf; rewrite domain_set0; split.
- exact: fgraph_set0.
- exact: NS0.
- by move => i /in_set0.
- by move => i iN /clt0.
Qed.

Definition cnf_rangep E :=
  [/\ finite_set E, fgraph E & forall x, inc x E -> omonomp x].


Definition cnf_sort E :=
  select (fun x =>  cnfp x /\ range x = E) (\Po (Nat \times E)).


Lemma finite_subset_ord X: finite_set X -> nonempty X -> ordinal_set X -> 
   exists2 n, inc n X & forall m, inc m X -> m <=o n.
Proof.
move: X; apply: finite_set_induction2.
   move => a oa; exists a; fprops => b bb; move: (oa _ bb) => /oleR.
   by rewrite (set1_eq bb).
move => a b Hrec nea osab.
have osa: ordinal_set a. move => t ta; apply: osab; fprops.
move:(Hrec nea osa) =>[c ca cg].
have osb: ordinalp b by apply:osab; fprops.
have osc: ordinalp c by apply: osa.
move: (omax_p1 osb osc)=> [qa qb].
exists (omax  b c); first by  rewrite/omax/Gmax; Ytac w; fprops.
move => t /setU1_P; case; first by move/cg => tt; apply:(oleT tt qb).
by move ->.
Qed.

Lemma cnf_sort_correct E (x := cnf_sort E): cnf_rangep E ->
  cnfp x /\ range x = E.
Proof.
move => ha.
suff: exists2 y, cnfp y & range y = E.
  move => [y yp1 yp2].
  apply: (select_pr1 (p := fun t => cnfp t /\ range t = E)).
    exists y => //; apply/setP_P => t ty.
    move: yp1 => [hu hv _ _]; move:  (domain_i1 ty) => pd.
    move: (in_graph_V hu ty) ->; apply: setXp_i.
      apply: (NS_inc_nat hv pd).
    by rewrite - yp2; apply: (inc_V_range hu pd).
  move =>  a b /= _ [ua ub] _ [uc ud]; rewrite - ud in ub.
  exact: (cnf_same_range ua uc ub).
clear x.
move  /card_finite_setP: (proj31 ha).
move: {2 3} (cardinal E)  (erefl (cardinal E)) => n hb nN.
move: n nN E ha hb; apply: Nat_induction.
  move => E _ ec ; exists \0f; first  exact cnfp0.
  by rewrite (card_nonempty ec) range_set0.
move => n nN Hrec E HE cardE.
case: (emptyset_dichot E) => neE.
  by case:(@succ_nz n); rewrite - cardE neE cardinal_set0.
move: HE => [fsE fgE mnE].
pose F := domain E.
have fsF: finite_set F by apply: finite_fun_image.
have neF: nonempty F by apply:funI_setne.
have osF: ordinal_set F by move => i /funI_P [z /mnE/proj32 oi -> ].
move: (finite_subset_ord fsF neF osF) =>[e0 /funI_P [a aE av] e0p].
have amax: forall z, inc z E -> P z  <=o P a.
  move => z zE; rewrite - av; apply: e0p; apply/funI_P; ex_tac.
move: (esym(cpred_pr5 aE)); rewrite cardE (cpred_pr1 (CS_nat nN)).
clear F fsF neF osF e0p.
set F := E -s1 a; move => cardF.
have sFE: sub F E by move => t/setC1_P [].
have HF: cnf_rangep F.
  split.
  - exact: (sub_finite_set sFE fsE).
  - exact: (sub_fgraph fgE).
  - by move => x /sFE /mnE.
move:(Hrec F HF cardF) => [x ox rx].
move/cnfpP: (ox) =>[fgx dxN qc qd].
move:(cnf_card_range ox); rewrite rx cardF => dxn.
have ndx: ~ inc n (domain x) by rewrite dxn; apply:Nat_decent.
set y := x +s1 (J n a).
have dy: domain y = csucc n.
  by rewrite domain_setU1 (cnf_card_range ox) rx cardF (succ_of_nat nN).
have fgy: fgraph y by apply: (fgraph_setU1 _ fgx ndx).
have dyN: natp (domain y) by rewrite dy; apply:NS_succ.
have y_out: Vg y n = a by apply:(setU1_V_out _ fgx ndx).
have y_in i: i <c n -> Vg y i = Vg x i.
  by move => lin; apply:(setU1_V_in _ fgx ndx); rewrite dxn; apply/(NltP nN).
exists y; last by rewrite range_setU1 rx; apply:setC1_K.
have rb: forall i, inc i (domain y) -> omonomp (Vg y i).
  move => i;rewrite dy => /(NleP nN) /cle_eqVlt; case.
    by move ->; rewrite y_out; case: (mnE a aE).
  by move => id;rewrite (y_in i id); apply: qc;rewrite dxn; apply/(NltP nN).
apply/cnfpP.
split => // i iN;  rewrite /oexp dy => /(cltSleP nN) /cle_eqVlt; case => lt1.
  have lin: i <c n by rewrite - lt1; exact:(cltS iN).
  have gxE: inc (Vg x i) F.
    rewrite - rx; apply: (inc_V_range fgx).
    by rewrite dxn; apply/(NltP nN).
  rewrite /oexp lt1 y_out (y_in _ lin); split. 
    by apply:(amax _ (sFE _ gxE)).
  move/ (proj2 fgE _ _ (sFE _ gxE) aE) => ea.
   by move /setC1_P:gxE => /proj2.
rewrite (y_in _ lt1) (y_in _ (clt_ltT (cltS iN) lt1)); apply: (qd  i iN).
by rewrite dxn.
Qed.
  
Definition Vr x e := Vg (range x) e.
Definition cnf_exponents x :=  domain (range x).


Lemma Vg_out_of_range f x: ~ inc x (domain f) -> Vg f x = emptyset. 
Proof.
move => idx; rewrite /Vg /select; set T := Zo _ _.
case:(emptyset_dichot T); first by move ->; rewrite setU_0.
by move =>  [y /Zo_P [_  /domain_i idf]]; case: idx.
Qed.


Lemma Vr_ne x e: Vr x e <> \0c ->
   inc e (cnf_exponents x).
Proof.
move => h;ex_middle bad; move: h.
by rewrite /Vr (Vg_out_of_range bad).
Qed.

Lemma cnf_coef_or_e_zero d: Vr \0f d = \0c.
Proof.
by rewrite /Vr range_set0 Vg_out_of_range // domain_set0 => /in_set0.
Qed.

Lemma Vr_correct x i: cnfp x -> inc i (domain x) ->
    Vr x (oexp x i) = (ocoef x i).
Proof.
move => ox idx.
move: (ox) => [ha hb hc hd]. 
symmetry; exact:(pr2_V (cnf_range_fgraph ox) (inc_V_range ha idx)).
Qed.

Lemma Vr_posnat x e: cnfp x -> inc e (cnf_exponents x) ->
  posnatp (Vr x e).
Proof.
move=> ox;move: (ox) => /cnfpP [ax _ hb _].
move/funI_P => [z /(range_gP ax) [i idx -> ] ->].
rewrite (Vr_correct ox idx).
exact: (proj33 (hb _ idx)).
Qed.


Lemma cnf_coef_of_lc x: cnfp_nz  x -> 
 cnf_lc x = Vr x (cnf_degree x).
Proof.
move => xnz.
by rewrite /cnf_lc (Vr_correct (proj1 xnz) (cnf_size_nz_bis xnz)).
Qed.

Lemma NS_Vr x e: cnfp x -> natp (Vr x e).
Proof.
move => ox.
case: (p_or_not_p (inc e (domain (range x)))); last first.
  rewrite /Vr; move/Vg_out_of_range => ->; apply: NS0.
by move /(Vr_posnat ox) => /proj1.
Qed.

Lemma Vr_exten x y: cnfp x -> cnfp y ->
    (forall e, Vr x e = Vr y e) -> x = y.
Proof.
move: x y.
suff H x y: cnfp x -> cnfp y ->
            (forall e, Vr x e = Vr y e) ->
            sub (range x) (range y).
  move => x y ox oy j; apply: (cnf_same_range ox oy).
  by apply: extensionality; apply H => //.
move => ox oy h t /(range_gP (proj41 ox)) [i idx tv].
move:  (Vr_correct ox idx); rewrite h => eq1.
case:  (inc_or_not  (oexp x i) (domain (range y))) => ety.
  have ->: t = J (oexp x i)(ocoef x i) by rewrite tv ((proj43 ox) _ idx).
  rewrite - eq1 /Vr.
  apply: (fdomain_pr1 (cnf_range_fgraph oy) ety).
move/cnfpP: ox => /proj43=> h1; case (proj2(proj2(proj33(h1 _ idx)))).
by rewrite -/(ocoef x i)- eq1 /Vr (Vg_out_of_range ety).
Qed.


Lemma cnf_exponents_of x (E := cnf_exponents x):
  cnfp x -> (finite_set E /\ ordinal_set E).
Proof.
move => ox.
have aux: cardinal (cnf_exponents x) = domain x.
  rewrite (cnf_card_range ox).
  by apply: cardinal_fun_image; move: (proj2 (cnf_range_fgraph ox)).    
split.
  apply/NatP; rewrite aux; exact: (proj42 ox).
move => t  /funI_P [z /(range_gP (proj41 ox)) [i idy ->]->].
  by apply: (proj42 (proj1 (proj44 ox))); apply/(NltP (proj42 ox)).
Qed.



Lemma posnat_lc x: cnfp_nz x -> posnatp (cnf_lc x).
Proof.
move => xnz; move: (cnf_size_nz_bis xnz) => si.
by move /cnfpP: (proj1 xnz) => [_ _ qa _]; case:(qa _ si).
Qed.


Lemma OS_cnf_degree x:  cnfp_nz x -> ordinalp (cnf_degree x).
Proof.
move => xnz; move: (cnf_size_nz_bis xnz) => si.
by move /cnfpP: (proj1 xnz) => [_ _ qa _]; case:(qa _ si).
Qed.

Lemma cnf_degree_greatest_bis x i: cnfp x ->  i <c (cnf_size x) ->
  oexp x i <o cnf_degree x.
Proof.
move => ox lt1; apply: (CNF_exponents_sM (proj42 ox) (proj1 (proj44 ox)) lt1).
have aux:cnfp_nz x.
  split => //xe.
  by move:lt1; rewrite xe /cnf_size domain_set0 cpred0 => /clt0.
apply/(NltP (proj42 ox)); apply:(cnf_size_nz_bis aux).
Qed.

Lemma cnf_degree_greatest x i: cnfp x -> inc i (domain x) ->
  oexp x i <=o cnf_degree x.
Proof.
move => ox; move: (proj42 ox) => dN /(NltP dN) lidx.
case: (equal_or_not x emptyset) => xe.
  by move: lidx; rewrite xe domain_set0 => /clt0.
move:(cnf_size_nz (conj ox xe)) => [mN mv].
move: lidx; rewrite mv => /(cltSleP mN) => /cle_eqVlt; case.
  by move ->; apply: oleR; apply: OS_cnf_degree.
by move/(cnf_degree_greatest_bis ox); case.
Qed.


Lemma cnf_sum_prop5 x: cnfp_nz x -> 
  cnf_val x = (oopow (cnf_degree x)) *o (cnf_lc x) +o (cnf_rem x).
Proof.
move => xnz.
move: (cnf_size_nz  xnz) => [qa qb].
by rewrite /cnf_val /cnf_rem qb /CNFbvo /CNFbv (osum_fS _ qa).
Qed.


Lemma cnf_rem_prop1 x: cnfp x -> 
  cnf_rem x = cnf_val (cnf_nr x (cnf_size x)).
Proof.
move =>  /proj42 / NS_pred  ha.
rewrite /cnf_rem /cnf_val /cnf_nr restr_d; apply: (osumf_exten ha).
by move => i iln; rewrite/cantor_mon /oexp /ocoef LgV//; apply/NltP.
Qed.


Lemma cnfp_cnf_nr x k: cnfp x -> k <=c domain x -> cnfp (cnf_nr x k). 
Proof.
move => /cnfpP [ha hb hc hd] lk; rewrite /cnf_nr; apply/cnfpP.
rewrite restr_d; move: (NS_le_nat lk hb) => kN.
split; [  fprops | done | move => i idx | move => i iN idx].
  rewrite LgV//; exact:(hc _ (proj33 lk _ idx)).
move/(NltP kN):(idx)=> idx1.
move/(NltP kN):(clt_ltT (cltS iN) idx) => ik.
rewrite/oexp ! LgV//; apply: (hd _  iN (clt_leT idx lk)).
Qed.


Definition cnf_lt1 x y := exists2 d, 
   (Vr x d <c Vr y d)
   & forall i,  d <o i ->  (Vr x i = Vr y i).

Definition cnf_le x y := [/\ cnfp x, cnfp y & (x = y \/ cnf_lt1 x y)].
Definition cnf_lt x y :=  cnf_le x y /\ x <> y.


Notation "x <=f y" := (cnf_le x y) (at level 60).
Notation "x <f y" := (cnf_lt x y) (at level 60).

Lemma cnf_lt_prop x y: cnfp x -> cnfp y -> (x <f y <-> cnf_lt1 x y).
Proof.
move => ox oy; split.
   by move => [[_ _ ha] hb]; case: ha.
move => ha; split; first by split => //; right.
by move => exy; case: ha=> d /proj2 b _; case: b; rewrite exy.
Qed.

Lemma Vr_ne2 x e: cnfp x -> Vr x e <> \0c ->
 ordinalp e.
Proof.
by move => ox /Vr_ne /(proj2  (cnf_exponents_of ox)).
Qed.

Lemma cnf_leR x: cnfp x -> x <=f x.
Proof. by move => h; split => //; left. Qed.

Lemma cnf_leA x y: x <=f y -> y <=f x -> x = y.
Proof.
move => [ox oy la ][_ _ lb]; case: la => // - [e  ea eb].
case: lb => // - [i ia ib].
have H a b: a <c b -> b <> \0o. 
   move => h; exact: (nesym (proj2 (cle_ltT (cle0x (proj31_1 h)) h))).
move: (Vr_ne2 oy (H _ _ ea))  (Vr_ne2 ox (H _ _ ia)).
move => oe oi; case: (oleT_ell oe oi) => h.
- by rewrite h in ea ia; case: (proj2 (clt_ltT ea ia)).
- by case: (proj2 ia); rewrite (eb _  h).  
- by case: (proj2 ea); rewrite (ib _  h).  
Qed.


Lemma cnf_leT x y z: x <=f y -> y <=f z -> x <=f z.
Proof.
move => lexy  leyz; move: (leyz) => [oy oz];case; [by move <- | move => lyz].
move:  lexy =>[ox _];case; [by move -> | move => [e  ea eb] ].
move: lyz => [i ia ib].
have H a b: a <c b -> b <> \0o. 
   move => h; exact: (nesym (proj2 (cle_ltT (cle0x (proj31_1 h)) h))).
split => //; right.
move: (Vr_ne2 oy (H _ _ ea))  (Vr_ne2 oz (H _ _ ia)).
move => oe oi; case: (oleT_ell oe oi) => h.
- exists e; first by apply: (clt_ltT ea); rewrite h.
  by move => j jle; rewrite eb // ib // -h .
- exists i; first by rewrite eb.
  by move => j lj; rewrite - ib // eb //; apply: (olt_ltT h lj).
- exists e; first by rewrite - ib.
  by move => j lj; rewrite eb // ib //; apply: (olt_ltT h lj).
Qed.
  

Lemma cnf_le_total x y: cnfp x -> cnfp y -> x <=f y \/ y <=f x.
Proof.
move => ox oy.
set F :=Vr.
case:(p_or_not_p (exists e, F x e <> F y e)); last first.
   move => bad; left; split => //; left.
   by apply:(Vr_exten ox oy) => e; ex_middle w; case: bad; exists e.
set E := (cnf_exponents x \cup cnf_exponents y).
have ha e: F x e <> F y e -> inc e E.
  move => ep;rewrite /E;case: (equal_or_not (F x e) \0o) => fz.
    move/nesym: ep; rewrite fz => /Vr_ne; fprops.
  move/Vr_ne: fz; fprops.
move => [e0 e0p].
set Ep := Zo  E (fun e => F x e <> F y e).
have hb e: F x e <> F y e -> inc e Ep by move => he;apply:Zo_i => //; apply:ha.
move: (cnf_exponents_of oy); move => [ qa qb].
move: (cnf_exponents_of ox); move => [ qc qd].
have neF: nonempty Ep by  exists e0; apply: hb.
have fsF: finite_set Ep. 
   by apply:sub_finite_set (setU2_finite qc qa); apply: Zo_S.
have osF: ordinal_set Ep by  move => t /Zo_S /setU2_P;case; fprops.
move:(finite_subset_ord fsF neF osF)=> [e1 /Zo_P[e1E el1] aux].
have e1l e: e1 <o e ->  F x e = F y e.
  move => lt1; ex_middle bad.
  have ee: inc e Ep by  apply: hb.
  by case : (oleNgt (aux _ ee)).
clear qa qb qc qd neF fsF aux.
case: (NleT_ell (NS_Vr e1 ox) (NS_Vr e1 oy))=> cp.
- by  case el1.
- by left; split => //; right; exists e1 => //.
- by right; split => //; right; exists e1 => // i /e1l //.
Qed.  

Lemma cnf_lex0 x: x <=f \0f -> x = \0f.
Proof.
by move => [ha hb]; case => // - [e]; rewrite cnf_coef_or_e_zero => /clt0.
Qed.  

Lemma cnf_le0x x : cnfp x -> \0f <=f x.
Proof.
move => ox; case: (cnf_le_total ox cnfp0) => // /cnf_lex0 <-.
by apply:cnf_leR.
Qed.

Lemma cnf_lt_deg x y: cnfp_nz  x -> cnfp_nz y ->
  cnf_degree x <o cnf_degree y ->  x <f y.
Proof.
move => xp yp ltd.
have H z e: cnfp z -> cnf_degree z <o e -> Vr z e = \0c.
  move => az h; rewrite /Vr Vg_out_of_range //.
  move => /funI_P [k /(range_gP (proj41 az)) [i idx ->] ev ].
  by case: (oltNge h); move: (cnf_degree_greatest az idx); rewrite /oexp - ev.
move: (proj1 xp)(proj1 yp) => ox oy.
split; last by move => eq; case: (proj2 ltd); rewrite eq.
split => //; right; exists (cnf_degree y).
   rewrite (H _ _ ox ltd) - (cnf_coef_of_lc yp).
   by case: (posnat_lc yp).
by move =>  d dle; rewrite (H _ _ oy dle)  (H _ _ ox  (olt_ltT ltd dle)).
Qed.


Lemma cnf_lt_eq_deg x y: cnfp_nz  x -> cnfp_nz y ->
  cnf_degree x = cnf_degree y -> cnf_lc x <c cnf_lc y ->  x <f y.
Proof.
move => xp yp sd ltd.
have H z e: cnfp z -> cnf_degree z <o e -> Vr z e = \0c.
  move => az h; rewrite /Vr Vg_out_of_range //.
  move => /funI_P [k /(range_gP (proj41 az)) [i idx ->] ev ].
  by case: (oltNge h); move: (cnf_degree_greatest az idx); rewrite /oexp - ev.
move: (proj1 xp)(proj1 yp) => ox oy.
split; last by move => eq; case: (proj2 ltd); rewrite eq.
split => //; right; exists (cnf_degree y).
   by rewrite - (cnf_coef_of_lc yp) - sd - (cnf_coef_of_lc xp).
by move =>  d dle; rewrite (H _ _ oy dle) H // sd.  
Qed.

Lemma cnf_le_compat x y: cnfp x -> cnfp y ->
   ( x <=f y <-> cnf_val x <=o cnf_val y).
Proof.
move => ox oy.
pose R := fun x y => x <=f y <-> cnf_val x <=o cnf_val y.
have R0y z: cnfp z -> R emptyset z.
  move => oz;rewrite /R cnf_val0; split => _.
    by apply: ole0x; apply:OS_cnf_val.
  by apply: cnf_le0x.
have Rx0 z: cnfp z -> R z emptyset.
  move => oz;rewrite /R cnf_val0; split => h.
     move/cnf_lex0:h ->; rewrite cnf_val0; apply: (oleR OS0).
  case: (equal_or_not z emptyset) => znz.
    rewrite - znz; apply: (cnf_leR oz).
  by case(oltNge (OS_cnf_valp (conj oz znz))).
pose deg z :=  Yo (z = emptyset)  \0o (cnf_degree z).
have od1 z: cnfp z -> ordinalp (deg z).   
   by move => oe; rewrite /deg; Ytac h; fprops; apply: OS_cnf_degree.
move:(od1 _ ox) (od1 _ oy) => qa qb.
case: (omax_p1 qa qb).
have: ordinalp (omax (deg x) (deg y)) by rewrite /omax/Gmax; Ytac hh.
move: (omax _ _); clear qa qb => d od.
move: d od x y ox oy.
apply: least_ordinal2 => d od Hrec x y ox oy lt1 lt2.
wlog: x y ox oy lt1 lt2  / deg x <=o deg y.
  move => hh; case: (oleT_ee (proj31 lt1) (proj31 lt2)); first by apply: hh.
  move => lt3; move: (hh y x oy ox  lt2 lt1 lt3) => aux.
  move: (OS_cnf_val ox) (OS_cnf_val oy) => oa ob.
  case: (equal_or_not x y) => exy.
   rewrite - exy; split => _; [ apply: (oleR oa) | apply: (cnf_leR ox)].
  split => lt5.
    by case: (oleT_ee oa ob);[ | move/aux => h; case: exy; apply: cnf_leA].
  case: (cnf_le_total ox oy) => // /aux h; case: exy; move: (oleA lt5 h).
  by move/(cnf_val_inj ox oy).
move => ledxdy. 
case: (equal_or_not x emptyset) => xnz; first by  rewrite xnz; apply:R0y.
case: (equal_or_not y emptyset) => ynz; first by  rewrite ynz; apply:Rx0.
case: (ole_eqVlt lt2) => lt2'; last first.
  apply: (Hrec _ lt2' _ _ ox oy ledxdy (oleR (proj31 lt2))).
have yp: cnfp_nz y by [].
have dyv: cnf_degree y = d by rewrite -lt2' /deg; Ytac0.
move :(cnf_sum_prop5 yp); rewrite dyv =>  eq1.
move:(cnf_rem_prop1 oy)  (OS_cnf_rem oy) => ryv ory.
move: (posnat_lc yp) => lcyp.
have lt3: cnf_degree x <=o d.
  by move: ledxdy; rewrite lt2' /deg; Ytac0.
move: (OS_oopow (proj32 lt3)) => ood.
have xp: cnfp_nz x by split.
move: (cnf_size_nz xp) (cnf_size_nz yp)=> [nN sxv] [mN syv].
move: (ox) (oy) => [ox1 ox2 ox3 ox4] [oy1 oy2 oy3 oy4].
case: (ole_eqVlt lt3) => cxy; last first.
  split => _; last first.
    rewrite - dyv in cxy.
    exact: (proj1 (cnf_lt_deg (conj ox xnz) (conj oy ynz) cxy)). 
  move: ox4; rewrite eq1 /cnf_val sxv => axx.
  move /posnat_ordinalp: lcyp => [qa qb].
  apply(oleT (proj1 (CNFq_pg2 nN (proj1 axx) cxy))).
  apply: (oleT (oprod_Mle1 ood qa)).
  apply: (osum_Mle0 (OS_prod2 ood (proj32_1 qa)) ory).
move :(cnf_sum_prop5 xp); rewrite cxy =>  eq2.
move:(cnf_rem_prop1 ox)  (OS_cnf_rem ox) => rxv orx.
move: (posnat_lc xp) => lcxp.
move: (cnf_and_val_pb oy) =>[_ ovy eqa _].
have cyp: \0o <o (cnf_val y) by apply: OS_cnf_valp.
move: (proj43 (the_cnf_split cyp)).
rewrite /the_cnf_rem /odegree eqa (Y_false (nesym (proj2 cyp))) dyv => rys.
move: (cnf_and_val_pb ox) =>[_ ovx eqb _].
have cxp: \0o <o (cnf_val x) by apply: OS_cnf_valp.
move: (proj43 (the_cnf_split cxp)).
rewrite /the_cnf_rem /odegree eqb (Y_false (nesym (proj2 cxp))) cxy => rxs.
have sd: cnf_degree x = cnf_degree y by rewrite cxy.
move:(OS_nat(proj1 lcxp)) (OS_nat (proj1 lcyp)) => olcx olcy.
move:(OS_prod2 ood olcx)(OS_prod2 ood olcy) => ofx ofy.
have ca: cnf_lc y <c cnf_lc x -> R x y.
  move => clc;split => h.
    by move: (cnf_lt_eq_deg yp xp (esym sd) clc)=> [qa]; case; apply: cnf_leA.
  have h': osucc (cnf_lc y) <=o cnf_lc x by apply/oleSltP; apply: oclt.
  have la: oopow d *o cnf_lc x <=o  cnf_val x. 
    rewrite eq2; apply: (osum_Mle0 ofx orx).
  have lb: cnf_val y <o oopow d *o (osucc (cnf_lc y)).
    rewrite eq1 (oprod2_succ ood olcy); apply: (osum_Meqlt rys ofy).
  by case: (oltNge (olt_leT lb (oleT  (oprod_Meqle h' ood) la)) h).
have cb: cnf_lc x <c cnf_lc y -> R x y.
  move => clc;split => _; last exact: (proj1 (cnf_lt_eq_deg xp yp sd clc)).
  have h': osucc (cnf_lc x) <=o cnf_lc y by apply/oleSltP; apply: oclt.
  have la: oopow d *o cnf_lc y <=o  cnf_val y. 
    rewrite eq1; apply: (osum_Mle0 ofy ory).
  have lb: cnf_val x <o oopow d *o (osucc (cnf_lc x)).
    rewrite eq2 (oprod2_succ ood olcx); apply: (osum_Meqlt rxs ofx).
  exact: (oleT (oleT (proj1 lb) (oprod_Meqle h' ood)) la).
case: (NleT_ell (proj1  lcxp) (proj1 lcyp)); [ | exact | exact ].
move => slc; clear ca cb.
set x' := (cnf_nr x (cnf_size x)).
set y' := (cnf_nr y (cnf_size y)).
have qa: (cnf_size x) <c (domain x) by rewrite sxv; apply : cltS.
have qb: (cnf_size y) <c (domain y) by rewrite syv; apply : cltS.
move: (cnfp_cnf_nr ox (proj1 qa)) (cnfp_cnf_nr oy (proj1 qb)) => rb rc.
have rg: cnf_val x' <=o cnf_val y' <-> cnf_val x <=o cnf_val y.
  rewrite eq1 eq2 /x' /y' - rxv - ryv - slc; split => ll.
    by apply:(osum_Meqle ll ofx).
  by apply: (osum_Meqler orx ory ofx).
apply: iff_trans rg. (*¨deplacer *)
clear ofx ofy rxs rys eqa eqb eq1 eq2 rxv ryv cxp cyp ovx ovy.
have dx': domain x' = cnf_size x by rewrite /x'/cnf_nr; aw.
have dy': domain y' = cnf_size y by rewrite /y'/cnf_nr; aw.
have cxy2 z: cnfp z -> z <> emptyset ->
  Vr (cnf_nr z (cnf_size z)) (cnf_degree z) = \0c
  /\ forall e, e <> (cnf_degree z) ->
    Vr (cnf_nr z (cnf_size z)) e = Vr z e.
  set z' := cnf_nr z (cnf_size z).
  move => oz znz.
  move: (cnf_size_nz (conj oz znz)) => [nN' szv].
  have qe: (cnf_size z) <c (domain z) by rewrite szv; apply : cltS.
  move: (cnfp_cnf_nr oz (proj1 qe)) => oz'.
  split.
    rewrite /Vr Vg_out_of_range // => /funI_P [t tr tv].
    move/(range_gP (proj41 oz')): tr; rewrite /cnf_nr; aw.
    move => [i idx ]; rewrite LgV // => xx.
    move/(NltP nN'): idx => ilx. 
    move/(NltP (proj42 oz)): (clt_ltT ilx qe) => idz.
    move/(NltP (proj42 oz)): qe => qz'.
    have eq:  oexp z (cnf_size z) = oexp z i by rewrite /oexp -xx.
    by case: (proj2 ilx);move: (cnf_monomial_inj oz qz' idz eq).
  move => e bed.
  case: (inc_or_not e (domain (range z'))) => er.
    move: er => /funI_P [t /(range_gP (proj41 oz')) [i idz ->] -> ].
    rewrite  (Vr_correct oz' idz).
    move: idz; rewrite /cnf_nr restr_d /ocoef => idz;  rewrite LgV//.
    rewrite -/(ocoef z i)- (Vr_correct) //.
    by apply/(NltP (proj42 oz)); apply: clt_ltT qe; apply/NltP.                   rewrite /Vr (Vg_out_of_range er) Vg_out_of_range  //.
  move /funI_P => [t /(range_gP (proj41 oz)) [i idz iv] tv ].
  move/(NltP (proj42 oz)): idz; rewrite szv; move/(cltSleP nN').
  case/cle_eqVlt; first by move => h; case: bed; rewrite tv iv h.
  move/(NltP nN') => idz.
  case: er; apply/funI_P; exists t => //; apply /(range_gP (proj41 oz')).
  aw; ex_tac; rewrite /cnf_nr LgV//.
have rh: x <=f y <-> x' <=f y'.
  have qc: inc (cnf_size x) (domain x) by apply/(NltP ox2).
  have qd: inc (cnf_size y) (domain y) by apply/(NltP oy2).
  have slm: Vg x (cnf_size x) = Vg y (cnf_size y).
    by apply: (pair_exten (ox3 _ qc) (oy3 _ qd)). 
  have H a b: a <c b -> b <> \0c.
    move => h; exact: (nesym (proj2 (cle_ltT (cle0x (proj31_1 h)) h))).
  have cx1:= (cnf_coef_of_lc (conj ox xnz)).
  have cy1:= (cnf_coef_of_lc (conj oy ynz)).
  move: (cxy2 _ ox xnz) (cxy2 _ oy ynz); rewrite -/x' -/y'.
  move=> [cx2 cx3] [cy2 cy3] .
  clear cxy2.
  split; move => [_ _ lrp]; split; [exact | exact | | exact | exact | ].
    case: lrp; first by  rewrite /x'/y' ; move ->; left.
    move => [e ea eb]; right.
    exists e. 
      move: ea; case:(equal_or_not e (cnf_degree x))=> h.
        by case/proj2;  rewrite  h - cx1 sd - cy1.
      by rewrite (cx3 e h) cy3 // - sd.
    move => j lee; move: (eb _ lee); case:(equal_or_not j (cnf_degree x))=> h.
      by rewrite h cx2 sd cy2.
    by rewrite (cx3 j h) cy3 // - sd.
  case: lrp => sv.
    have dd1: cnf_size x = cnf_size y by  rewrite - dx' - dy' sv.
    have dd: domain x = domain y by rewrite sxv syv dd1.
    left; apply:(fgraph_exten ox1 oy1 dd) => i /(NltP ox2).
    rewrite sxv => /(cltSleP nN); case/cle_eqVlt.
      by move ->;rewrite {2} dd1.
    move/(NltP nN)=> id1.
    by move: (f_equal (Vg ^~i) sv); rewrite /x'/y'/cnf_nr !LgV //  - dd1.
  move:sv => [e ea eb]; right.
  exists e.
    move: ea; case:(equal_or_not e (cnf_degree x))=> h.
      by case/proj2; rewrite h cx2  sd - cy2.
     by rewrite (cx3 e h) cy3 // - sd.
  move => j lee; move: (eb _ lee); case:(equal_or_not j (cnf_degree x))=> h.
    by move => _; rewrite h - cx1 sd - cy1.
  by rewrite (cx3 j h) cy3 // - sd.
apply:(iff_trans rh).
case: (equal_or_not x' emptyset) => xnz'; first by  rewrite xnz'; apply:R0y.
case: (equal_or_not y' emptyset) => ynz'; first by  rewrite ynz'; apply:Rx0.
have dx1 : deg x' <o d.
  rewrite /deg - cxy; Ytac0; rewrite /cnf_degree /oexp /x' /cnf_size restr_d.
  case: (equal_or_not (cnf_size x) \0c) => sz.
    by case: xnz'; apply/domain_set0_P; rewrite dx'.
  move: (cpred_pr nN sz) => [qN qv].
  have qe: inc (cpred (cnf_size x)) (cnf_size x).
      by rewrite {2} qv; apply:Nsucc_i.
  rewrite sxv (cpred_pr1 (CS_nat nN)) LgV//.
  by move: (proj44 (proj1 (proj44 ox)) _ qN); rewrite - qv; apply.
have dy1 : deg y' <o d.
  rewrite /deg - dyv; Ytac0; rewrite /cnf_degree /oexp /y' /cnf_size restr_d.
  case: (equal_or_not (cnf_size y) \0c) => sz.
    by case: ynz'; apply/domain_set0_P; rewrite dy'.
  move: (cpred_pr mN sz) => [qN qv].
  have qe: inc (cpred (cnf_size y)) (cnf_size y).
      by rewrite {2} qv; apply:Nsucc_i.
  rewrite syv (cpred_pr1 (CS_nat mN)) LgV//.
  by move: (proj44 (proj1 (proj44 oy)) _ qN); rewrite - qv; apply.
set d' := omax (deg x') (deg y').
have lta: d' <o d by rewrite /d'/omax/Gmax; Ytac w.
move: (omax_p1 (proj31_1 dx1) (proj31_1 dy1)) => [sa sb].
exact: (Hrec _  lta _ _ rb rc sa sb).
Qed.




Definition cnf_sum_monp x y d p :=
  [\/ inc p (range y) /\ P p <o d,
      inc p (range x) /\ d <o P p |
      p = J d ((Vr x d) +c (Vr y d))].

Definition cnf_sum_mons x y d :=
  Zo (range y) (fun p => P p <o d) \cup
  Zo (range x) (fun p => d <o P p) \cup
  singleton (J d  ((Vr x d) +c (Vr y d))).  

Lemma cnf_sum_monP x y d:
  (forall p, inc p (cnf_sum_mons x y d) <-> cnf_sum_monp x y d p).
Proof.
split.
  case/setU2_P.
    by case/setU2_P => /Zo_P [ha hb] ; [ constructor 1 |  constructor 2].
 by move => /set1_P; constructor 3.   
case => h.
- by apply: setU2_1; apply: setU2_1; apply/Zo_P.
- by apply: setU2_1; apply: setU2_2; apply/Zo_P.
- apply: setU2_2; rewrite - h; apply: set1_1.
Qed.


Lemma cnf_sum_mon_range x y  (d := (cnf_degree y)): cnfp x -> cnfp_nz y ->
   cnf_rangep (cnf_sum_mons x y d). 
Proof.
move => ox ynz; move: (proj1 ynz) => oy.
move /cnfpP:(ox)=> aox; move/cnfpP:(oy) => aoy.
move:(cnf_range_fgraph ox) => fgrx. 
move:(cnf_range_fgraph oy) => fgry.
move: (OS_cnf_degree ynz) => od.
have aux t:inc t (cnf_sum_mons x y d) -> omonomp t.
  case /cnf_sum_monP.
  + move: aoy => [ha hb hc _].
    by case =>/(range_gP ha) [i /hc ok -> xs].
  + move: aox => [ha hb hc _].
    by case =>/(range_gP ha) [i /hc ok -> xs].
  + rewrite /omonomp; move ->; aw; split; [ fprops | exact | ].
    move: (NS_Vr d ox) => ra.
    rewrite -(cnf_coef_of_lc ynz); apply:posnat_add (posnat_lc ynz).
    apply:(NS_Vr _ ox).
split; last exact.
  have H z P: cnfp z -> finite_set (Zo (range z) P).
    move => [ha hb _ _ ].
    apply: (sub_finite_set (@Zo_S (range z) P)); apply:(finite_range ha).
    by apply/NatP; rewrite card_nat.
  by apply:setU1_finite; apply:setU2_finite; apply:H.
split; first by  move => t /aux; case.
move => i j /cnf_sum_monP ip /cnf_sum_monP; case; case: ip.
  + by move => [ia _][ja _]; apply:(proj2 fgry).
  + by move => [_ lt1][_ lt2] sp; case: (proj2(olt_leT lt2 (proj1 lt1))).
  + by move => -> [_ /proj2 lt2]; aw => eq1; case:lt2.
  + by  move => [_ lt1][_ lt2] sp; case: (proj2 (olt_leT lt1 (proj1 lt2))).
  + by move => [ia _][ja _]; apply:(proj2 fgrx).
  + by move => -> [_ /proj2 lt2]; aw => eq1; case:lt2.
  + by move => [_ /proj2 lt1] ->; aw; move => eq2; case:lt1.
  + by move => [_ /proj2 lt1] ->; aw; move => eq2; case:lt1.
  + by move  <-.
Qed.

Definition cnf_sum x y :=
  Yo (y = \0f) x (cnf_sort (cnf_sum_mons x y (cnf_degree y))). 

Notation "x +f y" := (cnf_sum x y) (at level 50).

Definition cnf_sum_compat x y :=
  cnf_val (x +f y) = (cnf_val x) +o (cnf_val y).

Lemma cnf_sum0r x: x +f \0f  = x.
Proof. by rewrite /cnf_sum; Ytac0. Qed.

Lemma cnfp_sum x y: cnfp x -> cnfp y -> cnfp (x +f y).
Proof.
move => ha hb.
rewrite /cnf_sum; Ytac h => //.
exact: (proj1 (cnf_sort_correct (cnf_sum_mon_range ha (conj hb h)))).
Qed.

Lemma cnf_sum_range x y: cnfp x -> cnfp_nz y -> 
   range (x +f y) = cnf_sum_mons x y (cnf_degree y).
Proof.
move => ox ynz.
rewrite /cnf_sum (Y_false (proj2 ynz)).
by rewrite (proj2 (cnf_sort_correct (cnf_sum_mon_range ox ynz))).
Qed.

Lemma cnf_sum_rangeP x y:  cnfp x -> cnfp_nz y -> 
  forall t, inc t (range (x +f y)) <->  cnf_sum_monp x y (cnf_degree y) t.
Proof.
move => ox ynz; rewrite (cnf_sum_range ox ynz).
exact: (cnf_sum_monP x y (cnf_degree y)).
Qed.

Lemma cnf_sum_nz x y: cnfp x -> cnfp_nz y -> 
  x +f y <> \0f. 
Proof.
move => ox ynz sz.
move: (cnf_sum_range ox ynz); rewrite sz range_set0 /cnf_sum_mons.
move/esym /setU2_eq0P /proj2; set u := J _ _ => h.
by move:(set1_1 u); rewrite h => /in_set0.
Qed.
  

Lemma cnf_sum0l y: cnfp y -> \0f +f y = y.
Proof.
move => oy.
case: (equal_or_not y emptyset) => yz; first by rewrite /cnf_sum; Ytac0.
have ynz := (conj oy yz).
apply:(cnf_same_range (cnfp_sum cnfp0 oy) oy).
rewrite (cnf_sum_range cnfp0 ynz).
have ha := (cnf_size_nz_bis ynz).
set d := (cnf_degree y).
have eq1: J d (Vr C0 d +c Vr y d) = Vg y (cnf_size y).
  rewrite cnf_coef_or_e_zero - (cnf_coef_of_lc ynz).
  by rewrite (csum0l  (CS_nat (proj1 (posnat_lc ynz)))) (proj43 oy _ ha).
set_extens t.
  move/cnf_sum_monP; case.
  - by case.
  - by case; rewrite range_set0 => /in_set0.
  - rewrite eq1 => ->; apply: (inc_V_range (proj41 oy) ha).
move => tr; apply/ cnf_sum_monP.
move/(range_gP (proj41 oy)): (tr) => [i idy tv].
move: (cnf_size_nz ynz) => [hc hd].
move: idy; rewrite hd => /(NleP hc) => /cle_eqVlt; case.
  by move=> iv; constructor 3; rewrite eq1 - iv.
by move/(cnf_degree_greatest_bis oy); rewrite /oexp - tv => he; constructor 1.
Qed.

Lemma cnf_sum_small_deg x y: cnfp_nz  x ->  cnfp_nz y -> 
  cnf_degree x <o cnf_degree y -> 
  x +f y = y.
Proof.
move => xnz ynz cpd.
move: (proj1 xnz) (proj1 ynz) => ox oy.
apply:(cnf_same_range (cnfp_sum ox oy) oy).
rewrite (cnf_sum_range ox ynz).
have ha:=(cnf_size_nz_bis ynz).
set d := (cnf_degree y).
have hb i: inc i (domain x) -> oexp x i <o d.
  move => idx; exact: (ole_ltT (cnf_degree_greatest ox idx) cpd).
have eq1: J d (Vr x d +c Vr y d) = Vg y (cnf_size y).
  case: (inc_or_not d (domain (range x))).
    move=> /funI_P [t /(range_gP (proj41 ox)) [i ia ->] iv].
    by case:(proj2 (hb i ia)).
  move => h;rewrite {1}/Vr (Vg_out_of_range h). 
  rewrite - (cnf_coef_of_lc ynz).
  by rewrite (csum0l  (CS_nat (proj1 (posnat_lc ynz)))) (proj43 oy _ ha).
set_extens t.
  move/cnf_sum_monP; case.
  - by case.
  - move => [/ (range_gP (proj41 ox)) [i /hb /proj1 ok ->]].
    by move/oltNge; case.
  - rewrite eq1 => ->; apply: (inc_V_range (proj41 oy) ha).
move => tr; apply/cnf_sum_monP.
move/(range_gP (proj41 oy)): (tr) => [i idy tv].
move: (cnf_size_nz ynz) => [hc hd].
move: idy; rewrite hd => /(NleP hc) => /cle_eqVlt; case.
  by move=> iv; constructor 3; rewrite eq1 - iv.
by move/(cnf_degree_greatest_bis oy); rewrite /oexp - tv => he; constructor 1.
Qed.


Definition cnf_all_smaller x y :=
  forall i j,  i <c domain x -> j <c domain y -> oexp x i <o oexp y j.


Lemma cnf_nr_degree x k (v := cnf_val (cnf_nr x k)):
  cnfp x -> k <=c domain x -> k <> \0c ->
  \0o <o v /\ odegree v = oexp x (cpred k).
Proof.
move => ox kp1 kp2.
set y :=  (cnf_nr x k).
move:(NS_le_nat kp1 (proj42 ox)) => kN.
move: (cpred_pr kN kp2); set p := cpred k; move => [pN pv].
have ipkk: inc p k by rewrite pv; apply:Nsucc_i.
have ->: oexp x p = oexp y p by rewrite /y /cnf_nr/oexp LgV//.
have dy: domain y = csucc p by  rewrite /y/cnf_nr restr_d.
move: (proj44 (cnfp_cnf_nr ox kp1)); rewrite -/y dy => ax.
by move:(the_cnf_p5 pN ax); rewrite - dy.
Qed.


Lemma cnfp_cnf_ns x k: cnfp x -> k <=c domain x -> cnfp (cnf_ns x k). 
Proof.
move => /cnfpP [ha hb hc hd] lk; rewrite /cnf_ns; apply/cnfpP.
rewrite Lgd.
move:(NS_diff k hb); set m := _ -c _ => mN.
move: (NS_le_nat lk hb) => kN.
have H i:  i <c m -> i +c k <c domain x.
  by move/(csum_Mlteq kN); rewrite(csumC m)  (cdiff_pr lk). 
split.
- fprops.
- exact.
- by rewrite /cnf_s;move => i im; rewrite LgV//; apply: hc; apply/(NltP hb)/H /(NltP mN).
- rewrite/cnf_s/oexp;move => i iN idx.
  move/(NltP mN):(idx)=> idx1.
  move/(NltP mN):(clt_ltT (cltS iN) idx) => ik.
  rewrite !LgV// (csum_Sn _ iN); apply:(hd _ (NS_sum iN kN)). 
  by rewrite -(csum_Sn _ iN); apply: H; apply/(NltP mN).
Qed.


Lemma cnf_all_smaller_prop x y: cnfp x -> cnfp y -> 
  [\/ x = emptyset, y = emptyset | (cnf_degree x) <o (oexp y \0c) ] ->
  cnf_all_smaller x y.
Proof.
rewrite/cnf_all_smaller;move => ox oy; case.
-  by move ->; rewrite domain_set0 => i j /clt0.
-  by move ->; rewrite domain_set0 => i j _ /clt0.
- move => h1 i j /(NltP (proj42 ox)) idx jdy.
  apply: (olt_leT (ole_ltT (cnf_degree_greatest ox idx) h1)).
  apply: (CNF_exponents_M (proj42 oy) (proj1 (proj44 oy)) _ jdy).
  exact:(cle0x (proj31_1 jdy)).
Qed.

Lemma cnfp_cnf_nm x y: cnfp x -> cnfp y -> cnf_all_smaller x y ->
  cnfp (cnf_nm x y). 
Proof.
move => /cnfpP [ha hb hc hd] /cnfpP [ha' hb' hc' hd'] aux.
rewrite /cnf_nm /cnf_m; apply/cnfpP.
rewrite Lgd; move:(NS_sum hb hb'); set m := _ +c _ => mN.
have Hp i: i <c m -> domain x <=c i -> i -c domain x <c domain y.
  move => lt1 le2;  apply: (cdiff_Mlt hb' (NS_lt_nat lt1 mN) le2).
  by rewrite csumC.
split.
- fprops.
- exact.
- move => i lim; rewrite LgV//; move /(NltP mN):lim=>  lim.
  case: (cleT_el (CS_nat hb) (proj31_1 lim)) => cp1.
    by rewrite(Y_false (cleNgt cp1)); apply: hc'; apply/(NltP hb'); apply: Hp.
  by Ytac0; apply: hc; apply/NltP.
rewrite/oexp; move => i iN idx.
move/(NltP mN):(idx)=> idx1.
move/(NltP mN):(clt_ltT (cltS iN) idx) => ik.
have ii := (cltS iN).
rewrite !LgV//.
case: (NleT_el hb (NS_succ iN)) => cp1; last first.
  by rewrite(Y_true (clt_ltT ii cp1)); Ytac0; apply: (hd _ iN cp1).
rewrite (Y_false (cleNgt cp1)); case/cle_eqVlt: cp1 => cp2.
  rewrite cp2 (Y_true ii) cdiff_nn; apply: aux; first by rewrite cp2.
  apply/(strict_pos_P1 hb') => dyz.
  by move:(proj2 idx); rewrite /m dyz cp2 (csum0r (CS_succ _)).
move/(cltSleP iN): cp2 => cp2; rewrite (Y_false (cleNgt cp2)).
move: (Hp _ idx (cleT cp2 (proj1 ii)));rewrite (cdiffSn iN cp2) => cp3.
exact: (hd' _ (NS_diff (domain x) iN) cp3).
Qed.


Lemma cnfp_cnf_nm_range x y: cnfp x -> cnfp y -> 
  range (cnf_nm x y) = (range x) \cup (range y).
Proof.
move => ha hb.
set z := (cnf_nm x y).
have fgz: fgraph z by rewrite /z/cnf_nm; fprops.
have dz: domain z = domain x +c domain y by  rewrite /z/cnf_nm; aw.
move:(ha)(hb) =>[fgx nN _ _ ][fgy mN _ _].
have nmN := NS_sum nN mN.
set_extens t.
  move/(range_gP fgz) =>[i]; rewrite dz => lis->; move/(NltP nmN):(lis) => lid.
  rewrite /z/cnf_nm/cnf_m LgV//.
  case: (cleT_el (CS_nat nN) (proj31_1 lid)) => cp1.
    rewrite (Y_false (cleNgt cp1)); apply: setU2_2;apply: (inc_V_range fgy).
     apply/(NltP mN); apply:(cdiff_Mlt mN (NS_lt_nat lid nmN) cp1).
    by rewrite csumC.
  by Ytac0; apply: setU2_1; apply: (inc_V_range fgx); apply/NltP.
move => h; apply/(range_gP fgz); rewrite dz.
rewrite /z/cnf_nm/cnf_m.
case/setU2_P: h.
  move/(range_gP fgx)  => [i /(NltP nN) idx ->].
  have idd:  inc i (domain x +c domain y).
    apply/(NltP nmN); apply: (clt_leT idx); apply:(csum_M0le _ (CS_nat nN)).
  by ex_tac; rewrite LgV//; Ytac0.
move/(range_gP fgy)  => [i /(NltP mN) idx ->].
have sd: inc (i +c (domain x)) (domain x +c domain y).
  by apply/(NltP nmN); rewrite csumC; apply:(csum_Meqlt nN idx).
move:(cleNgt(csum_M0le i (CS_nat nN))); rewrite csumC => ll.
by ex_tac; rewrite LgV//; Ytac0; rewrite (cdiff_pr1 (NS_lt_nat idx mN) nN).
Qed.


Lemma cnf_nm_sum x y: cnfp x -> cnfp y -> 
  cnf_all_smaller x y ->
  (cnf_nm x y) =  y +f x.
Proof.
move => ox oy cpd.
move: (cnfp_cnf_nm ox oy cpd) => oz.
apply: (cnf_same_range oz (cnfp_sum oy ox)).
rewrite (cnfp_cnf_nm_range ox oy).
case: (equal_or_not x emptyset) => xz.
  by rewrite /cnf_sum xz range_set0 (Y_true (erefl _)) setU2_C setU2_0.
have xnz := conj ox xz.
move: (ox) => [fgx nN _ _].
move: (oy) => [fgy mN _ _].
move: (cnf_size_nz xnz) => [qa qb].
have sxdx:= (cnf_size_nz_bis xnz).
move/(NltP nN): (sxdx) => sxix.
have prop1: Vr y (cnf_degree x) = \0c.
  apply:Vg_out_of_range; move/funI_P => [z /(range_gP fgy) [i idy ->]] .
  move/(NltP mN): idy => pb.
  exact:(proj2 (cpd (cnf_size x) i sxix pb)).
have prop2: Vg x (cnf_size x) =
   J (cnf_degree x)
     (Vr y (cnf_degree x) +c Vr x (cnf_degree x)).
  rewrite - (proj43 ox _ sxdx); apply: f_equal.
  rewrite prop1  - (cnf_coef_of_lc xnz) csum0l //.
  exact:(CS_nat (proj1 (posnat_lc xnz))).
set_extens t.
  move => tp; apply/(cnf_sum_rangeP oy  xnz).
  case/setU2_P:tp => trx.
     move/(range_gP fgx): (trx) => [i idx mv].
     move/(NltP nN): idx; rewrite qb; move/(cltSleP qa).
     case/cle_eqVlt => ha; first by constructor 3; rewrite mv ha. 
     constructor 1; split; first  exact.
     by rewrite mv;exact:(cnf_degree_greatest_bis ox ha).
  constructor 2; split; first exact.
  move/(range_gP fgy): (trx) => [i idx ->]; apply: (cpd _ _ sxix).
  by apply/NltP.
case/(cnf_sum_rangeP oy xnz).
- by move => [ha _]; apply:setU2_1.
- by move => [ha _]; apply:setU2_2.
- by rewrite - prop2 => ->; apply:setU2_1; apply: inc_V_range.
Qed.

  
Lemma cnfp_cnf_mergeK x k :  cnfp x -> k <=c domain x ->
  cnf_nm (cnf_nr x k) (cnf_ns x k) = x.
Proof.
move => ox le1.
rewrite /cnf_nm/cnf_m.
have ->: domain (cnf_nr x k) = k by rewrite /cnf_nr Lgd.
have ->: domain (cnf_ns x k) = (domain x -c k) by rewrite /cnf_ns Lgd.
symmetry;rewrite (cdiff_pr le1).
move: (ox) => [fgx nN _ _]; apply: fgraph_exten; [ exact | fprops | by aw | ].
move => i /= idx; rewrite (LgV idx); move/(NltP nN): idx => idx.
case: (cleT_el (proj31 le1) (proj31_1 idx)) => cp1.
  have aux: inc (i -c k) (domain x -c k).
    by apply/(NltP (NS_diff k nN));apply:cdiff_pr7.
  rewrite (Y_false (cleNgt cp1)) /cnf_ns/cnf_s LgV//.
  by rewrite csumC (cdiff_pr cp1).
by Ytac0; rewrite /cnf_nr LgV//; apply/(NltP (NS_le_nat le1 nN)).
Qed.

Lemma cnf_sum_prop1 x y: cnfp x -> cnfp y -> 
  cnf_val (cnf_nm x y) = (cnf_val y) +o (cnf_val x).
Proof.
move => ox oy.
have nN := proj42 ox.
have mN := proj42 oy.
have nmN := (NS_sum nN mN).
rewrite /cnf_val /CNFbvo /CNFbv /cnf_nm Lgd.
set A := cantor_mon _ _ _.
set B := cantor_mon _ _ _.
set C := cantor_mon _ _ _.
have propA t: t <c domain y ->  A (t +c domain x) = B t. 
  move => tdy; rewrite /A/B/cantor_mon /oexp/ocoef.
  move:(NS_lt_nat tdy mN) => tN.
  have qc:inc (t +c domain x) (domain x +c domain y).
    by apply/(NltP nmN ); rewrite csumC; apply:csum_Meqlt.
  move:(cleNgt(csum_Mle0 t (CS_nat nN))) => qd.
  by rewrite LgV// /cnf_m (Y_false qd) (cdiff_pr1 tN nN). 
have propB t : t <c domain x  -> A t = C t.
  move => tdy; rewrite /A/C/cantor_mon/oexp/ocoef/cnf_m.
  have qc: inc t (domain x +c domain y).
    apply/(NltP nmN); apply: (clt_leT tdy).
    apply:(csum_M0le _ (CS_nat nN)).
  by rewrite LgV//; Ytac0.
have propC: ord_below A (domain x +c domain y).
  move => t ts.
  move:(NS_lt_nat ts nmN) => tN.
  case: (NleT_el nN tN).
    move => le1; move: (cdiff_pr le1); set j := _ -c _ => ea.
    have jdx: j <c domain y. 
      by apply:cdiff_Mlt => //; rewrite csumC.
    rewrite - ea csumC (propA _ jdx).
    exact:(CNFq_p0  (proj1 (proj44 oy)) jdx).
  move => tdx; rewrite (propB _ tdx).
  exact:(CNFq_p0  (proj1 (proj44 ox)) tdx).
rewrite (osum_fA nN mN propC).
apply: f_equal2.
  by apply: (osumf_exten mN) => t tn /=; apply: propA.
by apply: (osumf_exten nN) => t tn /=;apply: propB.
Qed.
  
Lemma cnf_sum_prop2 x y: cnfp x -> cnfp y -> 
  cnf_all_smaller x y ->
  cnf_sum_compat y x.
Proof.
move => ha hb hc;
by rewrite /cnf_sum_compat - (cnf_nm_sum ha hb hc) (cnf_sum_prop1 ha hb).
Qed.

Lemma cnf_sum_prop3 x k :  cnfp x -> k <=c domain x ->
  cnf_val (cnf_ns x k) +o cnf_val(cnf_nr x k) = cnf_val x.
Proof.
move => ha hb.
move: (cnfp_cnf_nr  ha hb) => hc.
move: (cnfp_cnf_ns  ha hb) => hd.
by rewrite - {3} (cnfp_cnf_mergeK ha hb) - (cnf_sum_prop1 hc hd).
Qed.


Lemma cnf_sum_rec x: cnfp_nz x ->
 cnf_val x = cnf_val (cnf_ns x \1c) +o (oopow (oexp x \0c)) *o (ocoef x \0c).
Proof.
move => xnz.
have od1:= proj2(cnf_size_nz_ter xnz). 
move: (proj44 (proj1 xnz)) => [[_ qb qc _] _].
move: (OS_oopow (qb _ od1))(proj31_1 (qc _ od1))=> ra rb.
have odx: \1c <=c (domain x) by apply/cge1P.
rewrite -(cnf_sum_prop3 (proj1 xnz) odx).
rewrite {2}/cnf_val /cnf_nr restr_d /CNFbvo /CNFbv.
set u := cantor_mon _ _ _.
have eq1: u \0c = oopow (oexp x \0c) *o ocoef x \0c.
   rewrite/u/cantor_mon/ocoef/oexp LgV//; apply: set1_1.
by rewrite osum_f1 eq1 //; apply: OS_prod2.
Qed.


Lemma cnf_sum_prop4 x k
      (x1 := cnf_val (cnf_nr x k)) (x2 := cnf_val (cnf_ns x (csucc k)))
      (x3 := oopow (oexp x k) *o (ocoef x k)):
  cnfp x ->  k <c (domain x) ->
  [/\ ordinalp x1, ordinalp x2, ordinalp x3 &
  cnf_val x = x2 +o (x3 +o x1) ].
Proof.
move => ox lkd; rewrite /x1 /x2/x3.
move:(NS_lt_nat lkd (proj42 ox)) => kN.
have ha: csucc k <=c domain x by apply/cleSltP.
split.
- apply: (OS_cnf_val (cnfp_cnf_nr ox (proj1 lkd))).
- apply:(OS_cnf_val (cnfp_cnf_ns ox ha)).
-  exact:(CNFq_p0 (proj1 (proj44 ox)) lkd).
- rewrite -(cnf_sum_prop3 ox ha); apply: f_equal.
  rewrite /cnf_val /cnf_nr restr_d /CNFbvo /CNFbv (osum_fS _ kN) restr_d.
  apply: f_equal2.
    by rewrite/cantor_mon/oexp/ocoef LgV//; apply:Nsucc_i.
  apply: (osumf_exten kN) => i ilk.
  move/(NltP kN): (ilk) => is1.
  move:(proj33 (proj1 (cltS kN)) _ is1) => is2.
  by rewrite /cantor_mon/oexp/ocoef !LgV.
Qed.

Definition cnf_nc y c :=
  Lg (domain y) (cnf_c (Vg y) (cnf_size y) (J (cnf_degree y) (c +c cnf_lc y))).

Lemma cnf_nc_prop y c (z :=  cnf_nc y c) :
   cnfp_nz y  -> natp c ->
   [/\ cnfp z, domain z = domain y,
    forall i, i<c domain y -> oexp z i = oexp y i,
    forall i, i<c cnf_size y -> Vg z i = Vg y i &
    cnf_lc z = c +c cnf_lc  y].
Proof.
move => ynz; move/cnfpP:(proj1 ynz) => [fgx nN qa qb] cN.
have eq1: domain z = domain y by rewrite /z/cnf_nc; aw.
have eq2: cnf_size z = cnf_size y by rewrite /cnf_size eq1.
move: (cnf_size_nz_bis ynz) => ha.
move: (cnf_size_nz ynz) => [dN dv].
have ->:cnf_lc z = c +c cnf_lc y.
  by rewrite {1}/cnf_lc eq2 /z/cnf_nc/cnf_c /ocoef/cnf_size LgV//; Ytac0; aw.
have aux i: i <c cnf_size y -> Vg z i = Vg y i.
  rewrite /z/cnf_nc => ils; rewrite LgV //. 
    by rewrite /cnf_c (Y_false (proj2 ils)).
  move /(NltP nN): ha => sd.
  by apply/(NltP nN); apply: (clt_ltT ils sd).
have eq3:forall i, i<c domain y -> oexp z i = oexp y i.
  move => i; rewrite dv/oexp ; move/(cltSleP dN).
  case/cle_eqVlt => cpa; last by  rewrite aux.
  by rewrite cpa /z/cnf_nc/cnf_c LgV//;Ytac0; aw.
split => //.
apply/cnfpP; split.
- rewrite /z/cnf_nc; fprops.
- by rewrite eq1.
- move => i; rewrite eq1 => idy.
  move /(NltP nN): (idy); rewrite dv; move/(cltSleP dN).
  case/cle_eqVlt => cpa; last by  rewrite (aux _ cpa); apply: qa.
  rewrite cpa /z /cnf_nc /cnf_c LgV//; Ytac0; split; aww.
    by apply: OS_cnf_degree.
  by apply:(posnat_add cN); case:(qa _ ha).
- move => i iN;rewrite eq1 => lin.
  by rewrite (eq3 _ (clt_ltT (cltS iN) lin)) (eq3 _ lin); apply: qb.
Qed.

Definition cnf_ncms x y k :=
  cnf_nm (cnf_nc y (ocoef x k)) (cnf_ns x (csucc k)).

Lemma cnf_ncms_prop x y k:
  cnfp x -> cnfp_nz y -> k <c (domain x) -> 
  oexp x k = cnf_degree y ->
  x +f y = cnf_ncms x y k.
Proof.
move =>ox ynz lkn dv.
move:(proj1 ynz) => oy.
move: (cnfp_sum ox oy)=> oz1.
have nN := proj42 ox.
have mN := proj42 oy.
set c := ocoef x k.
move:(NS_lt_nat lkn nN) => kN.
move/(cleSltP kN):(lkn) => leskn.
move:(cnf_size_nz ynz)(cnf_size_nz_bis ynz).
set sy := cnf_size y; move => [dyN dyv] dyl1.
have sdy: sy <c (domain y) by apply/(NltP mN).
have cN: natp c.
   move/(NltP nN): lkn => kdx.
   move/cnfpP: ox => /proj43 =>h; exact: (proj1 (proj33 (h _ kdx))).
move: (cnf_nc_prop ynz cN) => [os1 qb qc qd qe].
have eq2: cnf_degree  (cnf_nc y c) = cnf_degree y.
  by rewrite/cnf_degree /cnf_size qb qc.
have os2:= (cnfp_cnf_ns ox leskn).
have lt1: cnf_all_smaller (cnf_nc y c) (cnf_ns x (csucc k)).
   apply:(cnf_all_smaller_prop os1 os2).
   case: (equal_or_not (csucc k) (domain x)) => lt1.
     by constructor 2; rewrite /cnf_ns lt1 cdiff_nn /Lg funI_set0.
   have qq: csucc k <c domain x by split.
   have qa: inc \0c (domain x -c csucc k).
     apply/(NltP (NS_diff (csucc k) nN)); apply:card_ne0_pos; fprops.
     by apply: cdiff_nz.
   constructor 3.
   rewrite /cnf_ns /cnf_s/oexp LgV // (csum0l (CS_succ _)) eq2 - dv.
   by apply: (CNF_exponents_sM nN (proj1 (proj44 ox)) (cltS kN) qq).
apply: (cnf_same_range (cnfp_sum ox (proj1 ynz))  (cnfp_cnf_nm  os1 os2 lt1)).
rewrite (cnfp_cnf_nm_range os1 os2).
have Hu: fgraph (cnf_nc y c) by rewrite /cnf_nc; fprops.
have eq3:
   Vg (cnf_nc y c) sy =
   J (cnf_degree y)
     (Vr x (cnf_degree y) +c Vr y (cnf_degree y)).
   move/(NltP nN): lkn => kdx.
   rewrite - (cnf_coef_of_lc ynz).
   rewrite -{2} dv (Vr_correct ox kdx).
   by rewrite /cnf_nc /cnf_c/sy LgV//; Ytac0.
move:(NS_diff (csucc k) nN) => dkN.
set_extens t.
  move => /(cnf_sum_rangeP ox ynz) => h; apply/setU2_P; case:h.
  - move => [ta tle]; left.
    move: tle;move/(range_gP (proj41 oy)):ta => [i idy ->] tl2.
    apply/(range_gP (proj41 os1)); rewrite qb; ex_tac; rewrite qd //.
    split; first by apply/(cltSleP dyN); rewrite - dyv; apply/(NltP mN).
    by move => ne1; case: (proj2 tl2); rewrite ne1.
  - move => [ty tle]; right.
    move: tle; rewrite - dv.
    move/(range_gP (proj41 ox)): ty => [i idx ->] => lt2.
    move:(NS_inc_nat nN idx) => iN.
    case: (NleT_el iN kN) => lik.
       case:(oleNgt (CNF_exponents_M nN (proj1 (proj44 ox)) lik lkn) lt2).
    move/(cleSltP kN): lik => lik.
    move/(NltP nN): idx => idx.
    have ii: inc (i -c (csucc k)) (domain x -c csucc k).
      apply/(NltP dkN); apply: (cdiff_pr7 lik idx nN).
    apply/(range_gP (proj41 os2)); rewrite /cnf_ns/cnf_s Lgd.
    by ex_tac; rewrite LgV //csumC cdiff_pr.
  - move ->; left; rewrite - eq3; apply: (inc_V_range (proj41 os1)).
    by rewrite qb.
move=> h; apply/(cnf_sum_rangeP ox ynz).
case/setU2_P: h.
  move/(range_gP Hu) => [i idx ->].
  move: idx; rewrite qb => idy.
  move/(NltP mN): (idy); rewrite dyv; move/(cltSleP dyN).
  case/cle_eqVlt => cisy.
    constructor 3; rewrite cisy; apply:eq3.
  move:(CNF_exponents_sM mN (proj1 (proj44 oy)) cisy sdy) => hv.
  constructor 1. rewrite (qd _ cisy);split => //.
  by apply: (inc_V_range (proj41 oy)).
move/(range_gP (proj41 os2)) => [i].
rewrite /cnf_ns Lgd => lid;rewrite LgV ///cnf_s => ->.
move/(NltP dkN):lid => lt2.
move:(csum_Meqlt (NS_succ kN) lt2); rewrite (cdiff_pr leskn) csumC => l1.
constructor 2; split.
  by apply:(inc_V_range (proj41 ox)); apply/NltP.
rewrite - dv; apply:(CNF_exponents_sM nN (proj1 (proj44 ox)) _ l1).
rewrite (csum_nS _ kN); apply/(cltSleP (NS_sum (NS_lt_nat lt2 dkN) kN)).
apply: (csum_Mle0 _ (CS_nat kN)).
Qed.

Lemma cnf_ncms_prop_sd x y :
  cnfp_nz x -> cnfp_nz y -> 
  cnf_degree x = cnf_degree y ->
  x +f y = cnf_nc y (cnf_lc x).
Proof.
move => xnz ynz sd.
have ox := proj1 xnz.
move: (cnf_size_nz xnz) => [mN mv].
move/(NltP (proj42 ox)):(cnf_size_nz_bis xnz) => mk.
rewrite (cnf_ncms_prop ox ynz mk sd) /cnf_ncms -/(cnf_lc x) - mv.
have ->: (cnf_ns x (domain x))  = emptyset.
  rewrite /cnf_ns cdiff_nn; apply: funI_set0.
have cN:= (proj1 (posnat_lc xnz)).
move: (cnf_nc_prop ynz cN).
set u := cnf_nc _ _; move => [pa pn pc pd pe].
have dd1: domain u +c emptyset = domain u.
  by  rewrite (csum0r (CS_nat (proj42 pa))).
have sdd: domain (cnf_nm u emptyset) = domain u by  rewrite /cnf_nm Lgd; aw.
apply: fgraph_exten.
- rewrite /cnf_nm; fprops.
- exact (proj41 pa).
- exact.
- rewrite  sdd => i idu; rewrite /cnf_nm domain_set0 dd1 LgV//.
  by rewrite /cnf_m Y_true //; apply/(NltP (proj42 pa)).
Qed.

Lemma cnf_sd_lc x y :
  cnfp_nz x -> cnfp_nz y ->
  cnf_degree x = cnf_degree y ->
  cnf_lc(x +f y) = (cnf_lc x) +c cnf_lc y. 
Proof.
move => xnz ynz sd.
rewrite(cnf_ncms_prop_sd xnz ynz sd).
have cN:= (proj1 (posnat_lc xnz)).
by move: ( (cnf_nc_prop ynz cN)) =>[_ _ _ _].
Qed.

Lemma cnf_sum_prop6 x c: cnfp_nz x -> natp c ->
   cnf_val (cnf_nc x c) = oopow (cnf_degree x) *o c +o (cnf_val x).
Proof.
move => xnz cN.
move:(cnf_nc_prop xnz cN); set z := cnf_nc _ _.
move => [oz dz zexp zg zlc].
move:(cnf_size_nz  xnz)(cnf_size_nz_bis xnz).
set m := cnf_size x; move => [mN dxv] hh.
have co: c <o omega0  by apply olt_omegaP.
move:(proj44 (proj1 xnz));rewrite /cnf_val dxv => axo.
move: (CNFb_change_nv mN axo co) => [ha <-].
rewrite dz - dxv; apply: (osumf_exten (proj42 (proj1 xnz))) => i ilx.
move/(NltP (proj42 (proj1 xnz))): (ilx) => idx. 
rewrite /cantor_mon (zexp _ ilx) /z/cnf_nc /ocoef/cnf_c LgV//; apply: f_equal.
by Ytac h; Ytac0; aw; trivial;rewrite (osum2_2int cN (proj1 (posnat_lc  xnz))).
Qed.


Lemma ord_negl_p9 x y k: 
   cnfp x -> cnfp_nz y -> k <=c (domain x) -> 
   (forall i, i <c k -> oexp x i <o cnf_degree y) ->
   cnf_val (cnf_nr x k) <<o cnf_val y.
Proof.
move => ox ynz lkd hd.
move:(cnf_size_nz ynz)(cnf_size_nz_bis  ynz).
set m := cnf_size x; move => [mN dyv] hh.
have ovy := (OS_cnf_val (proj1 ynz)).
have kN: natp k by apply:NS_le_nat lkd (proj42 ox).
case: (equal_or_not k \0c) => knz.
  rewrite /ord_negl.
  by rewrite /cnf_nr knz {1} /cnf_val /CNFbvo/CNFbv restr_d osum_f0 osum0l.
move: (cnf_nr_degree ox lkd knz) => [up ud].
move: (proj44 (proj1 ynz));  rewrite dyv => ay.
move: (the_cnf_p5 mN ay); rewrite - dyv -/(cnf_val _); move =>[yp ddy].
apply: (ord_negl_p7 up yp); rewrite {1} ud ddy -/(cnf_degree y).
apply: (hd _ (cpred_lt kN knz)).
Qed.
  
                                     
Lemma cnf_sum_prop7  x y k:
  cnfp x -> cnfp_nz y -> k <c (domain x) -> 
  oexp x k = cnf_degree y ->
  cnf_sum_compat x y.
Proof.
move => ox ynz lkd hk.
move/(cnfpP): (ox) => ox'.
move: (NS_lt_nat lkd (proj42 ox)) => kN.
move/(cleSltP kN): (lkd) => lk1.
have ox2:= cnfp_cnf_ns ox lk1.
move/(NltP (proj42 ox)): (lkd) => kdx.
move:(proj1 (proj33 (proj43 ox' _ kdx))) => cN.
move: (cnf_nc_prop ynz cN) => [oy1 _ _ _ _].
have ovy := (OS_cnf_val (proj1 ynz)).
rewrite /cnf_sum_compat  (cnf_ncms_prop ox ynz lkd hk).
rewrite (cnf_sum_prop1 oy1 ox2).
move: (cnf_sum_prop4 ox lkd) => [ow ou ov ->].
rewrite - (osumA  ou (OS_sum2 ov ow) ovy).
apply: f_equal.
rewrite  (cnf_sum_prop6 ynz cN).
move: ov; rewrite hk;  move => ov.
rewrite - (osumA ov ow ovy); apply: f_equal.
move:(cnf_size_nz ynz)(cnf_size_nz_bis ynz).
set m := cnf_size x; move => [mN dyv] hh.
symmetry. apply: (ord_negl_p9 ox ynz (proj1 lkd)).
move => i lik; rewrite - hk.
apply:(CNF_exponents_sM (proj42 ox) (proj1 (proj44 ox)) lik lkd).
Qed.  

Definition position_in_cnf x d :=
  intersection ((Zo (domain x) (fun i => d <=o oexp x i)) +s1 (domain x)).

Lemma position_in_cnf_prop x d (k :=  position_in_cnf x d):
  cnfp x -> ordinalp d ->
  [/\ k <=c domain x,
      forall i, i <c k -> oexp x i <o d &
      k = domain x \/ d <=o oexp x k].
Proof.
move => ox od; rewrite /k/ position_in_cnf; clear k.
set n := domain x; set E := Zo _ _.
have nN:= proj42 ox.
have Eb: forall t, inc t (E +s1 n) -> t <=c n.
  move => t /setU1_P; case;first by  move/Zo_S /(NltP nN) /proj1.
  move => ->; apply: (cleR (CS_nat nN)).
have ha: sub (E +s1 n) Nat by move => y /Eb lyn; apply: (NS_le_nat lyn nN).
have hb: nonempty (E +s1 n) by exists n; fprops.
move: (inf_Nat ha hb); set k := intersection _;move => [ kE hd].
move:(Eb _ kE)(ha _ kE) => lekn kN.
split => //; last by case/setU1_P: kE => h; [ right; move/Zo_hi: h |  left].
move => t ltk; 
have td: inc t (domain x) by apply/(NltP nN); apply: (clt_leT ltk lekn).
have oe: ordinalp (oexp x t).
    by move/cnfpP: ox => /proj43 h; case: (h _ td).
case: (oleT_el od oe) => h //.
have /hd/cleNgt []//: inc t (E +s1 n) by apply:setU1_r; apply:Zo_i.
Qed.

Lemma cnf_sum_prop8 x y (d := cnf_degree y) (k := position_in_cnf x d):
  cnfp x -> cnfp_nz y -> 
  x +f y = cnf_sum (cnf_ns x k) y.
Proof.
move => ox ynz.
move: (OS_cnf_degree ynz); rewrite -/d => od.
move: (position_in_cnf_prop ox od); rewrite -/k.
move => [kdx kp1 kp2].
move: (cnfp_cnf_ns ox kdx) => oz.
have nN := proj42 ox.
have kN := NS_le_nat kdx nN.
have aux: Vr (cnf_ns x k) d =  Vr x d.
  case: (inc_or_not d (domain (range x))) => ddrx.
    move/funI_P:ddrx => [t tx tv]; move/(range_gP (proj41 ox)):tx =>[i idx iv].
    have dv: d = oexp x i by rewrite tv iv.
    rewrite {2} dv  (Vr_correct ox idx).
    move/(NltP nN): (idx) => iix.
    move: (NS_inc_nat nN idx) => iN.
    case: (NleT_el kN iN) => lik; last by case:(proj2 (kp1 _ lik));ue.
    have sidx:  inc (i -c k) (domain x -c k).
      by apply/(NltP (NS_diff k nN));  apply: cdiff_pr7.
    have idz: inc (i -c k)  (domain  (cnf_ns x k)) by rewrite/cnf_ns Lgd.
    move:(Vr_correct oz idz).
    rewrite {2 3} /cnf_ns/cnf_s /oexp /ocoef LgV//.
    by rewrite (csumC _ k) (cdiff_pr lik) dv.
  rewrite /Vr (Vg_out_of_range ddrx).  
  case: (inc_or_not d (domain (range (cnf_ns x k)))) => hu; last first.
    by rewrite (Vg_out_of_range hu).  
  move/funI_P:hu => [t tx tv]; move/(range_gP (proj41 oz)):tx =>[i].
  rewrite /cnf_ns Lgd => idx; rewrite LgV// => iv.
  case: ddrx; rewrite tv iv /cnf_s; apply /funI_P.
  exists ((Vg x (i +c k))) => //; apply: (inc_V_range (proj41 ox)).
  apply/(NltP nN).
  move/(NltP (NS_diff k nN)): idx => lik.
  by move:(csum_Meqlt kN lik); rewrite (cdiff_pr kdx) csumC.
apply: (cnf_same_range (cnfp_sum ox (proj1 ynz))  (cnfp_sum oz (proj1 ynz))).
set_extens t.
  move/(cnf_sum_rangeP ox ynz) => h; apply/(cnf_sum_rangeP oz ynz).
  case: h.
  - by constructor 1.
  - move => [ha hb]; constructor 2; split => //.
    apply/(range_gP (proj41 oz)).
    move/(range_gP (proj41 ox)): ha =>[i idx iv].
    move:hb; rewrite iv => hb.
    move/(NltP nN): (idx) => iix.
    move: (NS_inc_nat nN idx) => iN.
    case: (NleT_el kN iN) => lik; last by move:(oltNge hb (proj1(kp1 _ lik))).
    have sidx:  inc (i -c k) (domain x -c k).
      by apply/(NltP (NS_diff k nN));  apply: cdiff_pr7.
    by rewrite /cnf_ns Lgd; ex_tac; rewrite LgV// /cnf_s csumC cdiff_pr.
  - move => tv; constructor 3; rewrite tv aux; reflexivity.
move/(cnf_sum_rangeP oz ynz) => h; apply/(cnf_sum_rangeP ox ynz).
case: h.
- by constructor 1.
- move =>[ha hb]; constructor 2; split => //.
  move/(range_gP (proj41 oz)): ha =>[i].
  rewrite /cnf_ns /cnf_s Lgd => idx; rewrite LgV//; move ->.
  apply: (inc_V_range (proj41 ox)); apply/(NltP nN).
  move/(NltP (NS_diff k nN)): idx => lik.
  by move:(csum_Meqlt kN lik); rewrite (cdiff_pr kdx) csumC.
- move => tv; constructor 3; rewrite tv aux; reflexivity.
Qed.

Lemma cnf_sum_prop9 x y (d := cnf_degree y) (k := position_in_cnf x d):
  cnfp x -> cnfp_nz y ->  ~(inc d (domain (range x))) ->
  x +f y = cnf_nm y (cnf_ns x k).
Proof.
move => ox ynz dd.
have oy := proj1 ynz.
move: (OS_cnf_degree ynz); rewrite -/d => od.
move: (position_in_cnf_prop ox od); rewrite -/k.
move => [kdx kp1 kp2].
move: (cnfp_cnf_ns ox kdx) => oz.
rewrite  (cnf_sum_prop8 ox ynz) -/k; symmetry; apply: (cnf_nm_sum oy oz).
move => i j /(NltP (proj42 oy)) idy jdz.
apply:(ole_ltT (cnf_degree_greatest oy idy)); rewrite -/d.
move: jdz;rewrite /cnf_ns/cnf_s Lgd /oexp => jl1.
have nN := proj42 ox.
case: (cle_eqVlt kdx) => ckn.
  by move: jl1; rewrite - ckn cdiff_nn => /clt0.
move/(NltP (NS_diff k nN)): (jl1) => jdz; rewrite LgV//.
case: kp2; first by  move=> kv; case: (proj2 ckn).
move/ole_eqVlt; case => cd.
  case:dd; apply/funI_P; rewrite cd; exists (Vg x k) => //.
  by apply:(inc_V_range (proj41 ox)); apply/NltP.
have le1: k <=c j +c k by apply:(csum_Mle0 _ (proj31_1  ckn)).
have le2:  j +c k <c domain x.
  by move:(csum_Meqlt (NS_lt_nat ckn nN) jl1); rewrite (cdiff_pr  kdx) csumC.
apply(olt_leT cd).
exact: (CNF_exponents_M (proj42 ox) (proj1 (proj44 ox)) le1 le2). 
Qed.

Lemma cnf_sum_prop10 x y:  cnfp x -> cnfp_nz y  ->
  ~(inc (cnf_degree y) (domain (range x))) ->
  cnf_sum_compat x y.
Proof.
move => ox ynz hd.
rewrite/cnf_sum_compat (cnf_sum_prop9 ox ynz hd). 
move: (OS_cnf_degree ynz) => od.
move: (position_in_cnf_prop ox od) =>[kdx kp1 kp2].
move:(cnfp_cnf_ns ox kdx) (cnfp_cnf_nr ox kdx) => ox1 ox2.
rewrite (cnf_sum_prop1 (proj1 ynz) ox1) - (cnf_sum_prop3 ox kdx).
rewrite - (osumA (OS_cnf_val ox1) (OS_cnf_val ox2) (OS_cnf_val (proj1 ynz))).
apply: f_equal.
symmetry; apply: (ord_negl_p9 ox ynz kdx kp1).
Qed.

Lemma position_in_cnf_prop2 x i:
  cnfp x -> inc i (domain x) ->  position_in_cnf x (oexp x i) = i.
Proof.
move=> ox pb.
move/cnfpP: (ox) => /proj43 h; move: (proj32 (h _ pb)) => od.
move: (position_in_cnf_prop ox od); set k :=  position_in_cnf _ _.
move => [ka kb kc].
have nN:= (proj42 ox).
move/(NltP nN): pb => idx.
move:(NS_lt_nat idx nN) => iN.
case: (cleT_ell (proj31 ka) (CS_nat iN)); [exact | |  by move/kb; case].
move => lik.
case: kc; first by move => ea; case:(proj2 (clt_ltT lik idx)).
case/oleNgt.
exact: (CNF_exponents_sM (proj42 ox) (proj1 (proj44 ox)) lik idx).
Qed.

Lemma cnf_sum_compat_prop x y: cnfp x -> cnfp y -> cnf_sum_compat x y.
Proof.
move => ox oy.
have oox := OS_cnf_val ox.
case: (equal_or_not y emptyset) => ynz.
  by rewrite /cnf_sum_compat ynz cnf_sum0r cnf_val0 (osum0r oox).
case: (inc_or_not (cnf_degree y)(domain  (range x))).
  move/funI_P => [p /(range_gP (proj41 ox)) [k kdx kv] pv].
  move/(NltP (proj42 ox)): (kdx) => lkx.
  have hu: oexp x k = cnf_degree y by rewrite pv/oexp - kv.
  exact: (cnf_sum_prop7 ox (conj oy ynz) lkx hu).
exact: cnf_sum_prop10.
Qed.


Lemma cnf_osum x y: ordinalp x -> ordinalp y ->
  the_cnf (x +o y) = the_cnf x +f the_cnf y.
Proof.
move => ox oy.
move: (the_cnf_p0 ox)(the_cnf_p0 oy); set a := the_cnf x; set b := the_cnf y.
move => [oa av][ob bv].
move: (cnf_sum_compat_prop oa ob).
rewrite /cnf_sum_compat av bv. move <-.
exact: (proj43 (cnf_and_val_pb (cnfp_sum oa ob))).
Qed.


  
Lemma cnf_sumA x y z: cnfp x -> cnfp y -> cnfp z ->
  x +f (y +f z) = (x +f y) +f z.
Proof.
move => ox oy oz.
move: (cnfp_sum oy oz) (cnfp_sum ox oy) => oyz oxy.
apply: (cnf_val_inj (cnfp_sum ox oyz) (cnfp_sum oxy oz)).
rewrite (cnf_sum_compat_prop ox oyz) (cnf_sum_compat_prop oxy oz).
rewrite (cnf_sum_compat_prop oy oz)(cnf_sum_compat_prop ox oy).
exact: (osumA (OS_cnf_val ox)(OS_cnf_val oy)(OS_cnf_val oz)).
Qed.

Lemma odegree_sum a b: ordinalp a -> ordinalp b ->
  odegree (a +o b) = omax (odegree a) (odegree b).
Proof.
move => oa ob.
have deg0: odegree \0o = \0c by rewrite /odegree; Ytac0.
case: (equal_or_not a \0o) => ap.
  by rewrite ap (osum0l ob)  deg0 (omax_xy (ole0x (OS_degree ob))).
case: (equal_or_not b \0o) => bp.
  by rewrite bp (osum0r oa) deg0 (omax_yx (ole0x (OS_degree oa))).
case: (equal_or_not (a +o b) \0o) => abp.
   by case: (osum2_zero oa ob abp).
move: (the_cnf_p0 oa); set x := the_cnf a; move => [ox xv].
move: (the_cnf_p0 ob); set y := the_cnf b; move => [oy yv].
rewrite /odegree (Y_false ap) (Y_false bp) (Y_false abp)  -/x -/y.
rewrite (cnf_osum oa ob) -/x -/y. 
have xz: x <> emptyset by move => xz; case: ap; rewrite -xv xz cnf_val0.
have yz: y <> emptyset by move => yz; case: bp; rewrite -yv yz cnf_val0.
move: (conj ox xz) (conj oy yz) => xnz ynz.
move: (OS_cnf_degree xnz)(OS_cnf_degree ynz) => edx edy.
case: (oleT_el edy edx) => ltd; last first.
  by rewrite (cnf_sum_small_deg xnz ynz ltd) (omax_xy (proj1 ltd)).
rewrite (omax_yx ltd).
symmetry; set d1 := cnf_degree x.
have eq0:= (cnf_sum_range ox ynz).
have os:= (conj (cnfp_sum ox oy) (cnf_sum_nz ox ynz)).
have H := cnf_sum_rangeP ox ynz.
apply: oleA.
  suff : exists2 p, inc p (range (cnf_sum x y))  & P p = d1.
     move => [p  /(range_gP (proj41 (proj1 os))) [i idr iv] pv].
     by move:(cnf_degree_greatest (proj1 os) idr); rewrite /oexp - iv pv.
  have Hb := (inc_V_range (proj41 ox) (cnf_size_nz_bis xnz)).
  case: (equal_or_not (cnf_degree y) d1) => eq1.
    exists (J d1 ((Vr x d1) +c (Vr y d1))); aw; trivial.
    by rewrite - eq1; apply /H; constructor 3.
  by exists (Vg x (cnf_size x)) => //; apply/H; constructor 2.
move:(inc_V_range (proj41 (proj1 os)) (cnf_size_nz_bis os)).
rewrite /cnf_degree/oexp;case /H.
- move => [/(range_gP (proj41 oy)) [i idy ->] hv].
  by move:(oleT (cnf_degree_greatest oy idy) ltd).
- move => [/(range_gP (proj41 ox)) [i idx ->] hv].
  exact:(cnf_degree_greatest ox idx).
- by move ->; aw.
Qed.

Lemma ord_negl_p7_bis x y: \0o <o x -> \0o <o y ->
  (odegree x <o odegree y <-> x <<o y).
Proof.
move => xp yp; split; first by apply:ord_negl_p7.
move:(the_cnf_p0_nz xp)(the_cnf_p0_nz yp).
set a := the_cnf x; set b := the_cnf y.
move => [anz av][bnz bv].
move: xp yp => [/proj32 ox /nesym xz][/proj32 oy /nesym yz] xy.
move:(cnf_osum ox oy); rewrite xy -/a -/b => eq1.
move: (odegree_sum ox oy); rewrite xy. 
case:(oleT_el (OS_degree oy) (OS_degree ox)) => // le1.
rewrite (omax_yx le1) => dxdy.
have sd: cnf_degree a = cnf_degree b.
  by move: dxdy; rewrite /odegree -/a -/b; Ytac0; Ytac0.
move:(cnf_sd_lc  anz bnz sd); rewrite - eq1.
move:(posnat_lc anz)(posnat_lc bnz) =>[qa qb][qc qd] => eq2.
by move:(proj2 (csum_M0lt qc (nesym(proj2 qb)))); rewrite csumC - eq2.
Qed.

Lemma cnf_valuation_sum_spec x y: cnfp x -> cnfp y -> domain y = \1c ->
   oexp (x +f y) \0c = oexp y \0c.
Proof.
move => ox oy dy1.
have sy: cnf_size y = \0c by rewrite /cnf_size dy1 cpred1.
set d := oexp y \0c.
have dd: d = cnf_degree y by rewrite/cnf_degree sy.
have ynz: cnfp_nz y.
  split => //;move => yz; move: dy1; rewrite yz  domain_set0; fprops.
have xynz :  x +f y <> emptyset by apply: cnf_sum_nz.
move:(cnfp_sum ox oy) => os.
have H := cnf_sum_rangeP ox ynz.
have zdd: inc \0c (domain (x +f y)).
  apply/(NltP (proj42 os)); apply: (card_ne0_pos (CS_nat (proj42 os))).
  by move/domain_set0_P.
apply: oleA.
  set t :=  J d (Vr x d +c Vr y d).
  have: inc t (range (x +f y)) by rewrite /t dd; apply/H; constructor 3.
  move=> /(range_gP (proj41 os)) [i idx iv].
  move/(NltP (proj42 os)): idx => ily.
  move: (cle0x (proj31_1 ily)) => i0.
  move:(CNF_exponents_M (proj42 os)  (proj1 (proj44 os)) i0 ily).
  by rewrite /oexp - iv /t pr1_pair.
move:(inc_V_range (proj41 os) zdd); rewrite /oexp; set u := Vg _ _.
case /H.
-  move => [/(range_gP (proj41 oy)) [i idy idv]/oltNge  pv].
  move/(NltP (proj42 oy)): idy => ily.
  move: (cle0x (proj31_1 ily)) => i0.
  case: pv; rewrite idv - dd.
  exact(CNF_exponents_M (proj42 oy)  (proj1 (proj44 oy)) i0 ily).
- by move => [_ /proj1]; rewrite dd.
- by move ->; rewrite pr1_pair dd; apply: oleR; apply: OS_cnf_degree.
Qed.

Lemma ovaluation_4a x e c: ordinalp x -> ordinalp e -> posnatp c ->
    ovaluation (x +o (oopow e) *o c ) = e.
Proof.
move => ox oe cp.
move: (cnf_one_term oe cp) =>[]; set b := Lg _ _; set y := _ *o _.
move => ob oy pa pb.
move: (the_cnf_p0 ox); set a := the_cnf x; move => [oa vv].
have hu: oexp b \0c = e.
  by rewrite /b/oexp LgV//; aw; trivial;exact: (set1_1 \0c).
have db: domain b = \1c by rewrite /b Lgd.
by rewrite /ovaluation (cnf_osum ox oy) -/a pa cnf_valuation_sum_spec.
Qed.

Lemma ovaluation4 y e: ordinalp y -> ordinalp e ->
  ovaluation (y +o oopow e) = e.
Proof.
move => oy oe.
by move:( ovaluation_4a oy oe PN1); rewrite (oprod1r (OS_oopow oe)).
Qed.
  
Lemma ovaluation_sum a b: ordinalp a -> \0o <o b ->
  ovaluation (a +o b) = ovaluation b.
Proof.
move => oa bp.
move: (ovaluation1 bp) => [c oc ->].
move:(OS_valuation bp) => ov.
rewrite (osumA oa oc (OS_oopow ov)).
by rewrite  (ovaluation4  (OS_sum2 oa oc) ov) (ovaluation4 oc ov).
Qed.

End Ordinals3a.
Export Ordinals3a.
