
(*  bourbalki aux  
$Id: ssete8.v,v 1.2 2018/07/13 12:58:25 grimm Exp $
*)


Set Warnings "-notation-overridden".
From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq  choice fintype.
From mathcomp
Require Import binomial  bigop ssralg poly ssrint.

Require Import ssete7.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* The next lemma uses F38, which follows from F36. 
However F37 is an easy consequence of F36, and we have the trivial
Lemma F37bis p p q:
  \sum_(k<q.+1) 'C(p+q,k) * 'C(p+q,p+k) = 'C((p+q).*2,q).
Proof. by move: (F37 (leq_addr q p)); rewrite addKn mul2n. Qed.
*)

Lemma F37bis p q:
  \sum_(k<q.+1) 'C(p+q,k) * 'C(p+q,p+k) = 'C((p+q).*2,q).
Proof.
pose f p q := \sum_(k<q.+1) 'C(p+q,k) * 'C(p+q,p+k).
pose g p q := 'C((p + q).*2, q).
rewrite -/(f p q) - /(g p q); move: p q.
have fp0: forall p, f p 0 = 1.
  by move => p; rewrite /f big_ord_recl big_ord0 binn bin0.
have gp0: forall p, f p 0 = g p 0.
  by move => p; rewrite /g bin0 fp0.
have fp1: forall p, f p 1 = (p.+1).*2.
  move => m; rewrite /f big_ord_recl big_ord_recl big_ord0 binn bin0.
  rewrite mul1n muln1 addn0 /=  /bump /= addn0 addn0.
  have r1: m = (m + 1) - 1 by rewrite addn1 subn1 -pred_Sn.
  rewrite {2} r1 -addnn addn1 bin_sub // bin1 //. 
have gp1: forall p, f p 1 = g p 1.
  by move => p; rewrite /g bin1 fp1 addn1.
have f0q: forall q, f 0 q = 'C(q.*2,q).
  move=> q; rewrite /f add0n -F38; apply: congr_big => // [[i isn]].
have g0a: forall q, f 0 q = g 0 q.
  by move => q; rewrite /g f0q.
have gp2: forall p q, g p.+1 q.+2 = g p q.+2  + ( g p.+1 q.+1).*2 +  g p.+2 q.
  move => p q; rewrite /g.
  have ->: (p.+1 + q.+2).*2 = (p.+1 + q.+1).*2.+2.
  by rewrite -doubleS; congr (double _); rewrite addnS.
  rewrite binS binS -addnA -addnA addSnnS; congr (_ + _).
  rewrite -[in X in _ = X + _] addnn -addnA; congr (_ + _).
  by rewrite binS addSnnS addSnnS.
suff fp2: forall p q, f p.+1 q.+2= f p q.+2 + (f p.+1 q.+1).*2 + f p.+2 q.
  pose aux q:= forall p, f p q = g p q.
  have aux2: forall q, aux q /\ aux q.+1.
    elim => [// | n [hr1 hr2]]; split => //.
    by elim => // => p hrec; rewrite gp2 fp2 hr1 hr2 hrec.
  move => p q; move: p. move: (aux2 q) => [] //.
move=> p q.
rewrite /f.
rewrite 4! addSn  2! addnS; set n:= (p+q).+2.
set t0 := \sum_ (k < q.+3) _; set t1 := \sum_ (k < q.+3) _. 
set t2 := \sum_ (k < q.+2) _; set t3 := \sum_ (k < q.+1) _.
rewrite /t0 big_ord_recl bin0 mul1n /ord0 addn0 binS.
set t4 := \sum_(i < q.+2) _.
have : t4 = \sum_(i < q.+2) (
    ('C(n, i.+1) * 'C(n.+1, (p+i).+2)) + ('C(n,i)) * 'C(n.+1, (p+i).+2)).
  rewrite /t4; apply: congr_big => // [[i lin]] _ /=.
  by rewrite /bump /= add1n addSn addnS binS mulnDl.
rewrite big_split /=.
set t5:=  \sum_(i < q.+2) _; set t6 :=  \sum_(i < q.+2) _; move => r1.
have: t5 = \sum_(i < q.+2) (('C(n, i.+1) * 
  'C(n, (p + i).+2)) + ( 'C(n, i.+1) *  'C(n, (p + i).+1))).
  rewrite /t5;apply: congr_big => // [[i lin]] _ /=.
  by rewrite binS mulnDr.
have : t6 = \sum_(i < q.+2) (('C(n, i) * 
  'C(n, (p + i).+2)) + ( 'C(n, i) *  'C(n, (p + i).+1))).
  rewrite /t5;apply: congr_big => // [[i lin]] _ /=.
  by rewrite binS mulnDr.
rewrite big_split /= big_split /=.
set t7:=  \sum_(i < q.+2) _; set t8:=  \sum_(i < q.+2) _.
set t9:=  \sum_(i < q.+2) _; set t10:=  \sum_(i < q.+2) _. 
have -> : t8 = t2.
  rewrite /t2 /t8; apply: congr_big => // [[i lin]] _ /=.
have ->: t7 = t3. 
  rewrite /t3 /t7; rewrite big_ord_recr /=.
  rewrite addnS -/n (bin_small (ltnSn n)) muln0 addn0.
  apply: congr_big => // [[i lin]] _ /=.
rewrite r1 => -> ->.
rewrite - [in X in _ = X] addnA (addnC t9) -(addnA t10).
rewrite addnCA (addnC ('C(n, p.+1))) -(addnA 'C(n, p)) addnA; congr ( _ + _).
  rewrite addnC /t1 big_ord_recl bin0 mul1n addn0; congr (_ + _).
  rewrite /t10; apply: congr_big => // [[i lin]] _ /=.
  by rewrite /bump /= add1n addnS.
rewrite addnA - addnn - (addnA t2) (addnC t3); congr ( _ + _).
rewrite /t9 / t2 big_ord_recr /=.
rewrite addnS -/n (bin_small (ltnSn n)) muln0 addn0.
symmetry; rewrite big_ord_recl bin0 mul1n addn0; congr (_ + _).
apply: congr_big => // [[i lin]] _ /=.
by rewrite /bump /= add1n addnS.
Qed.



Module Zformulas.

Import GRing.Theory.

Local Open Scope ring_scope.

Notation with_sign k x := ( (-1%:Z) ^+ k  *+  x ).
Notation with_sgn k x := ( (-1) ^+ k  *  x ).


Lemma F26a (k n: nat): 
  \sum_(i<k.+1) ( with_sign i 'C(n.+1, i)) = with_sign k 'C(n, k).
Proof.
move: k; elim; first by rewrite big_ord_recl /= big_ord0 ! bin0  addr0. 
move => k Hrec; rewrite big_ord_recr /= Hrec exprS - mulrnAr ! mulN1r.
by rewrite (binS n k) -opprB - mulrnBr ? addnK ? mulNrn // leq_addl.
Qed.

Lemma F26b (n: nat): 
  \sum_(i<n.+2) ( with_sign i 'C(n.+1, i)) = 0.
Proof. by rewrite - (exprD1n (-1%:Z) (n.+1)) subrr exprS mul0r. Qed.


Lemma bin_inva (j q: nat):
  \sum_(k<q.+1) with_sign k ('C(j+q, j+k) * 'C(j+k, j)) =  (q==0%N).
Proof.
case q; first by rewrite big_ord_recl /= big_ord0 !addn0 binn muln1 expr0 addr0.
move => n.
set A := \sum_(k < _) _.
have ->: A = \sum_(k < n.+2) (-1) ^+ k *+ 'C(n.+1,  k) *+ 'C(j + n.+1, j).
  by apply: eq_bigr => //; move => i _ /=; rewrite - mulrnA binom_exchange1.
by rewrite sumrMnl F26a bin_small // mulr0n mul0rn.
Qed.

Lemma bin_invb (j q: nat): j <= q ->
  \sum_(k<q.+1) with_sign k ('C(q, k) * 'C(k, j)) = 
    with_sgn j (Posz(q - j == 0)%N).
Proof.
move => h.
rewrite -  [in X in (X = _)] (subnKC h)  - addnS big_split_ord /=.  
rewrite big1 ? add0r; last by move => [i lin] _; rewrite (bin_small lin) muln0.
rewrite - (bin_inva j (q-j)) big_distrr /=; apply: eq_bigr.
by move => [i len] _ /=; rewrite mulrnAr  exprD.
Qed.

Lemma double_pow_m1 (i: nat) (a : int): with_sgn i (with_sgn i a) = a.
Proof. by rewrite mulrA -exprD -signr_odd addnn odd_double expr0 mul1r. Qed.


Definition bin_conv_dir (g: nat -> int) n :=
  \sum_(i<n.+1) (g i) *+ 'C(n,i).
Definition bin_conv_inv (f: nat -> int) n :=
 with_sgn n (\sum_(i<n.+1)  with_sgn i  (f i) *+ 'C(n,i)).


Lemma bin_conv_inv1 (f: nat -> int) n:
  bin_conv_inv f n = \sum_(i<n.+1) with_sgn i (f (n- i)%N) *+ 'C(n,i).
Proof.
rewrite /bin_conv_inv big_distrr /=.
rewrite - (big_mkord xpredT (fun i => with_sgn i (f (n- i)%N) *+ 'C(n,i))).
rewrite big_nat_rev /= big_mkord; apply: eq_bigr; move => [i] /=.
rewrite ltnS => lin _.
rewrite add0n  subnS subSKn bin_sub // subKn // mulrnAr mulrA.
congr (_ * _  *+ _).
by rewrite -(signr_odd _ (n-i)) -exprD (oddB lin) - oddD signr_odd.
Qed.


Lemma bin_conv_inv2 (f g: nat -> int) n:
  (forall i, i<=n -> f i = bin_conv_dir g i) ->
  (forall i, i<=n -> g i = bin_conv_inv f i).
Proof.
move => h. 
have h1:forall i m, m <=n -> i <= m ->  f i = \sum_(j<m.+1) (g j) *+ 'C(i,j).
  move => i m lemn leim; rewrite (h _ (leq_trans leim lemn)).
  rewrite - ltnS in leim; rewrite -  (subnKC leim) big_split_ord /=.
  rewrite - (addr0 (bin_conv_dir g i)); congr (_ + _); rewrite big1 //.
  by move => [k kn] _ /=; rewrite  bin_small // leq_addr.
move => i lein; rewrite /bin_conv_inv.
have ->: \sum_(i0 < i.+1) with_sgn i0 (f i0) *+ 'C(i, i0) =
  \sum_(k < i.+1) (\sum_(j<i.+1) (g j) * ((-1) ^+ k *+ ('C(i,k) * 'C(k, j)))).
  apply: eq_bigr ; move => [k lk] _ /=. 
  transitivity  (\sum_(j<i.+1) (g j) * (-1) ^+ k *+ 'C(k, j) *+ 'C(i,k)).
    rewrite sumrMnl; congr (_ *+ _).
    rewrite (h1 k i lein) // big_distrr /=; apply:  eq_bigr => j _.
    by rewrite mulrnAr mulrC.
  by apply:  eq_bigr => j _; rewrite - ! mulrnAr - !mulrnA mulnC.
rewrite exchange_big /= big_ord_recr /= big1.
  rewrite add0r - big_distrr /= (bin_invb (leqnn i)) subnn mulr1. 
  by rewrite (mulrC (g i)) double_pow_m1.
move => [j ji] _ /=; rewrite - big_distrr /=  (bin_invb (ltnW ji)).
by rewrite - (subnSK ji) ! mulr0.
Qed.

Lemma bin_conv_inv3 (f g: nat -> int) n:
  (forall i, i<=n -> f i = bin_conv_inv g i) ->
  (forall i, i<=n -> g i = bin_conv_dir f i).
Proof.
move => H.
pose g' i := with_sgn i (g i); pose f' i := with_sgn i (f i).
have H': forall i, i <= n -> f' i = bin_conv_dir g' i.
  by move => i lin; rewrite /f' (H _ lin)  /g' double_pow_m1.
move =>  i lin; move: (bin_conv_inv2 H' lin);rewrite /g' /bin_conv_inv => h.
move: (f_equal (fun z =>  (-1) ^+ i *z) h);rewrite !double_pow_m1.
by move => ->; apply : eq_bigr => j _; rewrite /f' double_pow_m1.
Qed.

Lemma bin_conv_inv_rec (f g: nat -> int) n:
  (forall i, i<=n.+1 -> g i = bin_conv_inv f i) ->
  (g n) + (g n.+1) =  bin_conv_inv (fun i => (f i.+1)) n.
Proof.
move => h.
rewrite addrC  (h _ (ltnSn n))  (h _ (leqnSn n)) !bin_conv_inv1 {h}.
rewrite  big_ord_recl [X in _ = X]  big_ord_recl /= - addrA !subn0 ! bin0. 
rewrite [X in _ + (X + _) = _]
  (_:_ = \sum_(i < n.+1) with_sgn i.+1 (f (n.+1 -  i.+1)%N) *+ 'C(n, i.+1)
    - \sum_(i < n.+1) with_sgn i (f (n - i)%N) *+ 'C(n, i)). 
 rewrite addrAC addrK; congr (_ + _).
  rewrite  big_ord_recr /= (bin_small (ltnSn n)) mulr0n addr0.
  apply: eq_bigr; move=> [i  lin] _ /=; rewrite subSn //.
rewrite -sumrB /=;  apply: eq_bigr; move=> [i  lin] _ /=.
rewrite -mulNrn - mulNr exprS mulN1r - mulrnDr //.
Qed.

Definition nb_surj n p := bin_conv_inv  (fun i => (i ^n)%N) p.

Lemma nb_surj_00 : nb_surj 0 0 = 1.
Proof.
rewrite /nb_surj /bin_conv_inv big_ord_recr /= big_ord0.
rewrite add0r double_pow_m1 //. 
Qed.

Lemma nb_surj_n0  n: nb_surj n.+1 0 = 0.
Proof.
rewrite /nb_surj /bin_conv_inv big_ord_recr /= big_ord0.
rewrite add0r double_pow_m1 exp0n //.
Qed.

Lemma nb_surj_0p p: nb_surj 0 p.+1 = 0.
Proof.
rewrite /nb_surj /bin_conv_inv; set s := \sum_(i< _) _.
suff: s = 0 by move => ->; apply: mulr0.
transitivity (\sum_(i < p.+2) (-1%:Z) ^+ i *+ 'C(p.+1, i)).
  by apply :eq_bigr => i _; rewrite expn0 mulr1.
rewrite F26a bin_small //. 
Qed.

Lemma nb_surj_n1  n: nb_surj n.+1 1 = 1.
Proof.
rewrite /nb_surj /bin_conv_inv big_ord_recr /= big_ord_recr /= big_ord0.
rewrite bin0 binn exp1n exp0n //.
Qed.

Lemma nb_surj_n2 n: nb_surj n.+1 2 = (2 ^n.+1 - 2)%N.
Proof.
rewrite /nb_surj /bin_conv_inv  ! big_ord_recr /= big_ord0.
rewrite exp0n // mulr0 mul0rn !add0r exp1n binn bin1 - signr_odd /= expr0 expr1.
rewrite ! mul1r mulr1n mulr1 addrC.
have s2: 2 <= (2 ^ n.+1) by  rewrite - {1} (expn1 2); apply: leq_pexp2l.
by rewrite -{1} (subnK s2) PoszD - addrA addrN addr0.
Qed.

Lemma nb_surj_1p p: nb_surj 1 p.+2 = 0.
Proof.
set g : ( nat -> int) := fun i =>  (if i ==1 then 1 else 0)%N.
pose f := bin_conv_dir g.
have aux: forall i, f i = i.
  move => i; rewrite /f /g /bin_conv_dir.
  rewrite big_ord_recl /= mul0rn add0r.
  case: i; first by  rewrite big_ord0.
  move => i; rewrite big_ord_recl /= bin1  big1 ? addr0.
    by rewrite - (intz i.+1) pmulrn. 
  by move => [j lji] _  /=; rewrite mul0rn.
transitivity (bin_conv_inv f p.+2).
  congr (_ * _); apply: eq_bigr => i _; rewrite aux //.
have H: (forall i, i<=p.+2 -> f i = bin_conv_dir g i) by move => i ip.
rewrite - (bin_conv_inv2 H) ?(leqnn p.+2) /g //=.   
Qed.

Lemma nb_surj_rec n p: 
   nb_surj n.+1 p.+1 = (nb_surj n p + nb_surj n p.+1) *+ (p.+1).
Proof.
set f: (nat -> int ):= (fun i : nat => (i ^ n)%N).
rewrite (bin_conv_inv_rec (f:=f)) // /bin_conv_inv -mulrnAr - sumrMnl. 
rewrite /nb_surj /bin_conv_inv /=.
have ->: (\sum_(i < p.+1) (-1) ^+ i * f i.+1 *+ 'C(p, i) *+ p.+1)
   = (\sum_(i < p.+1)  (-1) ^+ i * ((i.+1) ^(n.+1))%N%:Z *+ 'C(p.+1, i.+1)).
  apply:eq_bigr => i /= _; rewrite /f expnS mulnC PoszM  mulrA - mulrnA.
  rewrite mulnC mul_bin_diag  mulrnA; congr ( _ *+ _).
  by rewrite pmulrn - mulrzr intz.
rewrite exprSr - mulrA big_distrr /= big_ord_recl /= exp0n //(_: Posz 0 = 0) //.
rewrite mulr0 add0r; congr ( _ * _); apply: eq_bigr => i _ /=.
by rewrite mulrnAr mulrA  exprS mulN1r  mulN1r opprK.
Qed.


Lemma nbsurj_stirling n p: nb_surj n p = nbsurj n p.
Proof.
move: n p; elim. 
  case => //; first by rewrite  nb_surj_00 nbsurj00.
  by move => p; rewrite nb_surj_0p nbsurj0n.  
move => n H [|p]; first by rewrite nb_surj_n0 nbsurjn0.
by rewrite nb_surj_rec nbsurjS addnC H H - PoszD mulnC pmulrn mulrzz.
Qed.

Lemma nb_surj_small n p: nb_surj n (n+p.+1) = 0.
Proof.
move: p; elim: n; first by move => p; rewrite add0n nb_surj_0p. 
by move => n Hrec p; rewrite addSn nb_surj_rec Hrec -addnS Hrec // addr0 mul0rn.
Qed.

Lemma nb_surj_nn n: nb_surj n n = n`!.
Proof.
elim:n; first by rewrite  nb_surj_00.
move => n Hrec; rewrite  nb_surj_rec - {1} addn1 nb_surj_small addr0 Hrec //.
rewrite factS mulnC PoszM pmulrn - mulrzr intz //.
Qed.

Lemma nb_surj_Snn n: nb_surj n.+1 n = ('C(n.+1,2) * n`!) %N.
Proof.
elim:n; first by rewrite  nb_surj_n0 bin_small //. 
move => n Hrec; rewrite nb_surj_rec Hrec nb_surj_nn.
rewrite pmulrn - mulrzr intz - PoszD - PoszM (binS (n.+1)) bin1 mulnDl. 
by rewrite - mulnA 2! (mulnC _ n.+1) - factS - mulnDl.
Qed.

Lemma nb_surj_SSnn n: nb_surj n.+2 n = (('C(n.+3,4) + 2 * 'C(n.+2,4)) * n`!) %N.
Proof.
elim:n; first by  rewrite  nb_surj_n0  bin_small //. 
move => n Hrec; rewrite nb_surj_rec Hrec nb_surj_Snn.
rewrite pmulrn - mulrzr intz - PoszD - PoszM  mulnDl - mulnA.
rewrite 2! (mulnC _ n.+1)  - factS  mulnA - mulnDl -addnA. 
rewrite (binS (n.+3)) - addnA;congr( Posz ((_ + _) * _)).
rewrite (binS (n.+2) 3) mulnDr addnA (addnC 'C(n.+3, 3)) (binS (n.+2)).
rewrite - addnA (addnC _ 'C(n.+2, 2)) -addnA (mulSn n);congr(addn _ (addn _ _)).
by rewrite - (addn2 n) (mul_Sm_binm_1 n 2) - {1}(addn2 1)  mulnDl mul1n.
Qed.


End Zformulas.

Import GRing.Theory.
Open Scope ring_scope.


Section RingFormulas.

Variable R : ringType.
Implicit Types (x y : R) (n: nat).


Lemma shorten_sum (f: nat -> R) (n m : nat):
    (n <= m)%N -> (forall i, (n <= i < m)%N -> f i = 0) ->
  \sum_(i < m) f i = \sum_(i < n) f i.
Proof.
move => nm fz.
rewrite - (big_mkord xpredT) (big_cat_nat _ _ _ (leq0n n) nm) /= big_mkord.
rewrite  [X in ( _ + X)]big1_seq ? Monoid.mulm1 // => i; case /andP => _.
by rewrite mem_index_iota; apply: fz.
Qed.

(* f1  *)
Lemma F1 x y n: (\sum_(i<n.+1) (x+y*+ i))*+2  = (x*+2+y*+n)*+n.+1.
Proof.
elim: n; first by rewrite big_ord_recl big_ord0 mulr1n mulr0n !addr0.
move => n Hrec.
rewrite  big_ord_recr /= mulrnDl Hrec mulrnDl - !mulrnA mulrnDl - !mulrnA.
rewrite addrAC addrA - mulrnDr - addrA -mulrnDr mulrnDl - !mulrnA -(addn1 n.+1).
congr ((x  *+ _)  + (y *+ _)).
  rewrite  mulnDr //. 
rewrite mulnC - mulnDl add2n addn1 mulnC//. 
Qed.

End RingFormulas.


Section  RingPoly.
Variable R : ringType.

Local Open Scope ring_scope.

Lemma power_monom (c:R) n :
  ('X + c%:P) ^+ n = \poly_(i< n.+1) (c^+(n - i)%N *+ 'C(n, i)).
Proof.
rewrite addrC exprDn_comm ?poly_def; last by apply: commr_polyX.
apply: eq_big=> // [[i lin]] _ /=.
by rewrite - mul_polyC - polyC_exp polyC_muln  mulrnAl.
Qed.

(* is size_XaddC 
Lemma size_factorp (a: R) : size ('X + a%:P) = 2%N.
Proof. by rewrite -['X]mul1r  -cons_poly_def polyseq_cons polyseq1. Qed.
*)

Lemma sum_powers_of_x (n: nat) (x:R):
  (x-1) * (\sum_(i < n) x^+ i) = x ^+ n -1.
Proof.
elim: n => [| n Ihn]. 
  by rewrite big_ord0 expr0 mulr0 subrr.
rewrite  (big_ord_recr n) /= mulrDr Ihn  mulrBl mul1r -exprS.
by rewrite addrAC addrCA subrr addr0.
Qed.


End RingPoly.


Section PolyFormulas.


Lemma intmul_inj: injective(fun z:nat => (@intmul int_Ring 1%Z z)).
Proof. by move=> a b /=; rewrite !intz =>  sf; injection sf. Qed.

Lemma bin_vandermonde (k l i:nat): 
  (\sum_(j < i.+1) ('C(k, j)  *'C(l, (i - j))))%N = 'C(k+l , i)%N.
Proof.
apply: intmul_inj; set z1 := ('X + 1%:P) :{poly int}.
have aux: forall t j, (z1 ^+ t)`_j = 'C (t, j) %Z.
  move=> t j; rewrite /z1 (power_monom _ t) coef_poly expr1n.
  by case (ltnP j t.+1) => h //; rewrite ?pmulrn ?intz // bin_small.
move:(f_equal (fun z:{poly int} => z`_ i)  (exprD z1 k l)).
rewrite coefM aux;move  => ->;rewrite sumMz intz.
by apply: eq_bigr => j _;rewrite !aux intz PoszM. 
Qed.

Lemma G6_a (n p:nat) (a b: int): 
  (\sum_(i < p.+1) a^+ (p-i) * b ^+ i *+ ('C(n, i) * 'C(n-i, p-i)) = 
     (a+b) ^+ p *+  'C(n , p)  )%Z.
Proof.
have: (n < p) || (p <= n) by rewrite ltnNge orNb.
case /orP => lenp.
  rewrite bin_small // mulr0n big1 //; move => [i lip] _ /=.
  move: lip; rewrite ltnS leq_eqVlt; case /orP => lipp.
    by move /eqP:lipp => ->; rewrite bin_small.
  move: (ltn_sub2r lipp lenp) => h;rewrite (bin_small h) muln0 //.
have leq1: n - p < n.+1 by rewrite ltnS leq_subr.
move: (power_monom (a+b) n) => eq1.
move: (f_equal (coefp (n - p)%N) eq1) => /=; rewrite coef_poly leq1/=.
rewrite (subKn lenp) (bin_sub lenp) => <-.
rewrite polyC_add addrA exprDn coef_sum /=.
move: (lenp); rewrite - ltnS => lenp'. 
have aux: forall i : nat, p < i < n.+1 -> 
  (('X + a%:P) ^+ (n - i) * b%:P ^+ i *+ 'C(n, i))`_(n - p) = 0.
  move => i /andP [i1 i2]; rewrite  coefMn - polyC_exp coefMC power_monom.
  rewrite ltnS in i2; move: (ltn_sub2l (leq_trans i1 i2) i1).
  rewrite coef_poly ltnS ltnNge ;case ((n - p <= n - i)) => // _. 
  by rewrite mul0r mul0rn.  
rewrite  (shorten_sum lenp' aux); apply eq_bigr; move => [i lin] _ /=.
rewrite  coefMn - polyC_exp coefMC mulnC mulrnA  power_monom; congr (_  *+ _).
rewrite ltnS in lin; move: (leq_sub2l n lin) => le3.
rewrite coef_poly ltnS le3 - (bin_sub le3).
have ->: ((n - i - (n - p)) = p - i) %N.
  by rewrite - {1} (subnK lenp) -{2}  (subnK lin) addnA addnK addnC addnK.
by rewrite mulrC - mulrnAr mulrC.
Qed.


Lemma G6_b (n p:nat): p <> 0%N ->
  \sum_(i < p.+1)  (-1%:Z) ^+ i *+ ('C(n, i) * 'C(n-i, p-i)) =  0.
Proof.
move => pnz; move: (G6_a n p 1%:Z (-1%:Z)). 
rewrite addrN (_ : 0 ^+ p = 0) ? mul0rn; last first.
  by  move: pnz; case:p => // p;rewrite exprS mul0r.
by move => eq; rewrite - {2} eq; apply: eq_bigr => i _; rewrite expr1n mul1r.
Qed.

Lemma G6_c (n p:nat): 
  (\sum_(i < p.+1) 'C(n, i) * 'C(n-i, p-i) =  2 ^ p *'C(n , p)  )%N.
Proof.
apply: intmul_inj.
move: (G6_a n p 1 1); rewrite - mulr2n - natrX - mulrnA sumMz.
rewrite (_:  (2 ^ p * 'C(n, p))%:R  = (2 ^ p * 'C(n, p))%N%:~R) //.
by move => <-; apply: eq_bigr => i _; rewrite 2! expr1n mul1r //.
Qed.

Lemma F27_b n: (\sum_(i < n.+1)  i* 'C(n, i) = n * 2 ^ (n.-1) ) %N.
Proof.
apply: intmul_inj.
move: (refl_equal((deriv (('X + 1%:P) ^+ n):{poly int}).[1%Z])). 
rewrite {1} addrC exprDn_comm; last by apply:  commr_polyX.
rewrite deriv_exp derivD derivX derivC addr0 mul1r hornerMn horner_exp. 
rewrite! hornerE - mulr2n - natrX - mulrnA mulnC pmulrn /=. 
rewrite raddf_sum /= horner_sum sumMz;  move => <-; apply: eq_bigr => i _.
by rewrite expr1n mul1r !derivE !hornerMn hornerXn expr1n - mulrnA. 
Qed.

Notation with_sign k x := ( (-1%:Z) ^+ k  *+  x ).

Lemma F28 n: \sum_(i < n.+1)  with_sign i (i* 'C(n, i))
    =  if n is 1 then -1%:Z else 0.
Proof.
case:n; first by rewrite big_ord_recl big_ord0 //.
case; first by rewrite  2!big_ord_recl big_ord0 //.
move => n;move: (refl_equal((deriv (('X + 1%:P) ^+ n.+2):{poly int}).[-1%Z])). 
rewrite {1} addrC exprDn_comm; last by apply:  commr_polyX.
rewrite deriv_exp derivD derivX derivC addr0 mul1r hornerMn horner_exp. 
rewrite! hornerE_comm addNr /= exprS mul0r mul0rn raddf_sum /= horner_sum. 
rewrite -{4}(oppr0) ; set g := \sum_(i<_) _;  set f := \sum_(i<_) _.
move => <- /=; rewrite - sumrN; apply eq_bigr => i _.
rewrite expr1n mul1r !derivE !hornerMn hornerXn - 2!mulNrn - mulrnA.
case:i =>i _ /=; case: i => // i /=; rewrite exprS mulN1r //.
Qed.


End PolyFormulas.


Section BigOps.
Variables (R : comRingType) (idx : R) (op : Monoid.com_law idx).

Lemma big_ord_rev (n : nat) (P : nat -> bool) (F : nat -> R):
  \big[op/idx]_(i < n | P i) F i =
  \big[op/idx]_(i < n | P (n - i.+1)%N) F ( n - i.+1)%N.
Proof. by rewrite - big_mkord big_nat_rev add0n big_mkord. Qed.

Lemma bigop_simpl1  (n m : nat) (F : nat -> R):
   (forall j, (m <= j)%N -> F j = idx) ->
   \big[op/idx]_(j < n) F j = \big[op/idx]_(j < m | (j < n)%N) F j.
Proof.
set s :=  (n + m)%N => h.
rewrite (big_ord_widen s F (leq_addr m n)).
rewrite (big_ord_widen_cond s (fun j => (j < n)%N) F (leq_addl n m)).
rewrite (bigID (fun i0:ordinal s => (i0 < m)%N) _ F) /=.
rewrite [X in op _ X] big1 ? Monoid.mulm1 //.
by move => j; rewrite  -leqNgt; case/andP => _; by apply: h.
Qed.

Lemma big_ord1 (F: 'I_1 -> R): 
   \big[op/idx]_(i < 1) (F i) = F ord0.
Proof. by rewrite big_ord_recl big_ord0  Monoid.mulm1. Qed.

End BigOps.


(* *)

