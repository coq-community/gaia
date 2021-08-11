(*
Bourbaki aux fime
*)

From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path div.
From mathcomp
Require Import fintype tuple finfun bigop finset binomial.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma F7a n: 'C(n, 2) + 6 * 'C(n.+1, 4) = 'C(n, 2) ^ 2.
Proof.
case:n => // n; apply /eqP; rewrite - (eqn_pmul2l (ltn0Sn 3)); apply /eqP.
rewrite mulnDr - (expnMn 2 _ 2) - (mulnA 2 2)  mulnCA - (mulnA 2 3).
rewrite - 2!mul_bin_diag bin1 (mulnCA 3) - !mul_bin_diag mulnCA.
rewrite (mulnCA 2) (mulnCA 2) (mulnCA n.+2) - mulnDr; case:n => //n.
rewrite - !mul_bin_diag bin1 (mulnC _ n) mulnA - mulnDl - mulnn - mulnA.
by rewrite (mulnC n.+1) - {2} (add2n n) (mulSn _ n) addnA add2n - mulnS.
Qed.

Lemma binom_mn_n m n : 'C(m + n, m) = 'C(m + n, n).
Proof.  by have:= (bin_sub (leq_addl m n)); rewrite addnK. Qed.

Lemma bin2' n: 'C(n.+1,2) * 2 = n * n.+1. 
Proof.  by rewrite mulnC -mul_bin_diag bin1 mulnC. Qed.


Lemma mul_Sm_binm_1 n p: n * 'C(n+p,p) = p.+1 * 'C(n+p,p.+1).
Proof.
case: n => [| n]; first by rewrite add0n mul0n bin_small // muln0.
rewrite -binom_mn_n addSn -mul_bin_diag -mul_bin_diag binom_mn_n //.
Qed.

Lemma mul_Sm_binm_r n k p: (n-k) ^_ p * 'C(n,k) = (k +p) ^_ p * 'C(n,k+p).
Proof.
move: k;elim:p => [k | p IHp k]; first by rewrite !ffactn0 addn0.
have aux:  (n-k) * 'C(n,k) = k.+1 * 'C(n,k.+1).
  case(leqP k n) => h; first by rewrite -{2 3}(subnK h) -mul_Sm_binm_1.
  by rewrite bin_small //  bin_small // ? muln0 // leqW.
rewrite 2!ffactnS (mulnC (n-k)) -mulnA aux mulnCA - subnS IHp {IHp}.
rewrite mulnA addnS -addSn; congr (_ * _).
case: p; [ by rewrite addn0 | move => p].
by rewrite ffactnS mulnCA  addnS succnK ffactnSr addnK (mulnC _ k.+1).
Qed.

Lemma mul_Sm_binm_2 n k: (n-k) * 'C(n,k) = k.+1 * 'C(n,k.+1).
Proof. by have:= (mul_Sm_binm_r n k 1);rewrite !ffactn1 addn1. Qed.

Lemma binom_exchange j k q:
  'C(j+k+q,j+k) * 'C(j+k,j) = 'C(k+q,k) * 'C(j+k+q,j).
Proof.
have bin_fact1: forall n m,  'C(n+m,m) * (m`! * n`!) = (n+m)`!.
  by move => n m; move: (bin_fact (leq_addl n m)); rewrite addnK.
move: (bin_fact1 (k+q) j) (bin_fact1 q (j+k)).
rewrite (mulnC j`!) (addnC k)(addnC j)  - (bin_fact1 q k) - (bin_fact1 k j).
rewrite (mulnAC _ _ j`!) !mulnA - (addnA q) (addnC q) => <-.
move /eqP; rewrite !eqn_pmul2r ? fact_gt0 //;move /eqP ->; apply: mulnC. 
Qed.

Lemma binom_exchange1 j k n:
  'C(j+n,j+k) * 'C(j+k,j) = 'C(n,k) * 'C(j+n,j).
Proof.
case: (ltnP n k) => nk; last by rewrite - (subnKC nk) addnA binom_exchange.
by rewrite (bin_small nk) bin_small ?mul0n // ltn_add2l.
Qed.

Lemma sum_bin_rec (n :nat) (f: nat -> nat):
  \sum_(i<n.+1) 'C(n.+1,i.+1) * (f i) =
  \sum_(i<n) 'C(n,i.+1) * (f i) +  \sum_(i<n.+1) 'C(n,i) * (f i).
Proof.
transitivity 
   (\sum_(i < n.+1) 'C(n, i.+1) * (f i) + \sum_(i < n.+1) 'C(n, i) * (f i)).
 rewrite - big_split; apply eq_bigr => // i _; rewrite binS mulnDl //.
by rewrite big_ord_recr /= bin_small ?addn0.
Qed.


(* ---- Derangements *)


Fixpoint der_rec n :=
   if n is n'.+1 then if n' is  n''.+1 then n' * (der_rec n'' + der_rec n')
   else 0 else 1.

Definition derange n := nosimpl der_rec n.

Lemma derange0: derange 0 = 1.  Proof. by []. Qed.

Lemma derange1: derange 1 = 0.  Proof. by []. Qed.

Lemma derangeS n: derange n.+2 = (n.+1) * (derange n + derange n.+1). 
Proof. by []. Qed.

Lemma derangeS1 n (p := n.+1 * derange n):
   derange n.+1 = if (odd n) then p.+1 else p.-1.
Proof.
have pa: forall s, 0 <derange s.+2.
  elim => // s dp; rewrite derangeS muln_gt0 ltn0Sn addn_gt0 dp orbT //.
have pn: forall s, ~~odd s -> 0 < (s.+1) * derange s.
  by case => //;case => // s _; rewrite muln_gt0 ltn0Sn pa.
rewrite /p {p};elim :n => // n Hrec; rewrite derangeS Hrec /=.
move: (pn n); case (odd n).
    move => _; rewrite /negb (mulSnr n.+1) [in X in _ = X] addnS succnK.
    by rewrite - mulnDr (addnC).
by move => /= h; rewrite mulnDr; rewrite -{1} (@prednK (n.+1 * _)) // h.
Qed.


Lemma derange_sum n: 
  \sum_(i<n.+1) 'C(n,i) * (derange i) =  n`! /\
  \sum_(i<n.+1) 'C(n,i) * (derange i.+1) =  n * n`!.
Proof.
elim:n => [| n [IH1 IH2]]; first  by split; rewrite big_ord_recl big_ord0 //.
rewrite factS mulSn -IH2 -IH1;split.
  rewrite  (big_ord_recl n) big_ord_recl /= !bin0 mul1n -addnA; congr (_ + _).
  exact: (sum_bin_rec n (fun i => (derange (i.+1)))).
rewrite -big_split big_distrr /= big_ord_recl add0n; apply: eq_bigr => i _.
by rewrite - mulnDr mulnA  mul_bin_diag derangeS mulnCA mulnA.
Qed.


(* --- *)
Section Stirling.

(** Stirling Number of Second Kind 
 [ 'St(n,m) is the number of partitions of a set of [n] elements into [p] parts
   and  'St(n,m) is the number of surjective functions of a set with [n]
   elements into a set with [p] elements.  
*)

Fixpoint stirling2_rec n m :=
  match n, m with 
  | n'.+1, m'.+1 => m *stirling2_rec n' m + stirling2_rec n' m'
  | 0, 0 => 1
  | 0, _.+1 => 0
  | _ .+1, 0 => 0
  end.

Definition stirling2 := nosimpl stirling2_rec.
Definition nbsurj n m := (stirling2 n m) *  m`!. 

Notation "''St' ( n , m )" := (stirling2 n m)
  (at level 8, format "''St' ( n ,  m )") : nat_scope.
Notation "''Sj' ( n , m )" := (nbsurj n m)
  (at level 8, format "''Sj' ( n ,  m )") : nat_scope.

Lemma stirE : stirling2 = stirling2_rec.  Proof. by []. Qed.

Lemma stir00 : 'St(0, 0) = 1. Proof. by [].  Qed.
Lemma nbsurj00 : 'Sj(0, 0) = 1. Proof. by [].  Qed.
Lemma stirn0 n : 'St(n.+1, 0) = 0.  Proof. by [].  Qed.
Lemma nbsurjn0 n : 'Sj(n.+1, 0) = 0.  Proof. by [].  Qed.
 Lemma stir0n m : 'St(0, m.+1)  = 0.  Proof. by [].  Qed.
Lemma nbsurj0n m : 'Sj(0, m.+1)  = 0.  Proof. by [].  Qed.
Lemma stirS n m : 
   'St(n.+1, m.+1) = (m.+1) * 'St(n, m.+1) + 'St(n, m).  Proof. by [].  Qed.

Lemma nbsurjS n m :  'Sj(n.+1, m.+1) = (m.+1) * ('Sj(n, m.+1) + 'Sj(n, m)).  
Proof.
by rewrite /nbsurj stirS mulnDr mulnDl - ! mulnA (mulnCA _ _  m`!) factS.
Qed.

Lemma stir_n1  n: 'St(n.+1, 1) = 1.
Proof. by elim: n => // n Ihn; rewrite stirS Ihn. Qed.

Lemma nbsurj_n1  n: 'Sj(n.+1, 1) = 1.
Proof. by rewrite /nbsurj stir_n1. Qed.

Lemma nbsurj_n2  n: 'Sj(n.+1, 2) = (2 ^n.+1 - 2).
Proof. 
elim: n => // n Ihn; rewrite nbsurjS Ihn  nbsurj_n1  (expnS _ n.+1).
rewrite -(subnK (leq_trans(_: 2 <= n.+2) (ltn_expl n.+1 (ltnSn 1)))) //.
by rewrite addnK 2!mulnDr (_: 2 * 2 = 2 +2) // addnA addnK.
Qed.

Lemma stir_n2  n: 'St(n.+1, 2) = (2 ^n - 1).
Proof.
elim: n => // n Ihn; rewrite stirS Ihn stir_n1 expnS.
rewrite -(subnK (leq_trans (ltn0Sn n) (ltn_expl n (ltnSn 1)))) //.
by rewrite addnK mulnDr (_: 2 * 1 = 1 + 1) // addnA addnK.
Qed.

Lemma stir_small n p: 'St(n, (n+p).+1) = 0.
Proof.
move: p; elim: n => [p // | n Hrec p].
by rewrite addSn stirS Hrec -addnS Hrec muln0.
Qed.

Lemma stir_small1 n p: n < p -> 'St(n,p) = 0.
Proof. by move /subnKC => <-; rewrite addSn stir_small. Qed.


Lemma nbsurj_small n p: 'Sj(n, (n+p).+1) = 0.
Proof. by rewrite /nbsurj stir_small1 // - addSn leq_addr.  Qed.

Lemma stir_nn n: 'St(n, n) = 1.
Proof. by elim:n=> [//|n Hrec]; rewrite stirS Hrec stir_small1 ? muln0. Qed.

Lemma nbsurj_nn n: 'Sj(n, n) = n`!.
Proof.  by rewrite /nbsurj stir_nn mul1n. Qed.

Lemma binn n : 'C(n, n) = 1.
Proof. by elim: n => [// |n IHn]; rewrite binS bin_small. Qed.


Lemma stir_Snn n: 'St(n.+1, n) = 'C(n.+1,2).
Proof.
elim:n => [//|n IHn]. 
by rewrite stirS IHn stir_nn muln1 addnC (binS (n.+1)) bin1. 
Qed.

Lemma nbsurj_Snn n: 'Sj(n.+1, n) = 'C(n.+1,2) * n`!.
Proof. by rewrite /nbsurj stir_Snn.  Qed.

Lemma stir_SSnn n: 'St(n.+2, n) = 'C(n.+3,4) + 2 * 'C(n.+2,4).
Proof.
elim:n => [// | n Hrec]; rewrite stirS Hrec stir_Snn addnCA (binS (n.+3)).
rewrite -addnA; congr (_ + _).
rewrite (binS (n.+2) 3) (addnC 'C(n.+2, 4)) mulnDr addnA; congr (_ + _).
by rewrite  (binS (n.+2) 2) addnC addnA mulSnr -addn2 mul_Sm_binm_1 mulSnr.
Qed.

Lemma stir_Snn' n: 'St(n.+1, n) = \sum_(i<n.+1) i.
Proof.
elim: n => [//| n Ihn]; first by rewrite big_ord_recl big_ord0.
by rewrite  big_ord_recr /= stirS Ihn stir_nn addnC muln1.
Qed.

Lemma nbsurj_SSnn n: nbsurj n.+2 n = ('C(n.+3,4) + 2 * 'C(n.+2,4)) * n`!.
Proof. by rewrite /nbsurj stir_SSnn.  Qed.

Fixpoint stirling1_rec n m :=
  match n, m with 
  | n'.+1, m'.+1 => n' *stirling1_rec n' m + stirling1_rec n' m'
  | 0, 0 => 1
  | 0, _.+1 => 0
  | _ .+1, 0 => 0
  end.

Definition stirling1 := nosimpl stirling1_rec.

Notation "''So' ( n , m )" := (stirling1 n m)
  (at level 8, format "''So' ( n ,  m )") : nat_scope.


Lemma stir1_E : stirling1 = stirling1_rec.   Proof. done. Qed.
Lemma stir1_00 : 'So(0, 0) = 1.              Proof.  done. Qed.
Lemma stir1_n0 n : 'So(n.+1, 0) = 0.         Proof.  done. Qed.
Lemma stir1_0n m : 'So(0, m.+1)  = 0.        Proof.  done. Qed.
Lemma stir1_S n m :  'So(n.+1, m.+1) = n * 'So(n, m.+1) + 'So(n, m).  
  Proof.  done. Qed.

Lemma stir1_Sn1 n :  'So(n.+1,1) = n `!.
Proof. by elim:n => // n Hr; rewrite stir1_S stir1_n0 Hr addn0. Qed.

Lemma stir_Sn1 n :  'St(n.+1,1) = 1.
Proof. by elim:n => // n Hr; rewrite stirS Hr  stirn0. Qed.

Lemma stir1_small n p: 'So(n, (n+p).+1) = 0.
Proof.
move: p; elim: n => [p // | n Hrec p].
by rewrite addSn stir1_S Hrec -addnS Hrec muln0.
Qed.

Lemma stir1_small1 n p: n < p -> 'So(n,p) = 0.
Proof. by move /subnKC => <-; rewrite addSn stir1_small. Qed.

Lemma stir1_nn n :  'So(n,n) = 1.
Proof. by elim:n => // n Hr; rewrite stir1_S Hr stir1_small1 // muln0.  Qed.


Lemma stir1_Snn n: 'So(n.+1, n) = 'C(n.+1,2).
Proof.
elim:n => [//|n IHn]. 
by rewrite stir1_S IHn stir1_nn muln1 addnC (binS (n.+1)) bin1. 
Qed.

(* Euler *)

Fixpoint euler_rec n m :=
  match n, m with 
    | n'.+1, m'.+1 => m.+1 *euler_rec n' m + (n'-m') * euler_rec n' m'
    | 0, _ => 0
    |  _.+1, 0 => 1
  end.

Definition euler := nosimpl euler_rec.

Notation "''Eu' ( n , m )" := (euler n m)
  (at level 8, format "''Eu' ( n ,  m )") : nat_scope.

Lemma eulerE : euler = euler_rec. Proof. by []. Qed.
Lemma euler0m m : 'Eu(0, m) = 0. Proof. by [] . Qed.
Lemma eulern0 n : 'Eu(n.+1, 0) = 1. Proof. by []. Qed.
Lemma eulerS n m : 'Eu(n.+1, m.+1) = m.+2 * 'Eu(n, m.+1) + (n-m) * 'Eu(n,m).
Proof. by []. Qed.

Lemma euler_small n p: 'Eu(n, n+p) = 0.
Proof.
move: p; elim: n => [p // | n Hrec p].
by rewrite addSn eulerS -addnS 2!Hrec 2!muln0.
Qed.

Lemma euler_small1 n p: n <= p -> 'Eu(n,p) = 0.
Proof.  by move /subnKC => <-; rewrite euler_small. Qed.

Lemma euler_nn n: 'Eu(n.+1,n) = 1.
Proof. 
elim :n => [// | n Hrec]; rewrite eulerS Hrec euler_small1 ?subSnn // muln0//.
Qed.

(* nice formulas; obvious by inversion and Worpitzky *)
Lemma eulern1 n: 'Eu(n,1) + 'C(n.+1, 1) = 2 ^ n.
Proof.
elim:n => [// | n Hrec]; rewrite eulerS expnS - Hrec mulnDr - addnA {Hrec}.
by case: n => // n; rewrite eulern0 2!bin1 subn0 muln1 - addSnnS addnn -mul2n.
Qed.

Lemma eulern2 n: 'Eu(n,2) + 2^n * 'C(n.+1,1)  = 3 ^n + 'C(n.+1, 2).
Proof.
elim:n => [// | n Hrec]; rewrite eulerS (binS n.+1 1).
apply /eqP; rewrite - (eqn_add2r (2 * 'C(n.+1, 2))); apply /eqP.
rewrite -3! addnA (addnAC _ 'C(n.+1, 1)) - mulSn (addnA (3 ^ n.+1))(expnS 3). 
rewrite - mulnDr - Hrec {Hrec} mulnDr -addnA (mulnC 2) bin2'.
congr (_ + _);case: n => // n; rewrite subSS subn0 -{3} (bin1 n.+2) mulSnr. 
rewrite (addnCA _ (n * _))  addnA - mulnDr eulern1 addnA.
rewrite mulnC (expnS _ n.+1) (mulnC 2) mulnAC - mulnA - mulnDr mulnCA !bin1.
by rewrite mulSn addnA addn2 - mulnS (mulnC 3).
Qed.

Lemma eulern3 n: 
  'Eu(n,3) +  3^n * (n.+1) + 'C(n.+1, 3) = 4 ^n + 2^n * 'C(n.+1, 2). 
Proof.
elim:n => [// | n Hrec]; rewrite eulerS (binS n.+1 2) (addnC 'C(n.+1, 3)).
rewrite addnA - (addnA (4 * _)) - (addnA (4 * _)).
apply /eqP; rewrite - (eqn_add2r (4 * 3 ^ n * n.+1 + 3 * 'C(n.+1, 3))). 
rewrite - addnA (addnCA 'C(n.+1, 3))  - addnA - mulSn - mulnA - mulnDr.
rewrite (addnC _ (4 * _)) addnA  - mulnDr (addnA ('Eu( _,_))) Hrec {Hrec}.
rewrite  mulnDr - expnS - mul_Sm_binm_2 mulnA - (mulnA 2 2) -expnS -mulnA.
rewrite  mul2n -addnn (addnA (4 ^ n.+1))  (binS n.+1 1) mulnDr - 5!addnA.
apply /eqP; congr (_ + (_ + _)); case:n => // n; case :n => // n. 
rewrite 4! subSS 2!subn0 expnS (mulnC 2) -mulnA (mulnC 2) bin2' -{1}(bin1 n.+3).
rewrite - {2} (addn2 n) mulnDl mulnDr mulnCA addnAC addnA - mulnDr.
rewrite (addnC _ 'Eu(n.+2, 2)) eulern2 addnC mulnA; congr (_ + _).
rewrite mulnDr addnAC addnA (expnS _ n.+2) mulnAC - mulnDl - addnA.
by rewrite - mulSn mulnS addnA addn3 - mulSn mulnAC mulnA.
Qed.

(* symmetry formula *)

Lemma euler_sub n m: m <=n -> 'Eu(n.+1,m) = 'Eu(n.+1, n-m).
Proof. 
move: m; elim: n; first by case.
move => n Hrec m; rewrite leq_eqVlt; move/orP; case.
  by move /eqP => ->; rewrite euler_nn subnn eulern0.
rewrite ltnS; case: m; first by rewrite subn0 euler_nn eulern0.
move => m le1; rewrite (subSn le1) eulerS (eulerS n.+1) (subnSK le1).
rewrite addnC (subSn (ltnW le1)) (Hrec _ (ltnW le1)) (Hrec _ le1).
by rewrite (subSn (leq_subr _ _)) (subnBA _ le1) addKn.
Qed.

Lemma euler_sum n : \sum_(i<n.+1) 'Eu(n.+1,i) = (n.+1)`!.
Proof.
elim:n => [|n IHn]; first by rewrite big_ord_recl big_ord0 addn0.
rewrite big_ord_recl eulern0.
transitivity (1 + (\sum_(i < n.+1) (i.+2) * 'Eu(n.+1, lift ord0 i)
  + (\sum_(i < n.+1) (n.+1 -i) * 'Eu(n.+1, i)))). 
   congr (_ + _); rewrite -big_split /=; apply: eq_bigr => i _; apply: eulerS.
rewrite big_ord_recr big_ord_recl /= euler_small1 // muln0 addn0 muln1 subn0.
rewrite (addnCA _ n.+1) addnA add1n - big_split /= factS -IHn.
rewrite big_ord_recl eulern0 mulnDr muln1 big_distrr /=; congr (_ + _).
apply: eq_bigr; move => [i lin] _; rewrite -mulnDl /= (subSn lin). 
by rewrite (subnSK lin) - add2n - addnA (addnC i) add2n subnK ? (ltnW lin).
Qed.

Lemma euler_sum_aux n p: 
    \sum_(i<n.+1) 'Eu(n.+1,i) * 'C(i,p) = 'Sj(n.+1, n.+1 - p). 
Proof.
move:p; elim: n.
  move => p; rewrite big_ord_recl big_ord0 /=; case p => //.
move => n Hrec p.
case (ltnP n.+1 p) => ltnp.
   move : (ltnp); rewrite - subn_eq0 => /eqP ->; rewrite nbsurjn0 big1 //.
   move => [i lin] _; rewrite bin_small ?muln0 //. apply: (leq_trans  lin ltnp).
move: ltnp; case: p.
   move => _; rewrite subn0 nbsurj_nn - euler_sum; apply: eq_bigr.
    by move => i _; rewrite bin0 muln1.
move => p ltnp; rewrite (subSn ltnp) nbsurjS - Hrec subSS - {2} subSn //.
rewrite - Hrec - big_split big_distrr /= big_ord_recl  add0n.
transitivity (\sum_(i < n.+1)  (i.+2) * 'Eu(n.+1, i.+1) * 'C(i.+1, p.+1) 
   +  \sum_(i < n.+1) (n.+1-i) * 'Eu(n.+1, i) * 'C(i.+1, p.+1)).
   rewrite - big_split /=; apply: eq_bigr => i _.
   by rewrite - mulnDl - eulerS.
have ->: \sum_(i < n.+1) i.+2 * 'Eu(n.+1, i.+1) * 'C(i.+1, p.+1) =
  \sum_(i < n.+1) i.+1 * 'Eu(n.+1, i) * 'C(i, p.+1). 
  rewrite big_ord_recr /= euler_small1 // muln0 addn0.
  by symmetry; rewrite big_ord_recl /= add0n.
rewrite -big_split /=; apply: eq_bigr; move => [i  lein] _ /=.
set x := 'Eu(n.+1, i).
rewrite 2! (mulnC _ x) -2! mulnA - 2! mulnDr (mulnCA _ x); congr (_ * _).
rewrite binS mulnDr addnA -mulnDl addSn subnKC ? (ltnW lein) //.
case (ltnP i p) => ltip. 
   by rewrite bin_small ? leqW // bin_small // 3!muln0.
rewrite  mulnDr addnC {1} (_: (n - p).+1 = (n.+1 - i)  + (i - p)).
  by rewrite mulnDl mul_Sm_binm_2 -addnA  -mulnDl addSn addnS subnKC. 
by rewrite ltnS in lein; rewrite subSn // addSn - {1} (subnK lein) addnBA.
Qed.

(*  Worpitzky *)
Lemma euler_sum_pow k n : k ^n.+1 = \sum_(i<n.+1) 'Eu(n.+1,i) * 'C(k+i,n.+1).
Proof.
elim:n; first by rewrite big_ord_recl big_ord0 mul1n // addn0 bin1 // addn0.
move => n Hrec.
rewrite big_ord_recl // addn0 eulern0 mul1n.
transitivity (\sum_(i < n.+2) i.+1 * 'Eu(n.+1, i) * 'C(k + i, n.+2)
   + (\sum_(i < n.+1) (n.+1-i) * 'Eu(n.+1, i) * 'C(k + i.+1, n.+2)));last first.
   rewrite big_ord_recl // addn0 eulern0 mul1n - addnA -big_split /=. 
   by congr (_ + _); apply: eq_bigr => i _; rewrite -mulnDl -eulerS.
rewrite big_ord_recr /= euler_small1 // muln0 addn0 // -big_split /=.
rewrite expnS Hrec big_distrr /=; apply: eq_bigr => i _ /=.
rewrite mulnAC (mulnAC (n.+1 - i)) - mulnDl mulnC (mulnC _ 'Eu(_,_)).
rewrite addnS binS  (mulnDr (n.+1 - i)) addnA - mulnDl addSn. 
rewrite subnKC ?(@ltnW i) // -mul_Sm_binm_2 -mulnDl addnBA ? (@ltnW i) //.
case (ltnP (k + i) n.+1) => ltnp; first by rewrite (bin_small ltnp) !muln0.
by rewrite (subnK ltnp) addnK (mulnC k) mulnA.
Qed.

Lemma sum_pow_euler n k:  
   \sum_(i<n) i ^k.+1 =  \sum_(i<k.+1) 'Eu(k.+1,i) * 'C(n+i,k.+2). 
Proof.
move: k; elim :n. 
   move => k;rewrite big_ord0 big1 // => [] [i lin] _ /=. 
   by rewrite bin_small ?muln0 // add0n leqW //.
move => n IHn k; rewrite big_ord_recr /= IHn euler_sum_pow - big_split /=.
by apply: eq_bigr => i _; rewrite - mulnDr (addSn n) binS.
Qed.

Lemma F9aux2 n:  \sum_(i<n) i ^5 =
   'C(n, 6) + 26* 'C(n + 1, 6) +  66 * 'C(n + 2, 6) + 
   26 * 'C(n + 3, 6) + 'C(n + 4, 6).
Proof. rewrite sum_pow_euler 5! big_ord_recr /= big_ord0 2! mul1n addn0 //. Qed.

Section Partition.

Lemma neq_sym (T: eqType) (x y: T): (x != y) = (y != x).
Proof.
case: (_ =P _); first by  move => ->; rewrite eqxx.
case: (_ =P _) => // -> //.
Qed.

(* disjointU1 ne s'applique pas ? *)
Lemma disjointsU1 (T: finType) (A B: {set T}) x:
  [disjoint (x |: A)  & B]  =  (x \notin B) && [disjoint A & B].
Proof.
rewrite - !setI_eq0 setIUl; case h: (x \in B) => /=.
  by apply /set0Pn; exists x; rewrite !inE h eqxx.
rewrite (_  : [set x] :&: B = set0) ? set0U //.
by apply /setP  => y; rewrite !inE; apply /andP => [[/eqP ->]]; rewrite h.
Qed.


Lemma partition_ni_set0 (T:finType) (P: {set {set T}}) E i: 
   partition P E -> i \in P -> i != set0.
Proof.
by move /and3P => [_ _ /negP n0P]; apply:contraTneq => ->; apply /negP.
Qed.

Lemma card_partition_aux  (T:finType) (P: {set {set T}}) E:
   partition P E -> #|P| <= #|E|.
Proof.
move => pe;rewrite (card_partition pe) - sum1_card; apply: leq_sum => i.
rewrite card_gt0; apply: (partition_ni_set0 pe).
Qed.

Lemma partition_set0 (T:finType) (P: {set {set T}}) : 
   partition P set0  = (P == set0).
Proof.
apply /idP/eqP.
  by move /card_partition_aux; rewrite cards0 leqn0 => /eqP /cards0_eq. 
by move ->; rewrite /partition /trivIset /cover !big_set0 cards0 in_set0 !eqxx.
Qed.

Lemma card_inv_im (aT rT: finType) (f: aT -> rT) (A: {set aT}) (n: nat):
   (forall x, x \in A -> #|[set y in A | f x == f y]| = n) ->
   #|A| =  #|f @: A| * n.
Proof.
pose g x := [set y in A | x == f y ]. 
have: {in f @: A &, injective g}.
   move => x y /imsetP [x' x'A ->] /imsetP [y' y'A ->] => eq.
   have: (x' \in (g (f x'))) by  rewrite /g inE x'A eqxx.
   by rewrite eq inE => /andP [_] /eqP.
move /imset_injP; rewrite -imset_comp; move /eqP => <-  h.
apply:card_uniform_partition.
 by move => a /imsetP [x xA ->]; rewrite - (h _ xA).
exact: preim_partitionP.
Qed.




Lemma stirling_partition  (T: finType) (E: {set T}) (p:nat):
  #|[set P  | partition P E && (#|P| == p) ]| = 'St(#|E|, p).
Proof.
move: p; elim: {E} #|E| {1 3} E (refl_equal  #|E|).
  move => E /cards0_eq => ->; case.
     apply: (eq_card1 (x := (@set0 (set_of_finType T)))) => p.
     rewrite !inE cards_eq0 /= partition_set0; case : (p == set0) => //.
  move => n;apply: eq_card0 => p; rewrite !inE partition_set0 -cards_eq0. 
  by apply /andP=> [[/eqP ->]].
move => n IHn E cE; case.
  apply: eq_card0 => P; rewrite !inE; apply /andP => [[/and3P[/eqP cP p1 _ ]]].
  by rewrite cards_eq0 => /eqP p2; move: p1; rewrite/trivIset cP cE p2 big_set0.
move => p.
move: (ltn0Sn n); rewrite -cE card_gt0 => /set0Pn [xa xaE].
move: (setD1K xaE); set E' := E :\ xa => eq1.
have xaE': xa \notin E' by rewrite !inE eqxx andFb.
move: (sym_eq (cardsU1 xa E')); rewrite eq1 cE xaE' addnC addn1. 
move /eq_add_S => cE'; rewrite stirS - (IHn _ cE') - (IHn _ cE') {IHn}.
rewrite - sum1dep_card (bigID (fun P => (pblock P xa == [set xa]))) /=.
rewrite 2! sum1dep_card addnC; congr (_ + _).
  pose f x := ((pblock x xa) :\ xa |:  (x :\ (pblock x xa))).
  set A := [set x | _]; set B := [set x | _].
  have fAB: forall P (y := pblock P xa), P \in A ->
    (((f P) \in B) /\
     (xa \in y /\ (y \in P) /\  (y :\ xa \notin P :\ y))).
    move => P y; rewrite !inE.
    move => /andP [/andP [/and3P [/eqP cP /trivIsetP tI eP] /eqP sP] yxa].
    have yP: y \in P by apply: pblock_mem; rewrite cP.
    have xay: xa \in y by rewrite mem_pblock cP.
    have yane:  y :\ xa != set0.
       apply: (contraNneq _ yxa); rewrite -/y  -{2} (setD1K xay) => ->.
       by rewrite setU0 eqxx.
    have yanP: y :\ xa \notin P.
      apply /negP => y'P; move: (tI _ _ y'P yP (proper_neq (properD1 xay))).
      move /set0Pn: yane => [x /setD1P [xxa xy]] /pred0Pn.
      by case;exists x; rewrite /= !inE // xxa xy.
    have set0p: set0 \notin y :\ xa |: P :\ y.
      by rewrite !inE negb_or neq_sym yane negb_and eP orbT.
    have cy: cover (y :\ xa |: P :\ y) = E'.
      move: cP; rewrite -{1} (setD1K yP) /cover 2!bigcup_setU 2! big_set1 /E'.
      move => <-; apply /setP => x; rewrite in_setU 2! in_setD1 in_setU.
      apply /idP /idP; last by case /andP => ->; rewrite andTb.
      case /orP; first by move /andP => [-> ->] //.
      move => h; rewrite h orbT andbT; apply: contraTneq h => ->. 
      rewrite /cover; apply/negP => /bigcupP [i] /setD1P [iy ip] xi.
      by move /pred0P: (tI _ _ ip yP iy) => h;move: (h xa) => /=;rewrite xay xi.
   have dia: forall s, s \in P :\ y ->  y :\ xa != s -> [disjoint y :\ xa & s].
      move => s /setD1P  [sy sp] h1; move: (tI _ _ sp yP sy). 
      rewrite - setI_eq0 => /eqP hh; apply /pred0P => t /=. 
      by rewrite in_setD1 -andbA - in_setI setIC hh in_set0 andbF.
    have tIy: trivIset (y :\ xa |: P :\ y).
       apply /trivIsetP => s1 s2; case /setU1P => h1; case /setU1P => h2. 
       - by rewrite h1 h2 eqxx.
       - by rewrite h1; apply: dia.
       - by rewrite neq_sym disjoint_sym h2; apply: dia.
       - by apply: tI; [ case /setD1P: h1 | case /setD1P: h2].
    rewrite /partition set0p  cy tIy eqxx 3!andTb.
    by rewrite cardsU1 -sP (cardsD1 y P) yP in_setD1 negb_and yanP orbT.
  pose g P y := ( xa |: y) |: (P :\ y).   
  have fBA: forall P y, P \in B -> y \in P -> (g P y) \in A /\ f (g P y) = P.
    move => P y; rewrite !inE => /andP [/and3P [/eqP p1 p2 p3] /eqP p4] p5.
    move /trivIsetP: (p2) => tI; rewrite /partition.
    have xasP: forall s, s \in P -> xa \notin s.
      move => s sP; apply: contra xaE'=> xas; rewrite -p1.
      by apply /bigcupP; exists s.
    move: (xasP _ p5) => xay.
    have e1: (xa |: y \notin P :\ y).
      by rewrite in_setD1 negb_and (contra (xasP _)) ?orbT // setU11. 
    have e2:  xa |: y != [set xa].
      by apply :contraNneq p3 => h; move: (setU1K xay); rewrite h setDv => ->.
    have dia: forall s, s \in P :\ y ->  xa |: y != s -> [disjoint xa |: y & s].
      move => s /setD1P [sy sp] us; move: (tI _ _ sp p5 sy).
      by rewrite disjointsU1 disjoint_sym (xasP _ sp) => ->.
    have e3: trivIset (xa |: y |: P :\ y).
       apply /trivIsetP => s1 s2;  case /setU1P => h1; case /setU1P => h2.
       - by rewrite h1 h2 eqxx.
       - by rewrite h1; apply: dia.
       - by rewrite h2 disjoint_sym neq_sym; apply: dia.
       - by apply: tI; [ case /setD1P: h1 | case /setD1P: h2].
    rewrite /g /f (def_pblock e3 (setU11 (xa |: y) (P :\ y))(setU11 xa y)).
    rewrite in_setU1 negb_or in_setD1 negb_and p3  orbT neq_sym -card_gt0. 
    rewrite cardsU1 xay add1n ltn0Sn - p4 (cardsD1 y P) p5 cardsU1 e1 eqxx e2. 
    rewrite (setU1K xay) (setU1K e1) (setD1K p5) e3 !andbT - eq1 - p1.
    by rewrite - {2} (setD1K p5) /cover  2!bigcup_setU 2! big_set1 setUA.
  have -> : B = f @: A.
    apply /setP => y; apply /idP/idP.
       move => yb; move: (yb); rewrite inE => /andP [_] /eqP cy.
       move: (ltn0Sn p); rewrite -cy card_gt0 => /set0Pn [x xy].
       move: (fBA _ _ yb xy) => [h1 <-].
       by apply /imsetP; exists (g y x). 
    move /imsetP => [P] pa ->; apply: (proj1 (fAB _ pa)).
  rewrite mulnC; apply:card_inv_im => x xA.
  move: (proj1 (fAB _ xA)); rewrite inE => /andP [_] /eqP => <-.
  set s := [set y | _].
(* ici *)
  have ->: s = g (f x) @: f x.
    apply /setP => t; rewrite inE; apply /idP/idP.
      move => /andP [ta /eqP sf].
      move: (fAB _ ta); set y := pblock t xa ; move => [pa [pb [pc pd]]].
      apply /imsetP; exists (y :\ xa); first by rewrite sf;apply/setU1P; left.
      by rewrite  sf /f/g -/y (setD1K pb)  (setU1K pd)  (setD1K pc).
    move /imsetP => [z zf ->];move: (fBA _  _ (proj1 (fAB _ xA)) zf).
    by move => [-> ->]; rewrite eqxx.
  move: (fAB _ xA); set y := pblock x xa ; move => [pa [pb [pc pd]]].
  rewrite  (card_in_imset) // => u v p1 p2 eq.
  move: (fBA _ _ pa p1); rewrite inE => [][] /andP [] /andP [].
  move /and3P => [_ tI _] _ _ _.
  have p3 : pblock  (g (f x) u) xa = xa |: u.
    have r2: xa |: u \in (g (f x) u) by apply /setU1P; left.
    by rewrite (def_pblock tI r2) // setU11. 
  have p4 : pblock (g (f x) v) xa = xa |: v.
    rewrite eq in tI.
    have r2: xa |: v \in (g (f x) v) by apply /setU1P; left.
    by rewrite (def_pblock tI r2) // setU11. 
  have xau: forall u, u \in f x -> xa \notin u.
    move:  pa; rewrite inE => /andP [] /and3P [/eqP cf _ _] _.
    move => w wf; apply/negP => xaw; move /negP:xaE'; rewrite -cf /cover.
    by case; apply /bigcupP; exists w.
  have ->: u = (xa |: u) :\ xa by rewrite setU1K //; apply: xau.
  have ->: v = (xa |: v) :\ xa by rewrite setU1K //; apply: xau.
  by rewrite -p3 -p4 eq.
have aux: forall P, partition P E' -> [set xa] \notin P.
  move => P /and3P [] /eqP pa pb pc; apply /negP => pd.
  move/negP: xaE'; case; rewrite -pa.
  apply /bigcupP; exists [set xa] => //; apply: set11.
have h: {in [set P | partition P E' && (#|P| == p)] &,
  injective  (fun P =>  [set xa] |: P)}.
  move => P Q; rewrite !inE => /andP [p1 _] /andP [p2 _] eq.
  by rewrite - (setU1K (aux _ p1))  - (setU1K (aux _ p2)) eq.
rewrite  -(card_in_imset h) {h}; apply: eq_card => y; rewrite !inE. 
apply /idP/idP.
  move /andP =>[] /andP [] /and3P [] /eqP  uy ty ey /eqP cy /eqP  uy'.
  move: xaE; rewrite - uy => xay.
  move: (pblock_mem xay); rewrite uy' => xsay;  move: (setD1K xsay) => h.
  apply /imsetP; exists (y :\ [set xa]) => //. 
  move: (cardsU1 [set xa] (y :\ [set xa])); rewrite h setD11 add1n cy => cy'.
  rewrite inE -eqSS -cy' eqxx andbT /partition in_setD1 negb_and ey orbT andbT.
  apply /andP; split.
    rewrite /E' - uy - {2} h; rewrite /cover bigcup_setU big_set1 setU1K //.
    apply /negP => /bigcupP => [] [i] /setD1P [iny iy] xai.
    move /trivIsetP: ty => hh; move: (hh _ _ iy xsay iny).
    by rewrite disjoint_sym disjoints_subset sub1set; move /setCP; case.
  apply /trivIsetP => x x' /setD1P [] _ xy /setD1P [] _; move: xy. 
  move /trivIsetP:  ty; apply.
move /imsetP => [x]; rewrite inE => /andP [px] /eqP cx -> {y}.
move /and3P: px =>  [] /eqP ux tx ex. 
have pf: {in x, forall B : {set T}, [disjoint [set xa] & B]}.
    move => s sy /=; rewrite (eq_disjoint1 (x:= xa)). 
      apply /negP => xas.
      by move: xaE'; rewrite -ux; move /negP; case; apply /bigcupP; exists s.
   by move => u; rewrite !inE.
move: (trivIsetU1 pf tx ex) => [qa qb].
rewrite /partition cardsU1 qa qb cx add1n.
rewrite (def_pblock  qa (setU11 [set xa] x))? set11//.
rewrite /cover bigcup_setU big_set1 -/(cover x) ux eq1.
rewrite in_setU1 negb_or ex !eqxx ! andbT !andTb; apply /negP => /eqP h.
have // : 0 = 1 by rewrite - {1} (@cards0 T) h cards1.
Qed.


(* Note. si P partition de longueur k, i<k, I(P,i) le i-eme element
   enum_val i
je prends (P,i) -> (xa:y :| P :\ y) avec y = I(P,i)
*)

(* [in A, bijective f] [on B, bijective f]  <-> exists g tq.
     {on B, cancel f & g} & {in B, cancel g f}
     {in A, cancel f g} & {on A, cancel g & f}
{in A, cancel f g} == t \in A -> g (f t) = t
{on A, cancel g & f} == g t \in A -> f (g t) = t
donc (1) t \in B -> f (g t) = t &&  f t \in B -> g (f t) = t
donc (2) t \in A -> g (f t) = t &&  g t \in A -> f (g t) = t

*)

Lemma eqcard_equipotent (aT rT: finType):
  (#|aT| = #|rT|) <-> (exists f : aT -> rT, bijective f).
Proof.
split.
   move => sc.
   move:(enum_val_bij aT) => []; set n1 := #|_ |; move  => g1 c1 c2.
   move:(enum_val_bij rT) => []; set n2 := #|_ |; move  => g2 c3 c4.
   have nn: n1 = n2 by rewrite /n1 /n2.
   exists (fun x => enum_val (cast_ord nn (g1 x))).
   exists (fun x =>  enum_val (cast_ord (sym_eq nn) (g2 x))).
     by move => t /=;rewrite c3 cast_ord_comp cast_ord_id c2.
   by move => t /=; rewrite  c1 cast_ord_comp cast_ord_id c4.
move => [f bf].
have rtb: {on rT, bijective f} by apply: onW_bij.
rewrite -(on_card_preimset rtb) - cardsT. 
have -> // : f @^-1: rT = [set: aT] by apply/setP=> x; rewrite !inE.
Qed.

Definition set_surj_fun_on (aT rT: finType) (B: {set rT}):= 
  [set f: {ffun aT -> rT} | f @: aT == B ]. 

Definition set_surj_fun (aT rT: finType):= set_surj_fun_on aT [set: rT].

Lemma set_surj_fun_onP  (aT rT: finType)(B: {set rT} )(f: {ffun aT -> rT}):
   reflect 
      ((forall b, b \in B -> exists2 a, a \in aT & b = f a)
      /\ (forall a, f a \in B))
      (f \in set_surj_fun_on aT B).
Proof.
rewrite inE; apply: (iffP eqP).
  move => <-; split;[ by move => b /imsetP | by move => a;apply: imset_f].
move => [h1 h2]; apply /setP => b; apply /idP/idP. 
    move /imsetP => [x] _ ->;apply: h2.
by move => bb; apply /imsetP; apply: h1.
Qed.

Lemma set_surj_fun_P (aT rT: finType) (f: {ffun aT -> rT}):
   reflect (forall b, exists a, b = f a)(f \in set_surj_fun aT rT).
Proof.
rewrite inE; apply: (iffP eqP) => h.
  move => b; have brt: b \in  f @: aT by  rewrite h.
  by move /imsetP: brt => [a _ ->]; exists a.
apply /setP => b; apply /idP/idP.
  by move /imsetP; rewrite inE. 
by move: (h b) => [a -> _]; apply: imset_f.
Qed.

(*
Lemma card_set_surj_fun_p1 (aT rT: finType) (B: {set rT}):
   #|set_surj_fun_on aT B| =  #|set_surj_fun aT (set_of_finType aT)|.
Abort.


Lemma card_set_surj_fun_pr (aT rT rT': finType) (B: {set rT})(B': {set rT'}):
  #|B| = #|B'| ->  #|set_surj_fun rT B| = #|set_surj_fun rT B'|.
Proof.
move => h.
Abort.

Variables aT rT : finType.

Variables (f : aT -> rT).

Lemma preimset_proper (A B : {set rT}) :
  B \subset codom f -> A \proper B -> (f @^-1: A) \proper (f @^-1: B).
Proof.
set y:= [set x | x <- codom f ].
have : y = f @: aT.
  apply /setP => t. rewrite /y; apply /idP/idP.
move /imsetP => [u []]. move /imageP => [v atv] -> ->.
 apply /imsetP. exists v => //.
move /imsetP => [x xa] ->; apply /imsetP; exists (f x) => //.
apply: codom_f.
rewrite inE //. rewrite inE. apply: codom_f.
Check imageP.
Check image_codom.

move=> sBc /properP[sAB [u Bu nAu]]; rewrite properE preimsetS //=.
by apply/subsetPn; exists (iinv (subsetP sBc  _ Bu)); rewrite inE /= f_iinv.
Qed.

Definition set_surj_fun (aT rT: finType) :=
   (set_surj_fun_on  [set: aT] [set: rT]).

Definition nbsurj n p := set_surj_fun
  #[set f: {ffun `I_n -> 'I_p} ]
   cardinal(set_of_surjections (Bint n)  (Bint p)).
*)
End Partition.

(** Bell numbers *)

Definition Bell n := \sum_(i<n.+1) 'St(n, i).


Lemma Bell0: Bell 0 = 1.
Proof. by rewrite /Bell big_ord_recl big_ord0. Qed.
Lemma Bell1: Bell 1 = 1.
Proof. by rewrite /Bell 2!big_ord_recl big_ord0. Qed.

(* Some values

Lemma Bell2: Bell 2 = 2.
Proof. by rewrite /Bell 3!big_ord_recl big_ord0. Qed.
Lemma Bell3: Bell 3 = 5.
Proof. by rewrite /Bell 4!big_ord_recl big_ord0. Qed.
Lemma Bell4: Bell 4 = 15.
Proof. by rewrite /Bell 5!big_ord_recl big_ord0. Qed.
Lemma Bell5: Bell 5 = 52.
Proof. by rewrite /Bell 6!big_ord_recl big_ord0. Qed.
Lemma Bell6: Bell 6 = 203.
Proof. by rewrite /Bell 7!big_ord_recl big_ord0. Qed.
*)

Definition br m p := \sum_(k<m.+1) 'C(m,k) * 'St(k,p).
(* This is 'St(m.+1,p.+1).  Knuth 6.15 *)
 
Lemma foo1 n: br n n = 'St(n.+1,n.+1).
Proof.
rewrite /br big_ord_recr /= binn 2!stir_nn big1 // => i _.
by rewrite stir_small1 ?muln0.
Qed.


Lemma foo2 n: br n.+1 n = 'St(n.+2,n.+1).
Proof.
rewrite /br 2!big_ord_recr /= binn mul1n  big1; last first. 
   by move => i _; rewrite stir_small1 ?muln0.
by rewrite add0n stirS binSn 2!stir_nn.
Qed.

Lemma foo3 n: br n.+2 n = 'St(n.+3,n.+1).
Proof.
rewrite /br 3!big_ord_recr /= binn mul1n  big1; last first. 
   by move => i ; rewrite stir_small1 ?muln0.
rewrite add0n stirS binS binn mulnDl mul1n -addnA binSn stir_nn muln1.
rewrite addnA addnA stir_Snn (_: 'C(n.+2, n) + 'C(n.+1, 2) = n.+1 *n.+1).
  rewrite - mulnDr stirS stir_nn muln1 stir_Snn //.
by rewrite -addn2 binom_mn_n addn2 binS addnAC addnn - muln2 bin2' bin1 mulSnr.
Qed.


Lemma Bell_rec n: Bell n.+1 = \sum_(k<n.+1) 'C(n,k) * Bell k.
Proof.
suff aux: forall m p, \sum_(k<m.+1) 'C(m,k) * 'St(k,p) = 'St(m.+1,p.+1).
  transitivity (\sum_(i < n.+1)  \sum_(k < n.+1) 'C(n, k) * 'St(k, i)).
    by rewrite /Bell big_ord_recl add0n; apply: eq_bigr =>i _; rewrite aux.
  rewrite exchange_big /=; apply: eq_bigr; move=> [i lin ] _. 
  rewrite - big_distrr /= -(subnK lin) (addnC _ i.+1) big_split_ord /=.
  by rewrite [X in (_ + X)] big1 ? addn0// => j _;rewrite stir_small1 ?leq_addr.

(* so what ? *)
Abort.


Lemma sum_nbsurj n k:  \sum_(i<k.+1) 'Sj(k,i) * 'C(n,i) = n ^k.
Proof.
move:n; elim:k; first by move => n; rewrite big_ord_recr big_ord0 nbsurj00 bin0.
move => k Hrec n; case:n.
  rewrite expnS mul0n big1 //= => [] [i _] _ /=; case i => //.
  by move => n; have ->: 'C(0, n.+1) = 0 by []; rewrite muln0.
move => n; rewrite expnS - Hrec big_ord_recl  nbsurjn0 mul0n add0n.
transitivity (n.+1 * \sum_(i < k.+1) (('Sj(k, i) + 'Sj(k, i.+1)) * 'C(n, i))).
  rewrite big_distrr; apply: eq_bigr; move => [i lik] _ //=.
  by rewrite nbsurjS addnC mulnAC - mul_bin_diag - mulnA (mulnC _ 'C(n, i)). 
have aux: 'Sj(k, k.+1) = 0 by rewrite - [in k.+1] (addn0 k) nbsurj_small //.
congr (_ * _).
rewrite  [x in _ =  x] big_ord_recl bin0.
have ->: (\sum_(i < k) 'Sj(k, lift ord0 i) * 'C(n.+1, lift ord0 i) =
  \sum_(i < k) 'Sj(k, lift ord0 i) * 'C(n, lift ord0 i)
  + \sum_(i < k.+1) 'Sj(k, lift ord0 i) * 'C(n, i) ).
  rewrite [X in _ + X] big_ord_recr /= aux mul0n addn0 - big_split /=. 
  by apply: eq_bigr; move => i _;  rewrite binS  mulnDr.
rewrite addnA [X in _ = (X + _)] (_: _= \sum_(i < k.+1) 'Sj(k, i) * 'C(n,  i)).
  by rewrite - big_split; apply eq_bigr => i _; rewrite  mulnDl.
by rewrite big_ord_recl bin0.
Qed.


Lemma sum_pow n k:  \sum_(i<n) i ^k =  \sum_(i<k.+1) 'Sj(k,i) * 'C(n,i.+1).
Proof.
elim:n => [| n Hrec].
  rewrite big_ord0 big1 //; case => i Hi _.
  by have ->: 'C(0,i.+1) = 0 by []; rewrite muln0.
rewrite big_ord_recr /= - sum_nbsurj Hrec - big_split //. 
by apply: eq_bigr =>i _ /=;  rewrite  - mulnDr.
Qed.




Lemma F5aux n: \sum_(i<n) i =  'C(n,2).
Proof.
transitivity  (\sum_(i<n) i ^1); first by apply:eq_bigr => //.
rewrite sum_pow ! big_ord_recr  /= big_ord0 mul0n mul1n //.
Qed.

(* Proof by induction is shorter *)
Lemma F5aux2 n: \sum_(i<n) i = 'C(n,2).
Proof.
by elim: n => [| n Hn]; [ rewrite big_ord0 | rewrite big_ord_recr Hn binS bin1].
Qed.

Lemma F6aux n: \sum_(i<n) i ^2 =  'C(n,2) + 2 * 'C(n,3).
Proof.
by rewrite sum_pow 3! big_ord_recr /= big_ord0  mul0n mul1n.
Qed.

Lemma n1bin n: n ^1 = 'C(n,1).
Proof. by rewrite bin1. Qed.

Lemma n2bin n: n ^2 = n * 'C(n,1).
Proof. by rewrite bin1. Qed.


Lemma n3bin n: n ^3 = 'C(n,1) + 6 * 'C(n.+1,3).
Proof.
rewrite -sum_nbsurj 4! big_ord_recr big_ord0 /= mul0n mul1n 2!add0n - addnA.
by rewrite - (mulnDr 6) binS (addnC 'C(n, 2)).
Qed.

Lemma n4bin n: n ^4 =  n* 'C(n,1) +  6 * n*'C(n.+1,3) .
Proof. by rewrite (mulnC 6) - mulnA - mulnDr - n3bin expnS. Qed.

Lemma n5bin n: n ^5 =  'C(n,1) + 30 * 'C(n.+1,3) +  120 * 'C(n.+2,5).
Proof. 
rewrite -sum_nbsurj 6! big_ord_recr big_ord0 /= mul0n mul1n 2!add0n.
rewrite (mulnDl 30 120) - 5!addnA (addnA (_ * 'C(n, 2))) -(mulnDr 30 'C(n, 2)).
rewrite (addnC 'C(n, 2)) - binS -(mulnA 120 2).
congr (_ + (_ + _)).
rewrite - (mulnDr 120 (2 * 'C(n, 4))) - mulnDr; congr (120 * _).
by rewrite addnC 3!binS -2!addnA (addnA 'C(n,4)) addnn mul2n addnCA.  
Qed.

Lemma n6bin n: n ^6 =  n*'C(n,1) + 30 * n* 'C(n.+1,3) +  120 *  n*'C(n.+2,5).
Proof. 
by rewrite (mulnC 120) (mulnC 30) - 2! mulnA - 2!mulnDr - n5bin expnS. 
Qed.


Lemma F7aux n: \sum_(i<n) i ^3  = 'C(n, 2) +  6 * 'C(n, 3) +  6 * 'C(n, 4).
Proof.
by rewrite sum_pow 4! big_ord_recr /= big_ord0 add0n nbsurjn0 mul0n add0n mul1n.
Qed.

Lemma F8aux n: \sum_(i<n) i ^4 
 = 'C(n, 2) + 14 * 'C(n, 3) + 36 * 'C(n, 4)  + 24 * 'C(n, 5).
Proof.
by rewrite sum_pow 5! big_ord_recr /= big_ord0  mul0n mul1n.
Qed.

Lemma F9aux n:  \sum_(i<n) i ^5 =
  'C(n, 2) + 30 * 'C(n, 3) + 150 * 'C(n, 4)  + 240 * 'C(n, 5)
   + 120 * 'C(n, 6).
Proof.
by rewrite sum_pow 6! big_ord_recr /= big_ord0 mul0n  mul1n.
Qed.


(* This is much slower (5s including Qed, instead of 1s)
Lemma F10aux n:  \sum_(i<n) i ^6 =
  'C(n, 2) + 62 * 'C(n, 3) + 540 * 'C(n, 4)  + 1560 * 'C(n, 5)
   + 1800 * 'C(n, 6) + 720 * 'C(n, 7).
Proof. by rewrite sum_pow 7! big_ord_recr /= big_ord0 mul0n mul1n. Qed.
*)

Lemma F10aux n:  \sum_(i<n) i ^6 =
  'C(n, 2) + (31 *2) * 'C(n, 3) + (90 * 6) * 'C(n, 4)  + (65 * 24) * 'C(n, 5)
   + (15 * 120) * 'C(n, 6) + 720 * 'C(n, 7).
Proof. by rewrite sum_pow 7! big_ord_recr /= big_ord0 mul0n mul1n. Qed.

Lemma F11aux n:  \sum_(i<n) i ^7 =
  'C(n, 2) + (63 * 2) * 'C(n, 3) + (301 * 3`!) * 'C(n, 4)  
  + (350 * 4`!) * 'C(n, 5) + (140 * 5`!) * 'C(n, 6) 
  + (21 * 6`!) * 'C(n, 7)  + 7`! * 'C(n, 8).
Proof. by rewrite sum_pow 8! big_ord_recr /= big_ord0 mul0n mul1n. Qed.


Definition U_nkbin n k := 'C(n+k,k.*2.+2) + 'C((n+k).+1,k.*2.+2).
Definition T_nkbin n k := 'C(n+k,k.*2.+1) + 'C((n+k).+1,k.*2.+1).

Lemma UT_nkbin n k:  T_nkbin n k.+1 + U_nkbin n.+1 k =  T_nkbin n.+1 k.+1.
Proof.
rewrite  /T_nkbin /U_nkbin !addSn ! addnS doubleS addnCA -addnA addnA -!binS. 
by congr (_ + _); rewrite addnC - binS.
Qed.


Lemma U_nkbin_pr n k : n * 'C(n+k,k.*2.+1) =  (k.+1) * (U_nkbin n k).
Proof.
rewrite /U_nkbin (binS _ k.*2.+1) addnA addnn mulnDr.
rewrite -(mul2n 'C(_,_)) mulnA mulSnr muln2 addn2 - mul_Sm_binm_2 - mulnDl.
rewrite - {2} addnn -addnS subnDA addnK -addnn - addSn.
by case (leqP k.+1 n) => h; rewrite ?(subnK h) // bin_small ? ltn_add2r ?muln0. 
Qed.

Lemma T_nkbin_pr n k : n.*2.+1 * 'C(n+k,k.*2) =  (k.*2.+1) * (T_nkbin n k).
Proof.
rewrite /T_nkbin binS addnA addnn - (muln2 'C(_, _)) mulnDr mulnA.
rewrite - mul_Sm_binm_2 (mulnC _ 2) mulnA - mulnDl addnS -{3} (mul2n k).
rewrite - mulnDr -(addnn k)  subnDA addnK - mul2n.
case (leqP k n) => h;  rewrite ?(subnK h) // bin_small ? ltn_add2r ?muln0 //.
Qed.


Lemma n2bin' n: n ^2 = U_nkbin n 0.
Proof. rewrite  n2bin -(mul1n (U_nkbin n 0)) - U_nkbin_pr addn0 //. Qed.

Lemma n4bin' n: n ^4 = (U_nkbin n 0) +  12 * (U_nkbin n 1). 
Proof. 
rewrite  n4bin  -(mul1n (U_nkbin n 0)) -(mulnA 6 2) - 2! U_nkbin_pr.
by rewrite mulnA addn0 addn1.
Qed.

Lemma n6bin' n: n ^6 = (U_nkbin n 0) + 60* (U_nkbin n 1)+ 360 * (U_nkbin n 2). 
Proof. 
rewrite n6bin  -(mul1n (U_nkbin n 0)) -(mulnA 30 2)  -(mulnA 120 3). 
by rewrite - 3! U_nkbin_pr 2! mulnA addn0 addn1 addn2.
Qed.

Lemma sn2bin n: \sum_(i<n.+1) i ^2 = T_nkbin n 1.
Proof.
by rewrite F6aux /T_nkbin mul2n - addnn addnCA (addnC 'C(n.+1, 2)) - binS addn1.
Qed.

Lemma sn4bin' n: \sum_(i<n.+1) i ^4 = (T_nkbin n 1) +  12 * (T_nkbin n 2). 
Proof. 
elim: n => [| n Hrec];first by rewrite big_ord_recl big_ord0 //.
rewrite big_ord_recr /= Hrec n4bin'.
by rewrite addnCA - addnA - mulnDr addnA (addnC (U_nkbin _ _)) 2!UT_nkbin. 
Qed.

Lemma sn6bin' n: 
  \sum_(i<n.+1) i ^6 = (T_nkbin n 1) + 60 * (T_nkbin n 2) + 360 * (T_nkbin n 3).
Proof. 
elim: n => [| n Hrec];first by rewrite big_ord_recl big_ord0 //.
rewrite big_ord_recr /= Hrec n6bin' addnCA - 2!addnA - mulnDr UT_nkbin.
rewrite (addnA ( _ * _)) (addnCA ( _ * _)) - mulnDr (addnC _ (T_nkbin n 2)).
by rewrite 2!addnA (addnC _ (T_nkbin n 1))  2!UT_nkbin.
Qed.

End Stirling.



Lemma F1a n: \sum_(i<n) 1 = n.
Proof.
by rewrite big_const_ord //; elim:n => // h Hrec; rewrite iterS Hrec add1n.
Qed.

Lemma F1_aux n: \sum_(i<n) 1 = 'C(n,1).
Proof. by rewrite F1a bin1. Qed.


Lemma F5 n: (\sum_(i<n.+1) i) * 2 = n * (n.+1).
Proof. by rewrite F5aux bin2'. Qed.

Lemma F6 n: (\sum_(i<n.+1) i ^ 2 ) * 6 = n * (n.+1) * (2*n +1).
Proof.
elim: n; first by rewrite big_ord_recl big_ord0 //.
move => n Hrec;rewrite  big_ord_recr /=  mulnDl Hrec. 
rewrite expnS expn1 (mulnC n) -!mulnA - mulnDr; congr (_ * _).
rewrite mulnDr muln1  - (add2n n) - (addn1 n) ! mulnDl mul1n.
rewrite 3!mulnDr (mulnA 2) (mulnC 4) -(addnA (n * 4)) (addnAC _ 6).
by rewrite addnA -mulnSr - 2!mulnDr addnCA - addnA  addSnnS.
Qed.

(* Alternate proof, a bit shorter *)
Lemma F6' n: (\sum_(i<n.+1) i ^ 2 ) * 6 = n * (n.+1) * (n.*2.+1).
Proof.
rewrite F6aux mulnDl mulnAC  (_: 2 * 6 = 4 * 3) //  (_: 6 = 2 * 3) //. 
rewrite mulnA bin2' - (mulnA 4) - mul_bin_diag mulnCA (mulnC 4); case: n => // n.
rewrite  (_: 4 = 2 * 2) // (mulnA _ 2) bin2' (mulnC n) -(mulnA _ n) mulnA.
by rewrite (mulnC  n.+2) - mulnDr - muln2 (mulSn _ 2) addSn.
Qed.


Lemma F7 n: (\sum_(i<n.+1) i ^ 3 ) * 4 = (n * (n.+1)) ^2.
Proof.
elim: n; first by rewrite big_ord_recl big_ord0.
move => n Hrec;rewrite  big_ord_recr /=  mulnDl Hrec.
rewrite (expnD n.+1 2 1) mulnC 2 !expnMn expn1 -mulnA -mulnDr. 
by rewrite - (addn2 n) sqrnD mulSn (mulnC 2) - mulnA -addnA.
Qed.


Lemma F7b n: (\sum_(i<n.+1) i ^ 3 )  = 'C(n.+1,2) ^2.
Proof. by rewrite F7aux - addnA - mulnDr (addnC 'C(n.+1, 3)) - binS F7a. Qed.


Lemma F8 n: (\sum_(i<n.+1) i ^ 4 ) * 30 = 
   n * (n.+1) * (n.*2.+1) * (3*n*n + 3*n -1).
Proof.
have  pa: (24 * 30 = (36 * 4) *5) by done.
have  pb: (36 * 30 = (90 * 3) *4) by done.
have  pc: (14 * 30 = (70 * 2) *3) by done.
have  pd: (30 = 2 * 15) by done.
rewrite F8aux 3! mulnDl mulnAC pc (mulnAC 36) pb  (mulnAC 24) pa  {1} pd.
rewrite - (mulnA _ 3) - (mulnA _ 4) - (mulnA _ 5) - 3! mul_bin_diag /=.
rewrite (mulnCA (_ *4)) (mulnCA (90 * 3))  (mulnCA (70 * 2)) (mulnA _ 2) bin2'.
rewrite (mulnC n) - mulnA - 3! mulnDr -5!mulnA; congr (_ * _); case:n => //n.
rewrite -  3! mul_bin_diag (mulnCA 70) (mulnCA 90) (mulnCA 36) - 3! mulnDr.
congr (_ * _); case:n => // n.
rewrite bin1 (_: 90 = 45 *2) // [in 36 * _]  (_: 36 = (6 * 2) * 3) //. 
rewrite - (mulnA _ 2) - (mulnA _ 3) - 2! mul_bin_diag /=  bin1  (mulnCA (6 * 2)).
case:n => // n;rewrite - (mulnA 6) -mul_bin_diag /= bin1 mulnCA -addnA -mulnDr. 
rewrite (mulnC _ n) (mulnA 6) - mulnDl mulnCA.
rewrite -(addnA 24) (addnC 21) (mulnAC 2 3) - (mulnDl (2 * n) 7 3).
rewrite mulnDl addnA (mulnC n.+2) (mulnA 24) - (addnA 15) - mulnDl. 
rewrite (mulnS 24) addnA -(addnA 10 84) (mulnAC 2 12) (addnC 84).
rewrite - (mulnDl (2 * n) 7)  mulnDl addnA (addnC 15) 2!mulnSr.
rewrite  (mulnAC 2 5) - (addnA _ _ 15) - (addnA _ 10) - (mulnDl (2 * n) 7 5).
rewrite - mulnA  - mulnA - 2! mulnDr; congr (_ * _).
   by rewrite addnS - mul2n 3!mulnSr - 2!addnA //.
rewrite {2} (mulnSr 3) addnA (addnS _ 2) subn1 (succnK) -mulnA - addnA.
rewrite - (addnA 2 (3 * 1)) - (mulnA 3 4) - 3!mulnDr addnC. 
rewrite (mulnDl 2 2) - addnA -mulnDl add2n mul2n -addnn addnA addnCA.
by rewrite add1n -addnA - mulnS (addnC _ n.+2).
Qed.


Lemma F9 n: (\sum_(i<n.+1) i ^ 5 ) * 12 = 
   n * n * (n.+1) * (n.+1)  * (2*n*n + 2*n -1).
Proof.
have  pa: (120 * 12 = (48 * 5) *6) by done.
have  pb: (240 * 12 = (144 * 4) *5) by done.
have  pc: (150 * 12 = (150 * 3) *4) by done.
have  pd: (30 * 12 = (60 * 2) *3) by done.
have  pe: (12 = 2 * 6) by done.
rewrite F9aux 4!mulnDl mulnAC pd (mulnAC 150) pc (mulnAC 240) pb.  
rewrite  (mulnAC 120) pa {1} pe (mulnA _ 2) bin2' - (mulnA _ 3) - (mulnA _ 4). 
rewrite - (mulnA _ 5)  - (mulnA _ 6) - 4! mul_bin_diag {pa pb pc pd pe}.
rewrite (mulnCA (_ *5)) (mulnCA (_ * 4))  (mulnCA (_ * 3)) (mulnCA (60 * 2)).
rewrite (mulnC n) - mulnA - 4! mulnDr (mulnAC n n) (mulnC n n.+1) - 7!mulnA. 
congr (_ * _); case:n => // n;  rewrite - 4! mul_bin_diag. 
rewrite (mulnCA 60) (mulnCA 150) (mulnCA 144) (mulnCA 48)  - 4! mulnDr.
rewrite {2} (mulnSr 2 n) (addnA _ 1 1) addnA addnK -3 !addnA.
have ->: (2 * n.+1 * n.+1 + (2 * n + 1)) = (2* n +6) *n +3.
   rewrite - mulnA mulnSr mulnDr mulnA  mulnSr addnA addnAC - (addnA _ _ 1). 
   by rewrite addnAC - mulnDl -2!addnA addnA  - mulnDl -addnA.
have ->: n.+1 * (n.+2 * ((2 * n + 6) * n + 3)) =
   6 + n * (n.+1 * (n.+2) * (2*n +6) + 3* (n+3)).
  rewrite  3!mulnDr 3!mulnA mulnC addnCA (mulnCA _ 3) - (mulnDr 3 2).
  by rewrite (mulnC 3) {2} mulSn -{2} add2n -{2} addn2 -(addnA 2) -mulnS -addnS.
congr (_ * (6 + _)); case:n => // n.
have ->: n.+2 * n.+3 * (2 * n.+1 + 6) + 3 * (n.+1 + 3) =
    60 + n * (2*n*n + 18 * n + 55 ).
  rewrite (addSn n 3) - addnS (mulnDr 3) addnA (mulnSr 2 n) -(addnA _ 2).
  rewrite mulnDr - {3} (addn2 n) mulnDl - {3} (addn3 n) (mulnDr 2). 
  rewrite (mulnC 2) addnA - mulnDr mulnDl addnA mulnC - 2!mulnA.
  rewrite - mulnDr addnAC addnC -addnA addnA mulnC - mulnDr addnC.
  congr (60 + (n * _)); rewrite - (addn3 n) - addnA mulnDl (mulnC n 8).
  rewrite -(addn2 n) mulnA mulnDr (mulnAC 2 _ 3) (mulnDr 6) addnC. 
  rewrite (addnA _ (6 * n)) -mulnDl mulnDr (addnCA _ _ 40)  2!addnA.
  by rewrite  -2!mulnDl -3!addnA (addnCA 8) (mulnC 2).
rewrite - (mulnA 75 2) - (mulnA 12 4) - (mulnA 48 3) - 3! mul_bin_diag bin1.
rewrite mulnC (mulnCA  75) (mulnCA 48) (mulnCA 12) - 3! mulnDr.
congr (_ * (60 + _)).
case:n => // n; rewrite - (mulnA 24 2) - (mulnA 4 3) - 2! mul_bin_diag bin1.
rewrite mulnCA  (mulnCA 4) mulnC - 2!mulnDr; congr (_ * _).
transitivity (75 +((22 + 2 * n) * n)).
  congr (_ + _); case:n => //n; rewrite - (mulnA 2 2) - mul_bin_diag !bin1.
  by rewrite (mulnC _ n)  mulnA -mulnDl - (addnA 22 2)  (mulnS 2 n).
rewrite (mulnSr 18 n) - 2!addnA addnCA addnA 2! mulnSr (addnA (18 * n)).
rewrite -mulnDl {1} (addnC _ 2) (addnA 18) (addnA _ _ 2)  -mulnDl.
by rewrite -addnA addnC addnAC. 
Qed.

Lemma F9' n (a := 'C(n.+1,2)): (\sum_(i<n.+1) i ^ 5 ) * 3 = a * a * (4*a -1).
Proof.
apply /eqP; rewrite - (eqn_pmul2r (ltn0Sn 3)) - mulnA F9; apply /eqP.
rewrite (mulnAC n) - (mulnA _ n) - mulnDl - mulnSr - (mulnA 2). 
rewrite (mulnC _ n) - bin2' -/a  (mulnC _ 2) (mulnA 2 2) (mulnC _ 4).
by rewrite - (mulnA 2) (mulnCA a 2) mulnA - mulnA.
Qed.


Lemma F12 n: \sum_(i<n)  (i.*2.+1) = n ^2.
Proof.
elim: n; first by rewrite big_ord0.
move => n Hrec;rewrite  big_ord_recr /=  Hrec.
rewrite - (addn1 n) sqrnD -addnA; congr (_ + _).
by rewrite muln1 mulnC add1n muln2.
Qed.


Lemma F13' n: \sum_(i<n) (i.*2.+1)^2 = 8 * 'C(n.+1,3) + 'C(n,1).
Proof.
elim :n => //; first by rewrite big_ord0 bin0n.
move => n Hrec; rewrite big_ord_recr Hrec  /= (binS (n.+1))  mulnDr !bin1.
rewrite addnAC -{4} (add1n n)  addnA - (addnA _ _ 1); congr (_ + _ + _).
rewrite -(mulnA 4 2) -mul_bin_diag bin1 -addn1 sqrnD - !mulnn !muln1 addnAC.
by rewrite - mulnDl mulnA (mulnAC 2 2) - mulnA (mul2n n) mulnSr mul2n.
Qed.

Lemma F13 n: (\sum_(i<n)  (i.*2.+1)^2) * 3 =  n * (n ^2 * 4 - 1).
Proof.
rewrite F13'; case: n => //n. 
rewrite bin1  mulnDl mulnAC - mulnA - mul_bin_diag/= (mulnC n.+2).
rewrite - (mulnA 4 2) (mulnA 2) - mul_bin_diag /=  bin1 -mulnA (mulnC 4) - mulnA.
rewrite - mulnDr; congr (_ * _); rewrite -addn1 mulnDr mulnDl muln1.
by rewrite - mulnn mulSnr mulnDl (mulSnr n 4) (addnA _ 3 1) !addnA addnK.
Qed.

(* direct proof is longer *)

Lemma F13direct n: (\sum_(i<n)  ((i*2).+1)^2) * 3 =  n * (n ^2 * 4 - 1).
Proof.
elim: n; first by rewrite big_ord0.
move => n Hrec;rewrite  big_ord_recr /= mulnDl Hrec {Hrec}.
have aux: forall m, (m.+1) ^2 *4 - 1 = m^2 *4 + m * 8 + 3.
   move => m; rewrite -(addn1 m) sqrnD muln1 exp1n mulnDl.
   rewrite mulnDl mul1n - mulnAC addnAC - (mulnC m) (_ : 2 * 4 = 8)  //.
   by rewrite -(addn1 3) addnA addn1 subn1 -pred_Sn.
have aux2: forall m, (m ^2) *4 -1 = ((m * 2).+1) * ( (m * 2).-1).
  case => [// | m].
  rewrite aux - (addn1 m) mulnDl mul1n - addnS addn2 -pred_Sn -(addn1 (m*2)).
  rewrite mulnDl (mulnC 3)  mulnDr mulnDl mulnAC // addnA.
  congr (_ + _);rewrite - addnA ; congr (_ + _); rewrite -!mulnA //- mulnDr.
  done.
have aux3: forall m, (m.+1 * 2).-1 = (m* 2).+1.
  by move => m;rewrite -(addn1 m) mulnDl mul1n addn2 -pred_Sn.
rewrite aux2 aux2 aux3.
rewrite mulnCA expnS expn1 -mulnA - mulnDr.
symmetry; rewrite mulnA mulnC; congr(_ * _).
case: n => [// | n].
rewrite aux3.
have ->: (n.+1 * 2).+1 * 3 = (1* (n * 2).+1) + n*4 + 8.
  rewrite mul1n -(addn1 n) mulnDl -addnS mulnDl mul1n.
  rewrite - (addn1 (n * 2)) addnAC -addnA -addnA (addnA 1 8) add1n.
  by rewrite addnCA - mulnDr addnC -mulnA. 
symmetry; rewrite  addnA addnA  -mulnDl addn1 -addnA.
have ->: (n * 4 + 8) = n.+2 * 4 by rewrite -(addn2 n) mulnDl.
rewrite -mulnDr; congr (_ * _).
by rewrite addSn - (addn2 n) mulnDl.
Qed.

(* tentative proof.

Fixpoint cfn2_rec n m :=
     match n, m with 
   | n'.+1, m'.+1 => m *m *cfn2_rec n' m + cfn2_rec n' m'
  | 0, 0 => 1
  | 0, _.+1 => 0
  | _ .+1, 0 => 0
  end.

Definition cfn2 := nosimpl cfn2_rec.

Notation "''U' ( n , m )" := (cfn2 n m)
  (at level 8, format "''U' ( n ,  m )") : nat_scope.

Lemma foo n m:  
   n ^ (m.*2.+1) = \sum_(j<m.+1) (j.*2.+1)`! * 'U(m.+1,j.+1) * 'C(n+j, j.*2.+1).
Proof.
case m.
  by rewrite n1bin big_ord_recr big_ord0 /= add0n muln1 mul1n addn0 //.
case.
  rewrite n3bin 2! big_ord_recr big_ord0 /= addn1 add0n  addn0 mul1n //.
case.
  rewrite n5bin 3! big_ord_recr big_ord0 /= addn1 addn2 add0n  addn0 mul1n //.
case.
  rewrite 4! big_ord_recr big_ord0 /= addn1 addn2 addn3 add0n  addn0 mul1n //.
  transitivity ('C(n,1) + 126 * 'C(n.+1,3) +  
     1680 * 'C(n.+2,5) +  5040 * 'C(n.+3,7)). 
admit.
  done.
admit.
Qed.

*)

Lemma exp3_addn a b:  (a+b) ^3 =  a^3 + a^2 *b *3 + a*b^2 * 3 + b^3. 
Proof.
rewrite expnS sqrnD mulnDl 4!mulnDr.
have ->: a * (2 * (a * b)) =  a^2 *b *2.
  by rewrite -mulnA -mulnA (mulnA a b 2) (mulnC 2).
have ->:  b * (2 * (a * b)) =  a * b ^ 2 * 2.
  by rewrite mulnC - mulnA (mulnC 2) mulnA.
rewrite -expnS -expnS (addnAC _  (b^3)) addnA; congr (_ + _).
rewrite - 3 !addnA; congr (_ + _).
rewrite addnC addnA -addnA (mulnC b); congr (_ + _).
  by rewrite - (addn1 2) mulnDr muln1. 
by rewrite - (addn1 2) mulnDr muln1.
Qed.

Lemma exp3_addn1 a:  (a.+1) ^3 =  a^3 + a^2 *3 + a * 3 + 1.
Proof. by rewrite -addn1 exp3_addn !muln1. Qed.

Lemma F14 n: (\sum_(i<n)  ((i*2).+1)^3) =  n^2 * (n ^2 * 2 - 1).
Proof.
elim: n; first by rewrite big_ord0.
move => n Hrec;rewrite  big_ord_recr  Hrec /= {Hrec}.
have aux:forall m,  (m.+1 ^ 2 * 2 - 1) = m^2 *2 + m * 4 +1.
   move => m; rewrite - addnA - (addn1 m) sqrnD  mulnDl.
   rewrite mulnDl addnAC muln1 mul1n mulnAC addn2 subn1 -pred_Sn.
   by rewrite -addnS addn1 (mulnC _ m).
case: n => [// | n].
rewrite aux aux.
rewrite -addnA mulnDr -addnA.
rewrite -(addn2 n) sqrnD -addnA -addnA mulnDl (mulnDr (n^2)).
rewrite -addnA mulnCA; congr (_ + _).
set m := n.+1.
have ->:  (2 ^ 2 + 2 * (n * 2)) = 4 * m.
   by rewrite /m mulnC -(add1n n) mulnDr - mulnA mulnC.
rewrite  (mulnDr (4 * m)).
have ->: 4 * m * (m ^ 2 * 2) = (m * 2)^3.
   rewrite expnMn -mulnA (mulnA m) mulnC  -mulnA //.
rewrite exp3_addn1 addnC [in X in _ = X] addnC -4! addnA; congr (_ + _).
have ->:  (m * 2) ^ 2 * 3  = m^2 * 12 by rewrite expnMn -mulnA.
have ->: 4 * m * (m * 4 + 1) = m ^2 * 12 + ( m ^2 * 4 + m * 4).
  rewrite addnA (mulnC 4) mulnDr muln1; congr (_ + _).
  rewrite -(expnD (m * 4) 1 1) add1n expnMn (_: 4 ^2 = 12 + 4) //. 
  by rewrite mulnDr.
rewrite -addnA; congr (_ + _).
rewrite mulnDr mulnDr [in X in _ = X] addnC -addnA.
rewrite addnC (addnC 1) -addnA -addnA.
have r1:  m^2 * 4 =  n * m * 4 + m*4.
  rewrite -mulnDl; congr (_ * _).
  by rewrite  expnS expn1 {1} /m -(addn1 n) mulnDl mul1n.
have ->:  m ^ 2 * (n * 4) = n^2 * (m*4) + n * m *4.
  rewrite mulnAC (mulnC n 4) mulnA r1 mulnC mulnDr ! mulnA.
  by congr (_ + _); rewrite  -(mulnA 4) mulnC.
rewrite -addnA; congr (_ + _).
rewrite muln1 muln1  (addnCA (n^2)) r1 -addnA; congr (_ + _).
rewrite addnA addnCA.
have ->: (m * 4 + m * 4 = m * 2 + m * 2 * 3) by rewrite - mulnA - !mulnDr.
rewrite addnA; congr (_ + _).
rewrite /m - (addn1 n) sqrnD -addnA -addnA; congr (_ + _).
rewrite !muln1 mulnDl mulnC addnCA; congr (_ + _).
Qed.


Lemma F22 n: \sum_(i<n) i `! * i = n `! .-1.
Proof.
elim: n; first by rewrite big_ord0.
move => n Hrec;rewrite  big_ord_recr /=  Hrec {Hrec}.
rewrite factS - {2 3} (prednK (fact_gt0 n)).
by rewrite -(add1n n) mulnDl mul1n addSn - pred_Sn mulnC.
Qed.



Lemma F23 n m: \sum_(i<m) 'C(n+i, n) = 'C(n+m, n.+1).
Proof.
elim: m; first by  rewrite big_ord0  bin_small // addn0 //.
by move => m Hrec;rewrite  big_ord_recr /=  Hrec - binS addnS.
Qed.


Lemma F24_a n: n > 0 ->
  \sum_(i<n) ( 'C(n, i.*2)) = \sum_(i<n) ('C(n, i.*2.+1)).
Proof.
case n; [by rewrite ltn0 | move => m _].
rewrite big_ord_recl bin0.
rewrite [X in 1 + X] (_:_ = \sum_(i < m) ('C(m, i.*2.+2) + 'C(m, i.*2.+1))) //.
transitivity (\sum_(i < m.+1) ('C(m, i.*2.+1) + 'C(m, i.*2))); last by [].
rewrite big_split big_split /= addnA addnC; congr ( _  + _).
  rewrite big_ord_recr /= bin_small ?addn0 // ltnS -addnn; apply: leq_addr.
rewrite big_ord_recl bin0 //.
Qed.


Lemma F24_b (n: nat): n > 0 ->
  \sum_(i<n.+1 | ~~ odd i) ( 'C(n, i)) = \sum_(i<n.+1 | odd i) ('C(n, i)).
Proof.
move => np.
rewrite [X in _ = X] (_: _ = \sum_(i < n.*2.-1 | ~~ odd i) 'C(n, i)).
  rewrite big_mkcond [in X in _ = X ]  big_mkcond /=.
  move: np; case :n => [// | n _]. 
  case: n => [|m]; first  by rewrite 3! big_ord_recl 2! big_ord0 /=.
  have -> : (m.+2).*2.-1 = m.+3 + ( (m.+2).*2.-1 - m.+3).
    symmetry;apply: subnKC; rewrite 2! doubleS -pred_Sn 3! ltnS.
    rewrite -addnn; apply : leq_addr.
  rewrite big_split_ord /=  [in X in _ = _ + X] big1 ?addn0 //.
  move => i _; rewrite bin_small ? if_same //.
  by rewrite 3!addSn 3! ltnS leq_addr.
transitivity (\sum_(i < n.*2 | odd i) 'C(n, i)).
  rewrite big_mkcond [in X in _ = X]  big_mkcond /=.
  move: np; case :n => // m _.
  have -> : (m.+1).*2 = m.+2 + ( (m.+1).*2 - m.+2).
    symmetry;apply: subnKC; rewrite doubleS !ltnS -addnn; apply : leq_addr.
  rewrite big_split_ord /= [in X in _ = _ + X] big1 ?addn0 //.
  move => i _; rewrite  bin_small ? if_same //.
  by rewrite addnC  ! addnS ! ltnS;  apply : leq_addl.
transitivity (\sum_(i<n) ('C(n, i.*2.+1))).
   have pa: forall i: 'I_n, i.*2.+1 < n.*2.
     by move =>  [i] hi /=; rewrite  -doubleS leq_double.
   have pb: forall i: 'I_(n.*2), i./2 < n.
     move: np;  case n; move => // m _ [i] hi /=.
     move: hi; rewrite doubleS ltnS ltnS => lin.
     by move: (half_leq lin)  => /=; rewrite uphalf_double.
   have pc: forall i: 'I_n.*2, odd i -> Ordinal (pa (Ordinal (pb i))) = i.
     move => i oi; apply ord_inj => /=. 
     by rewrite -add1n - {2} (odd_double_half (nat_of_ord i)) oi.
   rewrite (reindex_onto (fun i =>  Ordinal (pa i)) _ pc). 
   apply: congr_big => // i; apply /andP; split. 
      by case:i => i lin //=; rewrite odd_double.
   apply /eqP; apply: ord_inj => /=; exact: uphalf_double.
transitivity (\sum_(i < n) 'C(n, i.*2)); first  by rewrite F24_a.
have pa: forall i: 'I_n, i.*2 < n.*2.-1. 
  move: np;  case n; move => // m _ [i] hi. 
  rewrite doubleS ltnS leq_double -ltnS //.
have pb: forall i: 'I_(n.*2.-1), i./2 < n.
  move: np;  case n; move => // m _ [i] hi /=.
  move: hi; rewrite doubleS ltnS ltnS => lin.
  by move: (half_leq lin)  => /=; rewrite half_double.
have pc: forall i: 'I_n.*2.-1, ~~odd i ->  Ordinal (pa (Ordinal(pb i))) = i.
  move => i oi; apply ord_inj => /=. 
  by rewrite  - {2} (odd_double_half (nat_of_ord i)) (negbTE oi).
symmetry;rewrite (reindex_onto  (fun i =>  Ordinal (pa i)) _  pc). 
apply: congr_big => // i;apply /andP; split. 
    by case:i => i lin //=; rewrite odd_double.
apply /eqP; apply: ord_inj => /=; exact: half_double.
Qed.


Lemma pascal11 n: \sum_(i < n.+1) 'C(n, i) = 2 ^ n.
Proof.
by rewrite  (Pascal 1 1 n);  apply: eq_bigr => i _ //; rewrite !exp1n !muln1.
Qed.

Lemma F24 n: n > 0 ->
  \sum_(i<n.+1 | odd i) ( 'C(n, i)) = 2 ^ (n.-1).
Proof.
move => np.
have: \sum_(i < n.+1) 'C(n, i) = 2 ^ (n.-1) * 2.
  by rewrite - expnSr  (prednK np) pascal11.
rewrite  (bigID (fun i : 'I_n.+1 => odd i)) /= (F24_b np).
by move /eqP; rewrite addnn - muln2  (eqn_pmul2r (ltn0Sn 1)); move /eqP.
Qed.

Lemma F25 n: n > 0 ->
  \sum_(i<n.+1 | ~~ odd i) 'C(n, i) = 2 ^ (n.-1).
Proof. by move => np; rewrite (F24_b np) F24. Qed.


Lemma G5_a r t q:
  \sum_(i<r.+1) ( 'C(t+r - i, t) * 'C(q + i, q) ) = 'C(q+t+r+1,r).
Proof.
move: t; elim:r.
 by move => t ; rewrite bin0 big_ord_recl /= big_ord0 ! addn0 subn0 !binn.
move => n H; elim => [|  t H1].
   rewrite addn0 addnAC addn1 - binom_mn_n  - {1} (addn1 q) - addnA add1n - F23.
   by apply: eq_bigr => i _;rewrite bin0 mul1n.
transitivity ( \sum_(i < n.+1) 'C(t.+1 + n - i, t.+1) * 'C(q + i, q)
       + \sum_(i < n.+2) 'C(t + n.+1 - i, t) * 'C(q + i, q)).
  rewrite big_ord_recr  (big_ord_recr (n.+1)) /= !addnK !binn !mul1n addnA.
  congr (_ + _); rewrite - big_split; apply: eq_bigr => i _ /=. 
  rewrite - mulnDl; congr (_ * _); case : i => [j] /=; rewrite ltnS => je.
  by rewrite - 2! addSnnS - (addnBA _ je) - binS  - (addnBA _ je) - addSn.
by rewrite H H1 !addn1 -(addnA q t) -(addSnnS t n) (addnA q) addnC (addnS _ n).
Qed.

Lemma G5_b n p q: p <= n -> q <p ->
  \sum_(q+1 <= k < (n - p + q + 1).+1) ( 'C(n-k, p-q-1) * 'C(k-1, q)) = 'C(n,p).
Proof.
move => pa pb.
rewrite - (bin_sub pa)  - addnA - subnDA addn1.
move: (subnK pb); set r := n - p; set t := p - q.+1 => pc.
have pd : n = q+t+r+1. 
  by rewrite (addnC _ r) - addnA  - (subnK pa) (addnC q) -addnA addn1 pc.
rewrite - {1} (add0n (q.+1)) big_addn big_mkord.
rewrite (subSn (leq_addl r q.+1)) addnK  pd -G5_a.
apply:congr_big => // i _;  congr (_ * _); last by rewrite addnS subn1 addnC.
case i => [m] /=; rewrite ltnS => mr; congr ('C(_, t)).
rewrite - (addnBA t mr)  (addnC q) -addnA -addnA (addnCA q) addn1. 
by rewrite - {1} (subnK mr) - addnA addnA addnK.
Qed.

(* deplacer *)
Lemma F6_aux n: n ^2 = 2 * 'C(n,2)  + 'C(n,1).
Proof.
case: n => // n; rewrite bin2 bin1 succnK mul2n  - mulnn mulnSr.
by move:(odd_double_half (n.+1 * n)); rewrite oddM /= andNb add0n => ->.
Qed.

Lemma F7_aux n:  n ^ 3 = 6 * 'C(n, 3) +  6 * 'C(n, 2) + 'C(n, 1).
Proof.
elim:n => //n Hrec; rewrite - {1} addn1 Pascal 4! big_ord_recr big_ord0 /=.
rewrite !exp1n expn0 expn1 !muln1 add0n /subn /=  bin0 bin1 mul1n Hrec.
rewrite (_: 'C(3, 2) = 3) // !binS !mulnDr bin0 addnA; congr (_ + 1).
rewrite  - 5!addnA (addnC ('C(n, 1))); congr (_ + (_ + (_ + _))).
by rewrite F6_aux mulnDr mulnA bin1 - addnA addnn - mul2n mulnA.
Qed.

Lemma F8_aux n: 
    n ^ 4 = 24 * 'C(n, 4) + 36 * 'C(n, 3) +  14 * 'C(n, 2) + 'C(n, 1).
Proof.
elim:n => //n Hrec; rewrite - {1} addn1 Pascal 5! big_ord_recr big_ord0 /=.
rewrite !exp1n expn0 expn1 !muln1 add0n /subn /=  bin0 bin1 mul1n Hrec.
rewrite !(binS n) 3! mulnDr bin0 addnA;congr (_ + 1).
set a := 24 * 'C(n, 4); set b := 36 * 'C(n, 3).
rewrite - 5! addnA  -(addnA (a + _))  (addnAC a) - (addnA b). 
rewrite (addnCA ( 36 * 'C(n, 2))) - 4! addnA; congr (_ + (_ + (_ + _))).
rewrite (_: 'C(4, 2) = 6) // (_: 'C(4, 3) = 4) //  F7_aux bin1.
rewrite (addnC _  (_ + n)) (addnC (24 * _)) - (addnA n); congr (n + _).
rewrite - addnA mulnDr mulnA - addnA; congr (_ + _).
rewrite F6_aux  2! mulnDr 2! mulnA bin1 - (addnA _  _ (4 * n)) - mulnDl.
by rewrite addnAC addnA - mulnDl - addnA - mulnDl.
Qed.

Lemma F9_aux n: 
    n ^ 5 = 120 * 'C(n, 5) +  240 * 'C(n, 4) + 150 * 'C(n, 3) + 
     30 * 'C(n, 2) + 'C(n, 1).
Proof.
elim:n => //n Hrec; rewrite - {1} addn1 Pascal 6! big_ord_recr big_ord0 /=.
rewrite !exp1n expn0 expn1 !muln1 add0n /subn /=  bin0 bin1 mul1n Hrec {Hrec}.
set a:= 120; set b := 240; set c := 150; set d := 30.
symmetry;rewrite 5!binS  bin0;rewrite addnA; congr (_ + 1).
rewrite -10 ! addnA !mulnDr -addnA;congr (_ + _).
rewrite addnC -2!addnA; congr (_ + _); rewrite addnC -3!addnA; congr (_ + _).
rewrite addnC -3!addnA; congr (_ + _);rewrite addnC -3!addnA; congr (_ + _).
rewrite F8_aux 3! mulnDr 3!mulnA -3!addnA; congr (_ + _).
rewrite (addnCA (5 * 'C(n, 1))) (addnCA (5 * 14 * 'C(n, 2)))(_: 'C(5,2) = 10) //.
rewrite F7_aux  2!mulnDr 2!mulnA - 2!addnA (addnA (5 * 36 * 'C(n, 3))).
rewrite - mulnDl {1} (_: c = 10 * 6 + 90) // mulnDl - addnA. 
congr (_ + (_ + _)); rewrite F6_aux bin1.
rewrite (addnC (10 * n))  (_: 'C(5,3) = 10) // (_: 'C(5,4) = 5) //.
rewrite mulnDr mulnA - (addnA _ _ (5 * n)) - mulnDl (addnC (5 * n)).
by rewrite -(addnA _ _ (5 * n)) -mulnDl addnA -mulnDl -addnA -mulnDl.
Qed.



Lemma F36 k l i: 
  (\sum_(j < i.+1) ('C(k, j)  *'C(l, (i - j)))) = 'C(k+l , i).
Proof.
pose f k i :=  (\sum_(j < i.+1) 'C(k, j) * 'C(l, i - j)).
rewrite -/(f k i) ; move: k i.
have fx0: forall k, f k 0 =  'C(k + l, 0).
  by move=> k; rewrite /f big_ord_recl big_ord0 addn0 !bin0 muln1.
have f0x: forall i, f 0 i = 'C(l, i).
  move=> i; rewrite /f big_ord_recl bin0 mul1n big1 ? addn0 ?subn0 //.
suff fxx: forall k i, f (k.+1) (i.+1) = f k i.+1 + f k i.
  by elim  => [//| k h1]; elim => [//| i h2]; rewrite fxx h1 h1 - binS addSn.
move=> k i; rewrite /f big_ord_recl (big_ord_recl (i.+1)) !bin0 !mul1n -addnA.
congr (_ + _); rewrite -big_split /=.
by apply: eq_bigr => j _ ; rewrite - mulnDl. 
Qed.

Lemma F37 n p: p<= n ->
  (\sum_(k < (n-p).+1) ('C(n, k)  *'C(n, p+k))) = 'C(2*n,n-p).
Proof.
move => h; move: (subnK h); set q := n - p; move => <-.
move: (F36 (q+p)(q +p) q);rewrite addnn - mul2n => <-.
apply: eq_bigr; move => [j] /=; rewrite ltnS => jq _.
by rewrite addnC - (@bin_sub (p + q)  (p + j)) ?leq_add2l // subnDl. 
Qed.

Lemma F38 n: \sum_(i<n.+1) 'C(n,i) ^2 = 'C(n.*2, n).
Proof.
rewrite - addnn - (F36 n n n); apply: congr_big => // [[i isn]].
by rewrite expnS expn1 bin_sub //.
Qed.

Lemma F27_a n: \sum_(i < n.+1)  i* 'C(n, i) = n * 2 ^ (n.-1) .
Proof.
elim:n; first by rewrite big_ord_recr big_ord0 mul0n //.
move => n Hrec; rewrite big_ord_recl mul0n add0n /= big_split /=.
have ->: \sum_(i < n.+1) 'C(n.+1, bump 0 i) =
   \sum_(i < n.+1) 'C(n, bump 0 i) +  \sum_(i < n.+1) 'C(n,i).
  rewrite - big_split /=; apply: eq_bigr; move => [i lin] _ //=.
rewrite addnAC pascal11 mulSnr; congr (_ + _).
have ->: n * 2 ^ n = n * 2 ^ n.-1 + n * 2 ^ n.-1.
   by case n => // m /=; rewrite addnn - muln2 expnSr mulnA.
rewrite [X in _ + X] (_ :_ = \sum_(i < n.+1) i*'C(n, bump 0 i) +  n * 2 ^ n.-1).
  rewrite addnA - {2} Hrec;  congr (_ + _);rewrite - big_split /=. 
  rewrite [X in _ = X] big_ord_recl big_ord_recr bin_small //=.
  rewrite mul0n muln0 !addn0 add0n; apply: eq_bigr => i _ /=; rewrite -mulSn //.
by rewrite - Hrec - big_split /=; apply: eq_bigr => i _; rewrite - mulnDr.
Qed.

(* catalan numbers *)

Lemma factSr n : n.+1 `! = n`! * n.+1.
Proof. by rewrite factS mulnC. Qed.


Lemma bin_fact2n_a n : 'C(n.*2, n) * (n`!)^2 = (n.*2)`!.
Proof.  by rewrite - addnn - mulnn - (bin_fact (leq_addr n n)) addnK. Qed.

Lemma bin_fact2n_b n : 0<n -> 'C(n.*2, n.-1) * (n`! * n.+1`!) = (n.*2)`!*n.
Proof.
case: n => // n _ /=.
rewrite factSr mulnAC mulnA. 
by move:(bin_fact (leq_addr n.+2 n)); rewrite addKn - addSnnS addnn => ->.
Qed.

Lemma bin_fact2n_c n :'C(n.*2, n) * (n`! * n.+1`!) = (n.*2)`!*n.+1.
Proof. by rewrite factSr (mulnA n`!) mulnn mulnA bin_fact2n_a. Qed.

Lemma bin_fact2n_d n : 0<n ->  'C(n.*2, n.-1) <= 'C(n.*2, n).
Proof.
move => /bin_fact2n_b ea.
have h: 0 <  (n`! * n.+1`!) by rewrite muln_gt0 !fact_gt0.
by rewrite -(leq_pmul2r h) ea bin_fact2n_c leq_mul2l leqnSn orbT.
Qed.

Lemma bin_fact2n_e n : 0<n -> 
   ('C(n.*2, n) - 'C(n.*2, n.-1)) * n.+1  = 'C(n.*2, n).
Proof.
move => h.
move/eqP:(f_equal2 subn  (bin_fact2n_c n) (bin_fact2n_b h)).
rewrite -mulnBr -mulnBl subSnn muln1 - (bin_fact2n_a n) factS (mulnCA n`!). 
by rewrite mulnn mulnA eqn_mul2r expn_eq0 eqn0Ngt fact_gt0 /= => /eqP.
Qed.

Lemma  bin_fact2n_f n: 0 <n ->  
  'C(n.*2.+2, n.+1) - 'C(n.*2.+2, n) = 'C(n.*2.+1, n.+1) - 'C(n.*2.+1, n.-1).
Proof.
move => h; have eqa:= (prednK h).
by rewrite -{4} eqa binS (binS n.*2.+1) eqa addnC subnDl.
Qed.


Lemma  bin_fact2n_g i: 0 < i ->
  (i.+2) * 'C(i.*2, i) + (3*i.+1) * 'C(i.*2, i.-1)
  = (i.+1) * 'C((i.+1).*2, i.+1).
Proof.
move => h; apply/eqP.
have ha: 0 < (i.+1)`!^2 by rewrite expn_gt0 fact_gt0.
rewrite - (eqn_pmul2r ha) -(mulnA i.+1) (bin_fact2n_a i.+1) mulnDl factS.
rewrite {1} expnMn -mulnA.
rewrite (mulnC (i.+1 ^ 2)) (mulnA _ _ (i.+1 ^ 2)) bin_fact2n_a -(mulnn (_ * _)).
rewrite - {2} factS -(mulnA (i.+1)) mulnACA (bin_fact2n_b h) -(mulnA 3) mulnn.
rewrite (mulnC _ i) mulnACA (mulnC (_ ^ 2)) - mulnDl 2!addSn -mulSn.
rewrite -(mulnA 2 2) 2!mul2n - doubleS - muln2 - mulnA (mulnCA 2) mulnA -factS.
by rewrite - mulnn (mulnA 2) mul2n doubleS mulnA -factSr mulnC.
Qed.

Definition catalan n := 'C(n.*2,n) %/(n.+1).

Lemma catalan0: catalan 0 = 1.
Proof. done. Qed.

Lemma catalan_pos n: 0 < n -> catalan n = 'C(n.*2, n) - 'C(n.*2, n.-1).
Proof.
by rewrite /catalan;move => /bin_fact2n_e {1} <-;rewrite mulnK.
Qed.

Lemma catalan_prop n: n.+1 * catalan n = 'C(n.*2, n).
Proof.
move:(leq0n n); rewrite leq_eqVlt => /orP; case => np.
  by move/eqP:np => <-.
by rewrite -(bin_fact2n_e np) mulnC (catalan_pos np).
Qed.

Lemma catalan_fact n: ((n`!)^2 * n.+1) * catalan n = (n.*2)`!.
Proof. by rewrite -mulnA catalan_prop mulnC bin_fact2n_a.  Qed.

Lemma catalan_rec n: (n.+2) * catalan n.+1 = (n.*2.+1.*2) * catalan n.
Proof.
apply/eqP.  
have ha m: 0 < ((m`!)^2 * m.+1) by rewrite muln_gt0 expn_gt0 fact_gt0 //.
rewrite -(eqn_pmul2l (ha n.+1)) mulnCA catalan_fact mulnA -(eqn_pmul2l (ha n)).
rewrite [in X in _== X] mulnCA catalan_fact doubleS factS - doubleS.
rewrite - muln2 - (mulnA _ 2) mulnCA (mulnC _ n.+2) -2! (mulnA n.+2).
rewrite -(mulnA _ _ (n.*2)`!) - (mul2n (n.*2.+1)) - (mulnA 2) - factS -mulnA.
by rewrite (mulnA n.+1) mulnn (mulnA (n`! ^ 2)) -expnMn  -factSr eqxx.
Qed.


Lemma catalan_SSn n: 0 < n -> 
  catalan n.+1 = 'C(n.*2.+1, n.+1) - 'C(n.*2.+1, n.-1).
Proof.
by move => h; rewrite catalan_pos // doubleS /=  (bin_fact2n_f h). Qed.



Lemma catalan_spec m k (n := (m + k.+1).*2.+1):
   ( 'C(n, m) < 'C(n, m.+2)) &&
   ( (m+ k.*2.+3) * ('C(n, m.+2)-'C(n, m)) == 'C(n.+1, m.+2)* k.*2.+1 ).
Proof.
have hx: m.+2 <= n.
  by rewrite ltnS -addSnnS -addnn -addnA leq_addr. 
have hz:= (leq_trans hx (leqnSn _)). 
set z := 'C(n.+1, m.+2).
suff h: ((m + k.*2.+3) * ('C(n, m.+2) - 'C(n, m)) == z * k.*2.+1).
  have: 0 < z * k.*2.+1 by rewrite muln_gt0 bin_gt0 hz //.
  by rewrite h andbT -{1} (eqP h) muln_gt0 addnS  subn_gt0.
have czp: 0 < (m.+2)`! * (n.+1 - m.+2)`! by rewrite muln_gt0 !fact_gt0.
have cxp: 0< ((m.+2)`! * (n - m.+2)`!) by rewrite muln_gt0 !fact_gt0.
set s := (m + k.*2.+2) * (m + k.*2.+3).
have cyp: 0 < s by rewrite muln_gt0 addnS /= addnS /=.
have eq4: (m + k.*2.+1)`! * s = (m + k.*2.+3)`!.
   by rewrite /s  mulnA !addnS -2!factSr.  
have eq1: (n.+1 - m.+2)`! = (m + (k.+1).*2)`!.
  by rewrite /n addnC -addnn addnACA addnn addnA -2!addnS addnK addnC.
have eq2: (n - m.+2)`! = (m + (k.*2.+1))`!.
  by rewrite /n -addSnnS -addnn addnACA (addnn k) addnAC addSnnS -addnS addnK.
have eq3: n - m = m + k.*2.+3. 
  by rewrite /n - addnn addnACA - addnA addnn -2!addnS addKn.
rewrite - (eqn_pmul2r czp) (mulnAC z) (bin_fact hz) eq1.
rewrite (mulnC _ (_ -_ )) - mulnA (mulnCA _ (m.+2)`!) addnS -factS -addnS.
set t := ((m.+2)`! * ((m + k.*2.+3))`!).
rewrite - (eqn_pmul2r cxp) mulnAC mulnBl (bin_fact hx) eq2.
rewrite -(eqn_pmul2r cyp) mulnAC mulnBl -(mulnA 'C(n, m)) -(mulnA (m.+2)`!) eq4.
rewrite {1} factS factS (mulnA m.+2) - (mulnA (m.+2 * m.+1))  mulnCA -{1}eq3.
rewrite (bin_fact (ltnW (ltnW hx))) (mulnC _ n`!) - mulnBr -/t -4!mulnA.
rewrite (mulnC _ s) {2} /s (mulnC (m + k.*2.+2)) -(mulnA _((m + k.*2.+2))).
rewrite addnS (addnS _ k.*2.+1) - 2!factS - 2!addnS -/t factSr.
rewrite - mulnA (mulnA n.+1); apply/eqP; congr (n`! * (_ * t)).
rewrite /s -4!addSnnS mulnDr mulnDl - addnA mulnSr - addnA addKn addnA.
by rewrite - mulSn mulnC - mulnDl addnA addnn - doubleD addSnnS addSn.
Qed.

Lemma catalan_prod n: (n.+1)`! * catalan n = \prod_(i<n) i.*2.+1.*2.
Proof.
elim:n => [| n Hr]; first by rewrite big_ord0.
by rewrite factSr -mulnA catalan_rec mulnCA Hr mulnC big_ord_recr /=.
Qed.

Lemma catalan_prod2 n: (n.+1)`! * catalan n = 2^n * \prod_(i<n) i.*2.+1.
Proof.
rewrite catalan_prod mulnC; elim:n =>  [| n Hr]; first by rewrite !big_ord0. 
by rewrite 2!big_ord_recr /= Hr mulnAC -(muln2 (n.*2.+1))  expnS - !mulnA.
Qed.

  
Lemma catalan_sum n: catalan n.+1 = \sum_(i<n.+1) catalan i * catalan (n-i).
Proof.
elim:n; first by rewrite big_ord_recr /= big_ord0.
move => n Hr. 
Abort.

Definition Tnk1 n k := 'C(n.*2.-1, n-k) - 'C(n.*2.-1, (n-k).-2).
Definition Tnk2 n k := ('C(n.*2, n-k) * (k.*2.+1)) %/ (n+k+1).

Lemma Tnk2_alt n k: k.+1 <= n ->
  (k.*2.+1)* 'C(n.*2, n-k) = (n+k).+1 * ('C(n.*2, (n-k)) - 'C(n.*2, n-k-1)).
Proof.
move => h; apply/eqP.
have ha: n + k + (n - k) = n.*2 by rewrite -addnA (subnKC (ltnW h)) addnn.
have hb: (n + k).+1 + (n - k - 1) = n.*2.
  by rewrite - subnDA addn1 - addnS - addnA (subnKC h) addnn. 
set A :=  'C(n.*2, n - k).
set B := 'C(n.*2, n - k - 1).
have Av: A = 'C(n.*2, n + k) by rewrite - ha binom_mn_n ha.
have Bv: B = 'C(n.*2, (n + k).+1) by rewrite - hb binom_mn_n hb.
move:(mul_Sm_binm_1 (n- k)  (n+k) ); rewrite addnC ha - Av - Bv mulnBr => <-.
by rewrite - mulnBl (subnBA _ (ltnW h)) addSn -addnA addnn - addnS addKn.
Qed.

Lemma Tnk2_div n k: k <= n ->
  (n + k + 1) * Tnk2 n k = 'C(n.*2, n-k) * (k.*2.+1).
Proof.
rewrite /Tnk2 leq_eqVlt => /orP; case => np.
  by rewrite (eqP np) addnn addn1 mulnK // mulnC.
by rewrite (mulnC _ k.*2.+1) (Tnk2_alt np) addn1 mulKn.
Qed.

Lemma Tnk2_div2 n k: k <= n ->
   (n-k)`! * (n + k + 1)`! * Tnk2 n k = n.*2 `!* (k.*2.+1).
Proof.
move => h.
have hb:  n - k <= n.*2.
  rewrite -addnn; exact: (leq_trans (leq_subr k n)(leq_addr n n)).
rewrite - mulnA addn1 factSr - mulnA - addn1 (Tnk2_div h) 2! mulnA. 
by move:(bin_fact hb); rewrite mulnC (subnBA _ h) - addnn - addnA addKn => ->.
Qed.
  
Lemma Tnk1_eq_Tnk2 n k: k+2 <=n ->  Tnk1 n k =  Tnk2 n k.
Proof.
move => h. 
set m := (n - k).-2.
move:(subnK h); rewrite subnDA subn2 -/m => nv.
have nk2: n - k = m.+2 by rewrite - nv (addnC k) addnA addn2 addnK.
rewrite /Tnk1  /Tnk2 {1 3} nk2 - {1 2 4 5}nv -/m addn2 addnS doubleS /=.
rewrite -addnA addn1 addSn - addnA addnn  doubleS - addnS.
have h1: 0 < (m + k.*2.+3) by rewrite addnS.
apply/eqP; rewrite - (eqn_pmul2l h1).
by move/andP:( catalan_spec m k) => [hh /eqP <-]; rewrite (mulKn _ h1).
Qed.


  
Lemma Tnk2_n0 n:  Tnk2 n 0 = catalan n.
Proof. by rewrite /Tnk2 subn0 muln1 addn0 addn1. Qed.

Lemma Tnk2_nn n:  Tnk2 n n = 1.
Proof. by rewrite /Tnk2 subnn bin0  mul1n addnn addn1 divnn //. Qed.

Lemma Tnk2_Snn n:  Tnk2 n.+1 n = n.*2.+1.
Proof. by rewrite /Tnk2 -{2}add1n addnK bin1  -addnA addn1 addnn mulKn. Qed.

Lemma Tnk2_sum n k: k < n ->
  (n-k)`!*(n+k+2)`! * ((Tnk2 n k) + (Tnk2 n k.+1)) = (n.*2.+1)`! * k.*2.+2.
Proof.
move=> lkn; move:(lkn); rewrite - (subn_gt0) => ha.
have eq3: (n - k) `! =  (n-k) * (n - k.+1)`!
  by rewrite - (prednK ha) factS subnS.
have eq4:= (subnK (ltnW lkn)).
rewrite mulnDr {1} addnS factS (mulnCA) - mulnA (Tnk2_div2 (ltnW lkn)) addnC.
rewrite eq3 - 2!(mulnA (n- k)) addn2 -addnS - (addn1 (_ + _)) (Tnk2_div2 lkn).
rewrite mulnCA (mulnCA _ (n.*2)`!) - mulnDr factSr addn1 -{3} eq4 -addnA.
rewrite addnn -2! addnS mulnDl addnA -mulnDr addSnnS - doubleS addnn.
rewrite (mulnC (k.+1).*2) -(mul2n ((k.+1).*2)) mulnA -mulnDl addnS -(muln2 k).
by rewrite - mulnDl eq4 muln2 mulnA.
Qed.

Definition Cat' n k:= 'C(n+k,n) * (n.+1-k).
Definition Cat n k:= ('C(n+k,n) * (n.+1-k) ) %/ n.+1.

Lemma Cat_rec_aux n k: k <= n ->
  n.+1 * Cat' n.+1 k.+1 = n.+2 * Cat' n k.+1 + n.+1* Cat' n.+1 k.
Proof.
move => h; apply /eqP; rewrite /Cat'.
rewrite mulnCA (mulnCA n.+2) (mulnCA n.+1).
have pp: 0 < n`! * (k.+1)`! by rewrite muln_gt0 !fact_gt0 .
rewrite -(eqn_pmul2r pp) mulnDl -mulnA mulnACA -factS( mulnCA (n.+1)`!) mulnCA.
rewrite - {3} (addKn n.+1 k.+1) (bin_fact (leq_addr k.+1 n.+1)) mulnAC.
rewrite - {4} (addKn n k.+1) (bin_fact (leq_addr k.+1 n)) - mulnA mulnACA.
rewrite - factS (factSr k) (mulnCA _ k`!) (mulnA (n.+1)`!) 2! mulnA mulnA.
rewrite -{6}(addKn n.+1 k) (bin_fact (leq_addr k n.+1)) -2!mulnA -(addSnnS n).
rewrite - mulnDr mulnC addnS factSr - mulnA 2!subSS;apply/eqP; congr muln.
rewrite (subSn (leq_trans h (leqnSn n))) (subSn h) -addSn mulnSr mulnSr.
rewrite addnA 2!(mulSnr _ k) (mulnC _ k) (addnAC _ k) -(addnA _ k) 2!(addnS k).
by rewrite (subnKC h) -2!(addnA  _ _ k) [RHS] addnA - mulnDl.
Qed.

Lemma Cat_dvd n k: k <= n -> Cat' n k = n.+1 * Cat n k.
Proof.
elim: n k; first by move => k; rewrite leqn0 => /eqP ->. 
move => n H; elim; first by rewrite /Cat /Cat' {1}mulnC addn0 subn0 mulnK //.
move => k HH; rewrite ltnS; rewrite leq_eqVlt => /orP; case => np.
  by rewrite (eqP np) /Cat /Cat' subSS addnn subSnn muln1 catalan_prop.
move /eqP: (Cat_rec_aux (ltnW np)); rewrite  /Cat -/(Cat' _ _) (H _ np) mulnCA.
rewrite - mulnDr eqn_pmul2l //  (HH (ltnW (ltn_trans np (ltnSn n)))) - mulnDr.
by move /eqP ->;rewrite mulKn.
Qed.

Lemma Cat_rec n k: k <= n -> Cat n.+1 k.+1 = Cat n k.+1 + Cat n.+1 k.
Proof.
move => h; apply/eqP.
have h':= (leq_ltn_trans h (ltnSn n)).
have ww: Cat' n k.+1 = n.+1 * Cat n k.+1.
  move:h; rewrite leq_eqVlt => /orP; case => np; last by rewrite Cat_dvd.
  by rewrite /Cat /Cat' (eqP np) subnn muln0 div0n muln0.
  move /eqP:(Cat_rec_aux h); rewrite (Cat_dvd h') (Cat_dvd(ltnW h')) ww.
by rewrite mulnCA (mulnCA n.+1) -mulnDr - mulnDr 2!mulnA eqn_pmul2l.
Qed.

Lemma CatnSn n:  Cat n n.+1 = 0.
Proof. by rewrite /Cat subnn muln0 div0n. Qed.

Lemma Catnn n: Cat n n =  catalan n.
Proof. by rewrite /Cat subSnn muln1 addnn //. Qed.

Lemma CatSnn n: Cat n.+1 n =  catalan n.+1.
Proof.  by rewrite - Catnn Cat_rec // CatnSn. Qed.

Lemma bin_subnn k n: k <= n -> 'C(n.*2, n + k) =  'C(n.*2, n - k).
Proof.
move => h; rewrite - bin_sub - addnn ? leq_add2l//.
by rewrite -{4} (subnKC h) addnA addKn.
Qed.

Lemma Cat_alt n k: k<=n -> Cat (n+k) (n-k) = Tnk2 n k.
Proof.
move => h.
rewrite /Tnk2 /Cat (subSn (leq_trans (leq_subr k n) (leq_addr k n))) -addnA.
by rewrite (subnKC h)  (subnBA _ h) - addnA !addnn addKn addn1 bin_subnn. 
Qed.



Fixpoint Mi i j:=
  if i is i.+1 then
    if j is j.+1 then Mi i j + (Mi i j.+1).*2 + Mi i j.+2
    else Mi i 0 + Mi i 1
  else (j==0):nat.



Definition Ni k n := ('C(n+k,n) * (n-k+1)) %/ (n+1).

Lemma aa: Mi  3 1 = 9. done. Qed.

Lemma Mi_rec i j: Mi i.+1 j.+1 = Mi i j + (Mi i j.+1).*2 + Mi i j.+2.
Proof. exact. Qed.
 
Lemma Mi_zero i j : i < j -> Mi i j = 0.
Proof. 
move: i j; elim => [[|j ] | i H [|j  lij]] //.
rewrite ltnS in lij; have lijw := (ltnW lij).
rewrite /= !H // !ltnS //; exact: (leq_trans lijw (leqnSn j)).
Qed.

Lemma Mi_diag i : Mi i i = 1.
Proof. by elim: i => // i H /=; rewrite H !Mi_zero. Qed.

Lemma Mi_subdiag i : Mi i.+1 i = i.*2+1.
Proof. 
elim: i => // i H. 
by rewrite Mi_rec H Mi_diag Mi_zero // addn0 // addnAC -doubleD (addn1 i).
Qed.

Lemma Mi_subsubdiag i : Mi i.+2 i = i.+2* i.*2.+1.
Proof.
elim: i => // i H; rewrite Mi_rec H  Mi_subdiag  Mi_diag !addn1 - addSn.
rewrite mulSn -addSn -doubleS -{1}muln2 -mulnDr add2n -doubleS.
by rewrite - (mul2n (i.+1).*2.+1) -mulnDl addn2.
Qed.

Lemma TMi_eq_Tnk2 i j: j <= i -> Mi i j = Tnk2 i j.
Proof.
elim:i j => [j  | n H [_ |]]; first by rewrite leqn0 => /eqP ->.
  move:(leq0n n); rewrite leq_eqVlt => /orP; case => np.
    by rewrite - (eqP np).
  move:(Tnk2_sum np)(Tnk2_div2 (leq0n n.+1)).
  rewrite !subn0 !addn0 muln1 muln2 addn1  addn2 => sa sb.
  have pp: 0 < n.+1`!* (n.+2)`! by rewrite muln_gt0 !fact_gt0.
  apply/eqP;rewrite /=  H // (H _ np) -(eqn_pmul2l pp) sb factS -2! mulnA.  
  by rewrite (mulnA n`!) sa - mul2n mulnA muln2 - factS.
move => k kp.
rewrite ltnS in kp.
move:(kp);rewrite leq_eqVlt => /orP; case => kp1.
  by rewrite (eqP kp1) Mi_diag Tnk2_nn.
move:(kp1);rewrite leq_eqVlt => /orP; case => kp2.
  by rewrite (eqP kp2) Mi_subdiag Tnk2_Snn addn1.
rewrite /= (H _ kp) (H _ kp1) (H _ kp2) - addnn addnA - addnA; apply/eqP.
have pp: 0 < (n-k)`! * (n+k.+1+2)`! by rewrite muln_gt0 !fact_gt0.
have ea: (n - k)`! = (n-k) * (n - k.+1)`!.
  rewrite - subn_gt0 in kp1; have eb :=(prednK kp1). 
  by rewrite -{1} eb factS eb subnS. 
have eb:(n + k.+1 + 2)`! = (n+k.+3)* (n + k + 2)`!. 
  by rewrite 2!addn2 factS !addnS.
rewrite - (eqn_pmul2l pp) mulnDr {1} eb mulnCA - mulnA  (Tnk2_sum kp1).
set t := _ * _.
rewrite {1} ea -mulnA - mulnA (mulnA (n - k.+1)`!) (Tnk2_sum kp2).
set s := _ * _.
have ->: t + s = (n.*2.+2)`! * (k.*2.+3).
  rewrite /t/s mulnCA (mulnCA (n-k)) -mulnDr -{2} (subnK kp) - addnA !addnS.
  rewrite addnn -3!addnS (addnC (n - k)) mulnDl -addnA -mulnDr -addSnnS addnn.
  rewrite -(muln2  (k.*2.+3)) mulnCA -mulnDr 2!addSn -{2} (muln2 k) -mulnDl.
  by rewrite (subnKC kp) muln2 mulnCA - factSr mulnC.
by rewrite - (@Tnk2_div2 n.+1 k.+1) ? ltnS // subSS addSn addn1 addn2.
Qed.

Lemma Mij_n0 n: Mi n 0 = catalan n.
Proof. by rewrite  TMi_eq_Tnk2 // Tnk2_n0. Qed.


(* Dyck paths ---------------------  *)


(* prep *)

Lemma take_rev n (T: Type) (s: seq T) : n <= size s ->
  take n (rev s) = rev (drop (size s - n) s).
Proof.
move => h;rewrite -{1}(cat_take_drop (size s - n) s) rev_cat take_size_cat //. 
by rewrite size_rev size_drop subKn.
Qed.


Lemma eqseq_catr (T:eqType) (s1 s2 s3: seq T) :
  (s1 ++ s3 == s2 ++ s3) = (s1 == s2).
Proof.
elim/last_ind: s3;first by rewrite !cats0.
by move => s x; rewrite -!rcons_cat  eqseq_rcons eqxx andbT /=. 
Qed.


(* noter *)

Lemma eqseq_cat1 (T: Type) (s1 s2 s3: seq T) :
  (s3 ++ s1 = s3 ++ s2) ->  (s1 = s2).
Proof. by elim s3 => // a l h; case. Qed.


Lemma eqseq_cat_simp (T:eqType) (s1 s3: seq T) :
  (s1 ++ s3 == s3) = (nilp s1).
Proof. by rewrite -{2}(cat0s s3) eqseq_catr - size_eq0. Qed.

Lemma card_set_pred: forall (T:finType) (P:T -> bool), 
  #|[set f:T | P f]| =  #|[pred f:T | P f]|.
Proof. by move => T P; apply: eq_card; move => t; rewrite in_set. Qed.


(* end prep *)

Definition DP_Tcount (l:seq bool) := count_mem true l.
Definition DP_Fcount (l:seq bool) := count_mem false l. 
Definition DP_balanced l :=  (DP_Tcount l == DP_Fcount l).

Lemma DP_count l: DP_Tcount l + DP_Fcount l = size l.
Proof. by elim:l => // a l /= <-; case:a; rewrite add1n //= add0n addnS. Qed.

Lemma DP_count' m n l: size l = m + n ->
   (DP_Tcount l == m) = (DP_Fcount l == n).
Proof.
move/eqP;rewrite - DP_count.
case ha: (DP_Tcount l == m);first by rewrite - (eqP ha) eqn_add2l.
by case hb: (DP_Fcount l == n) => //; rewrite - (eqP hb) eqn_add2r ha.
Qed.

Fixpoint DP_pos l :=
  if l is a::l' then DP_pos l' &&  (DP_Tcount l >=  DP_Fcount l) else true.

Definition Dyck_path l:= DP_balanced l && DP_pos l.

Lemma DP_posW l: DP_pos l -> DP_Fcount l <= DP_Tcount l.
Proof. by case:l => // a l /andP[]. Qed.

Lemma Dyck_path_size l: Dyck_path l ->
  size l = (DP_Tcount l).*2.
Proof. by move => /andP [/eqP ha hb]; rewrite - DP_count - ha addnn. Qed.

Lemma Dyck_size_even s: Dyck_path s -> size s = (size s)./2.*2.
Proof.  by move /Dyck_path_size => ->; rewrite half_double. Qed.

Lemma DP_count_sym l1 l2:
   DP_balanced (l1 ++ l2) ->
  (DP_Fcount l2 <= DP_Tcount l2) = (DP_Tcount l1 <= DP_Fcount l1).
Proof.
move/eqP; rewrite /DP_Fcount /DP_Tcount  !count_cat.
case:(leqP ((count_mem true) l1) ((count_mem false) l1)) => sa;
  case:(leqP ((count_mem false) l2) ((count_mem true) l2)) => sb //  eq1.
  by move: (leq_add sa sb); rewrite addnS eq1 ltnn.
by move: (leq_add sa sb); rewrite addSn eq1 ltnn.
Qed.

Lemma DP_prop2 l k (l1 := take k l) (l2 := drop k l) :  Dyck_path l ->
  (DP_Tcount l2 >= DP_Fcount l2) && (DP_Tcount l1 <= DP_Fcount l1).     
Proof.
rewrite -(cat_take_drop k l) => /andP [ha hb].
suff h3:(DP_Tcount l2 >= DP_Fcount l2) by rewrite - (DP_count_sym ha) h3.
move: hb; rewrite -/l2 -/l1;clear;elim l1; first exact:DP_posW.
by move => a l3 Hr; rewrite  cat_cons => /andP[ /Hr].
Qed.

Lemma DP_symmetry l: Dyck_path l -> Dyck_path (rev [seq ~~ x | x <- l]).
Proof.
move => h.
have Ha s:  DP_Tcount [seq ~~ x | x <- s] =  DP_Fcount s.
  by elim: s => //a s /= ->; case:a.
have Hb s:  DP_Fcount [seq ~~ x | x <- s] =  DP_Tcount s.
  by elim: s => //a s /= ->; case:a.
move/andP:(h)=> [/eqP ha _].
set s := (rev [seq ~~ x | x <- l]).
have bs: DP_balanced s.
  rewrite /s /DP_balanced - map_rev Ha Hb /DP_Fcount /DP_Tcount !count_rev.
  by apply/eqP.
have hc:forall k, k <= size s -> DP_Tcount (drop k s) >= DP_Fcount (drop k s).
  move => k kl.
  rewrite - (cat_take_drop k s) in bs.
  rewrite (DP_count_sym bs); move: kl; rewrite /s.
  rewrite -map_rev size_map size_rev - map_take Ha Hb => kl.
  rewrite (take_rev kl) /DP_Fcount /DP_Tcount !count_rev.
  by move /andP:(DP_prop2 (size l - k) h) => [].
rewrite /Dyck_path bs /=. 
elim: s hc {ha bs} => // a l' Hr H1 /=; rewrite (H1 0) // andbT.
apply: Hr => k kl; exact: (H1 k.+1 kl).
Qed.

Lemma DP_pos_cat l1 l2: DP_pos l1 -> DP_pos l2 -> DP_pos (l1 ++ l2).
Proof.
move => sa sb; elim: l1 sa => // a l H /andP [ha].
rewrite /= (H ha) /= /DP_Fcount /DP_Tcount !count_cat !addnA => sa.
exact: (leq_add sa (DP_posW sb)).
Qed.
  
Lemma Dyck_path_cat l1 l2: Dyck_path l1 -> Dyck_path l2 ->
  Dyck_path (l1 ++ l2).
Proof.
move =>/andP[/eqP ha hb] /andP[/eqP hc hd].
move: ha hc;rewrite/Dyck_path /DP_balanced /DP_Tcount /DP_Fcount !count_cat.
by move => -> ->; rewrite eqxx (DP_pos_cat hb hd).
Qed. 

Lemma Dyck_sub_path l1 l2: Dyck_path l1 -> Dyck_path (l1++l2) -> Dyck_path l2.
Proof.
move => /andP[sa sb] /andP[sc sd].
move: sa sc; rewrite /Dyck_path /DP_balanced /DP_Tcount /DP_Fcount.
rewrite !count_cat => /eqP ->; rewrite eqn_add2l => -> /=.
by elim: l1 sd {sb} => // a l Hr /= /andP[/Hr ]. 
Qed.


Lemma Dyck_sub_path' l1 l2: Dyck_path l2 -> Dyck_path (l1++l2) -> Dyck_path l1.
Proof.
move => /andP[sa sb] /andP[sc sd].
move: sa sc; rewrite /Dyck_path /DP_balanced /DP_Tcount /DP_Fcount.
rewrite !count_cat => /eqP => sc; rewrite sc eqn_add2r => -> /=.
elim: l1 sd {sb} => // a l Hr /= /andP[/Hr ]. 
by rewrite /DP_Fcount/DP_Tcount!count_cat sc !addnA leq_add2r => ->.
Qed.

Definition DyckFT := [:: false; true].

Lemma DyckFT_Dyck: Dyck_path DyckFT.
Proof. by [].  Qed.
 
Definition char_seq m (X: {set 'I_m}) := [seq x \in X | x <- (enum 'I_m)].
Definition list_to_set m l := [set x:'I_m | nth false l x].


Lemma size_char_seq m (X: {set 'I_m}): size (char_seq X) = m.
Proof. by rewrite size_map size_enum_ord. Qed.

Lemma char_seq_prop m (X: {set 'I_m}) k (km: k < m):
  nth false (char_seq X) k = ((Ordinal km) \in X).
Proof.
have km1: k < size (enum 'I_m) by rewrite (size_enum_ord m).
set K := (Ordinal km).
by rewrite/char_seq (nth_map K false _ km1) (nth_ord_enum K K). 
Qed. 

Lemma list_to_setK m l: size l = m -> char_seq (list_to_set m l) = l.
Proof.
move => ss.
apply: (eq_from_nth (x0:=false)); rewrite size_char_seq => // i lim.
by rewrite char_seq_prop inE.
Qed.

Lemma set_to_listK m  (X: {set 'I_m}) :  (list_to_set m (char_seq X)) = X.
Proof.
by apply/setP => i; rewrite inE char_seq_prop (@val_inj _ _ _ (Ordinal (ltn_ord i)) i).
Qed.

Lemma set_to_list_cardinal m (X: {set 'I_m}) :
  #|X| = DP_Tcount (char_seq X).
Proof.
rewrite /DP_Tcount/char_seq -sum1_count big_mkcond big_map -big_mkcond.
rewrite -sum1_card -big_enum big_filter big_filter_cond.
by apply: eq_big => // i /=; case: (i \in X).
Qed.

Lemma list_to_set_inj n: injective (fun s: n.-tuple bool => list_to_set n s).
Proof.
move => a b /= fab; apply:val_inj. 
rewrite /= -(list_to_setK (size_tuple a)).
by rewrite -(list_to_setK (size_tuple b)) fab.
Qed.

Lemma cardinal_tuple_nm n m:
  #|[set s: m.-tuple bool | DP_Tcount s == n]| = 'C(m,n).
Proof.
move: (card_draws (ordinal_finType m) n); rewrite card_ord => <-.
rewrite card_set_pred -(card_imset _  (@list_to_set_inj m));apply: eq_card => x.
rewrite !inE; apply/imsetP/idP => [ [y yp yv] | cx].
  by rewrite set_to_list_cardinal yv (list_to_setK (size_tuple y))//.
have sm: size (char_seq x) == m by rewrite size_char_seq.
set y:= Tuple sm. 
move:(list_to_setK (size_tuple y)) (set_to_listK x) => tt w.
by exists y => //; rewrite inE - tt -set_to_list_cardinal w.
Qed.

Fixpoint DP_splita l :=
  if l is a::l' then let u:= (DP_splita l').1 in
     if(nilp u) then 
       if (DP_Tcount l >=  DP_Fcount l) then ([::],l) else ([:: a], l')
     else (a::u,(DP_splita l').2)
  else ([::],[::]).

Definition ends_withF l := (last true l == false).
Definition ends_withT l := (last false l == true).

Lemma DP_splita_recover l: (DP_splita l).1 ++ (DP_splita l).2 = l.
Proof.
elim: l => // a l /=.
by case:(DP_splita l).1; [case: leqP | move => /= b l' {2} <-].
Qed.

Lemma DP_splita_pos1 l: DP_pos l = nilp ((DP_splita l).1).
Proof.
by elim:l => // a l /= <-;case ha: (DP_pos l) => //; case:leqP.
Qed.

Lemma DP_splita_correct l (a:= (DP_splita l).1 ) : 
  (nilp a) || ((ends_withF a) && (Dyck_path ((DP_splita l).2))).
Proof.
rewrite/a; clear a; elim:l => // a l/=.
set u := _.1;  set v := _.2.
case nu: (nilp u); [move => _ | by move/nilP: nu; case:u ].
have pl: DP_pos l by rewrite DP_splita_pos1.
have ww:=(DP_posW pl).  
case:leqP => //=; rewrite /Dyck_path/DP_balanced pl /= eqn_leq ww !andbT.
by case:a => //; rewrite add1n add0n  ? ltnS // => /ltnW; rewrite ltnNge ww.
Qed.

Definition swap_but_first l :=
   if l is a ::s then a:: [seq ~~ x | x <- s] else  nil.

Definition swap_but_last l := rev (swap_but_first (rev l)).

Definition Dyck_modify l :=
  (swap_but_last (DP_splita l).1) ++ (DP_splita l).2.


Lemma Dyck_modify_split l (s :=  (Dyck_modify l)) :
  ((DP_splita s).1 == swap_but_last (DP_splita l).1) &&
  ((DP_splita s).2 == (DP_splita l).2).
Proof.
have H v: nilp ((DP_splita v).1) -> (DP_splita v).2 = v.
   by move/nilP=> ea; move: (DP_splita_recover v); rewrite ea.
rewrite /s /Dyck_modify.
case/orP:(DP_splita_correct l) => /= [ok | /andP [ha hb] ].
   by move/nilP: (ok) => eq1; rewrite (H _ ok) eq1 /= eq1 (H _ ok) ! eqxx.
set l1 := (DP_splita l).1.
have hc: ends_withF (swap_but_last l1).
  move: ha; rewrite /ends_withF  -/l1 -{1} (revK l1) /swap_but_last.
  by case: (rev l1) => // a l'; rewrite /=!rev_cons !last_rcons /=. 
set l3:=(swap_but_last l1).
have ->:l3 = rcons (rev (behead (rev l3))) false.
   move /eqP: hc; rewrite  -/l3 -{1 2} (revK l3); case: (rev l3) => //.
   by move => a l';rewrite rev_cons last_rcons /= => ->.
elim: (rev _).
  move/andP:hb => [/eqP h]; rewrite DP_splita_pos1 =>h1.
  by rewrite /= h1 add1n add0n h ltnn !eqxx.
move => a l' /andP[/eqP ha' /eqP hb']; rewrite rcons_cons cat_cons /= ha' hb'.
by rewrite /nilp size_rcons /= !eqxx.
Qed.

Lemma Dyck_modify_inv l: (Dyck_modify (Dyck_modify l)) = l.
Proof.
have H s: swap_but_last (swap_but_last s) = s.
  rewrite/swap_but_last revK -{2} (revK s); case: (rev s) => // a s'.
  by rewrite /= - map_comp /comp map_id_in // => i _; case:i.
move:(Dyck_modify_split l) => /andP[/eqP ha  /eqP hb].
by rewrite {1}/Dyck_modify ha hb H DP_splita_recover.
Qed.


Lemma swap_but_last_size l: size (swap_but_last l) = size l.
Proof.
rewrite /swap_but_last -{2} (revK l) 2!size_rev.
by case: (rev l) => // a b; rewrite /swap_but_first /= size_map.
Qed.

Lemma swap_but_last_nil l: nilp (swap_but_last l) = nilp l.
Proof. by rewrite /nilp swap_but_last_size. Qed.

Lemma Dyck_modify_size l: size (Dyck_modify l) = size l.
Proof.
rewrite -{2}(DP_splita_recover l) /(Dyck_modify) !size_cat.
by rewrite swap_but_last_size.
Qed.

Lemma swap_but_last_count l:
  ends_withF l -> (DP_Tcount(swap_but_last l)).+1 = DP_Fcount l.
Proof.
rewrite /swap_but_last - {1 3} (revK l); case: (rev l) => // a s.
rewrite {1}rev_cons /ends_withF last_rcons => /eqP ->.
rewrite /DP_Tcount /DP_Fcount !count_rev /= add0n add1n; congr (_.+1).
by elim:s => // b s /= ->; case:b.
Qed.

Lemma Dyck_modify_tcount l (s:=  (Dyck_modify l)) :
  DP_balanced l ->  ~~nilp ((DP_splita l).1) ->
  ((DP_Tcount s).+1 == DP_Tcount l) && (DP_Fcount s == (DP_Tcount l).+1).
Proof.
move => /eqP ha hb.
suff hd: (DP_Tcount s).+1 =  DP_Tcount l.
  have hc: (DP_Tcount s) + (DP_Fcount s) = (DP_Tcount l) + (DP_Fcount l).
    by rewrite !DP_count  Dyck_modify_size.
  by rewrite hd eqxx /=; move /eqP:hc; rewrite - {1} hd ha addSnnS eqn_add2l.
move:(DP_splita_correct l).
rewrite ha /= (negbTE hb) /= => /andP[hc /andP[/eqP hd _]].
rewrite -(DP_splita_recover l) /s /Dyck_modify /DP_Tcount /DP_Fcount.
by rewrite  !count_cat -addSn (swap_but_last_count hc) -/(DP_Tcount _) hd.
Qed.

Lemma Dyck_modify_tcount_bis l (s:=  (Dyck_modify l)) :
  DP_Fcount l = (DP_Tcount l).+2 ->
  ((DP_Tcount s == (DP_Tcount l).+1) && (DP_balanced s)).
Proof.
move => ha.
suff hd: (DP_Tcount s == (DP_Tcount l).+1). 
  rewrite hd /= /DP_balanced (eqP hd) eq_sym.
  rewrite - (DP_count' (m:=(DP_Tcount l).+1)) //.
  by rewrite (Dyck_modify_size l) - DP_count ha addSnnS.
have hb: DP_pos l = false.
  by move: ha; clear; case: l => // a l /= ->; rewrite ltnNge leqnSn andbF.
rewrite - eqSS - ha.
move:(DP_splita_correct l).
rewrite  /= - DP_splita_pos1 hb /=  => /andP[hc /andP[/eqP hd _]].
rewrite -(DP_splita_recover l) /s /Dyck_modify /DP_Tcount /DP_Fcount.
by rewrite  !count_cat -addSn (swap_but_last_count hc) -/(DP_Tcount _) hd.
Qed.

Lemma cardinal_swap_but_last n: 
  #|[set X:{set 'I_(n.*2.+2) } | #|X| ==n ]| =
  #|[set X:{set 'I_(n.*2.+2)} | (#|X| == n.+1) && ~~Dyck_path (char_seq X) ]|.
Proof.
pose T := {set 'I_(n.*2.+2) }.
pose f (x:T):T := list_to_set (n.*2.+2) (Dyck_modify (char_seq x)).
have Ha (x:T): size (Dyck_modify (char_seq x)) = (n.*2.+2).
  by rewrite Dyck_modify_size size_char_seq.
have Hb: involutive f.
  by move=> x;rewrite /f (list_to_setK (Ha x)) Dyck_modify_inv set_to_listK.
rewrite !card_set_pred -(card_imset _ (inv_inj Hb));apply: eq_card => x.
rewrite !inE; apply/imsetP/idP => [ [y yp ->] | /andP[ca cb]].
  rewrite /f set_to_list_cardinal (list_to_setK (Ha y)).
  set l := char_seq y.
  move: yp; rewrite inE set_to_list_cardinal -/l => /eqP tt.
  have /eqP tt2: DP_Fcount l == n.+2.
    by rewrite - (DP_count' (m:=n)) ? tt// /l size_char_seq - addnn - 2!addnS.
  have w3: DP_pos l = false.
    move:tt tt2; clear;case: l => // a l /= -> ->.
    by rewrite leqNgt /= leqnSn andbF.
  move:tt2; rewrite - tt; move/Dyck_modify_tcount_bis.
  move /andP => [-> _]; rewrite /Dyck_path DP_splita_pos1.
  move:(Dyck_modify_split l) => /andP[/eqP -> _].
  by rewrite swap_but_last_nil - DP_splita_pos1 w3 andbF.
exists (f x); last by rewrite Hb.
move: ca; rewrite set_to_list_cardinal => tt.
rewrite inE set_to_list_cardinal /f (list_to_setK (Ha x)).
set l := char_seq x.
have sc: DP_balanced l.
  rewrite /DP_balanced eq_sym.
  by rewrite - (DP_count' (m:=n.+1)) // size_char_seq (eqP tt) addnn.
have sd:~~ nilp (DP_splita l).1.    
  by rewrite - DP_splita_pos1; move: cb; rewrite /Dyck_path sc.
by move/andP:(Dyck_modify_tcount sc sd) =>[]; rewrite (eqP tt) eqSS.
Qed.

Lemma cardinal_tuple_nSSn n: 
  #|[set s: (n.*2.+2).-tuple bool | (DP_Tcount s == n.+1) && ~~Dyck_path s ]|
   = 'C(n.*2.+2,n).
Proof.
move: (card_draws (ordinal_finType (n.*2.+2)) n); rewrite card_ord => <-.
rewrite cardinal_swap_but_last card_set_pred.
rewrite -(card_imset _ (@list_to_set_inj (n.*2.+2)));apply: eq_card => x.
rewrite !inE; apply/imsetP/idP => [ [y yp yv] | cx].
  rewrite set_to_list_cardinal yv (list_to_setK (size_tuple y))//.
have sm: size  (char_seq x) == (n.*2.+2) by rewrite size_char_seq.
set y:= Tuple sm. 
move:(list_to_setK (size_tuple y))  (set_to_listK x) => tt w.
by exists y; rewrite ?w // inE - tt -set_to_list_cardinal w.
Qed.

Lemma cardinal_Dyck_path n: 
  #|[set s: (n.*2).-tuple bool | Dyck_path s ]| = catalan n.
Proof.
case:n => //.
   rewrite /catalan /= bin0 divnn /=; apply:(eq_card1 (x:= [tuple ])) => s.
   by rewrite !inE; case: s => // u; case: u.
move => n.
rewrite catalan_pos //=.
rewrite -(cardinal_tuple_nSSn n) - (cardinal_tuple_nm n.+1 n.*2.+2). 
rewrite - cardsDS; last by apply/subsetP => x; rewrite !inE => /andP[].
apply: eq_card => t; rewrite !inE.
case h: (Dyck_path t); last by rewrite andbT; case: eqP => //.
move /andP:h => [eqa _]; move/eqP:(DP_count t); rewrite size_tuple - (eqP eqa).
by rewrite addnn - muln2 - {2} muln2 eqn_mul2r /= => ->.
Qed.


Fixpoint DP_splitb l :=
  if l is a::l' then let u:= (DP_splitb l').1 in let v:= (DP_splitb l').2 in
     if(nilp u) then 
       if (nilp v) then if a then ([::], [::a]) else ([::a], [::])
       else if (DP_balanced v) then ([::a],v) else ([::],a::v)
     else (a::u,v)
  else ([::],[::]).

Lemma DP_splitb_recover l: (DP_splitb l).1 ++  (DP_splitb l).2 = l.
Proof.
elim:l => // a l H /=.
case ha: (nilp (DP_splitb l).1); last by rewrite /= H.
move: H; move/nilP: ha => {1} -> /= ->.
by case hb: (nilp l); [ move/nilP:hb => ->;case:a | case: ifP].
Qed.

Lemma DP_splitb_lastT l: ends_withT (DP_splitb (rcons l true)).2.
Proof.
elim:l => // a l H /=.
case: (nilp (DP_splitb (rcons l true)).1) => //.
have hb: last a (DP_splitb (rcons l true)).2 == true.
  by move: H; case:  (DP_splitb (rcons l true)).2.
by case nl: (nilp _); [ move: H;move/nilP:nl => -> | case: ifP ].
Qed.


Lemma DP_splitb_pos2 l: nilp (DP_splitb l).1 || Dyck_path (DP_splitb l).2.
Proof.
elim: l => // a l /orP H /=.
case hh:(nilp (DP_splitb l).1); last by case:H => //; rewrite hh.
case nl: (nilp (DP_splitb l).2); first by case:a. 
rewrite /Dyck_path; case: ifP => // -> /=; clear; elim: l  => // a l H /=.
case: (nilp (DP_splitb l).1) => //. 
case:(nilp (DP_splitb l).2);first by case:a.
case: ifP => //=; rewrite H /=.
move: H; case: ((DP_splitb l).2) => // b s /andP [_ hb] hc.
case:a; rewrite add0n add1n; first by apply: (leqW hb).
by rewrite ltn_neqAle hb andbT eq_sym  -/(DP_balanced _) hc.
Qed. 

Lemma DP_splitb_Dyck12 l: Dyck_path l ->
   Dyck_path (DP_splitb l).1 && Dyck_path (DP_splitb l).2.
Proof.
move => h.
move:(DP_splitb_pos2 l) (DP_splitb_recover l).
case nl: (nilp (DP_splitb l).1); first by move/nilP:nl => -> _ //= ->.
move => /= h1; rewrite h1 andbT => h2; rewrite - h2 in h.
move: (DP_splitb l).1 (DP_splitb l).2 h1 h; clear; move=> u v /andP[/eqP  hu _].
move/andP =>[sa sb]; apply /andP; split.
  rewrite /DP_balanced -(eqn_add2r (DP_Fcount v)) - {1} hu.
  by move: sa; rewrite /DP_balanced /DP_Tcount /DP_Fcount !count_cat.
clear sa; elim: u sb => // a l H /= /andP [sa sb].
rewrite (H sa) /=.
move: sb; rewrite /DP_Fcount /DP_Tcount !count_cat 2!addnA -/(DP_Tcount v).
by rewrite hu leq_add2r.
Qed.


Definition DP_lower l := behead (behead (belast true l)).
Definition DP_raise v :=  false :: rcons v true.

Definition Dyck_irred l :=
  (l == DP_raise (DP_lower l))  && Dyck_path (DP_lower l).

Lemma DP_raiseK v: DP_lower (DP_raise v) = v.
Proof. by rewrite /DP_lower /DP_raise /= belast_rcons. Qed.

Lemma DP_raise_inj v1 v2: (DP_raise v1 == DP_raise v2) = (v1 == v2). 
Proof. by rewrite /DP_raise /= eqseq_cons eqseq_rcons !eqxx /= andbT. Qed.

Lemma DP_lowerK v:  (head true v == false) && ends_withT v ->
  DP_raise (DP_lower v) = v.
Proof.
case: v => // a l /= /andP[/eqP -> /eqP]; rewrite /DP_raise.
by case:l => // b l /= <-;rewrite - lastI.
Qed.

Lemma DP_count_catTF v: DP_balanced (DP_raise v) = DP_balanced v.
Proof.
rewrite /DP_raise /DP_balanced/DP_Tcount/DP_Fcount /=  - cats1 !count_cat /=.
by rewrite !add0n !add1n addn0 addn1 eqSS.
Qed.

Lemma Dyck_path_augment l: Dyck_path l -> Dyck_path (DP_raise l).
Proof.
move/andP => [];rewrite -(DP_count_catTF l) /DP_raise => fa ub2.
rewrite /Dyck_path /DP_pos -/DP_pos fa (eqP fa) leqnn /= andbT.
elim:l ub2 {fa} => // a l H /= /andP [h1].
rewrite (H h1) /= - cats1 /DP_Fcount /DP_Tcount.
rewrite !count_cat /= addn1 !addn0 addnS; apply: leqW.
Qed.

Lemma Dyck_irred_Dyck l: Dyck_irred l -> Dyck_path l.
Proof. move=>/andP[ /eqP {2} ->]; exact:Dyck_path_augment. Qed.

Lemma DP_lower_DyckK s:
  Dyck_path s -> ~~ nilp s -> DP_raise (DP_lower s) = s.
Proof.
case: s => // a l /and3P [sa sb _] _; rewrite DP_lowerK //.
move:sa; case: a; rewrite /DP_balanced /= add0n add1n  => /eqP h.
  by move: (DP_posW sb); rewrite -h ltnn.
by case:l sb h => // a l p _; elim: l a p => [ [] | a l H b /andP [/H ]].
Qed.


Lemma DP_splitb_prop1 l: Dyck_path l -> ~~nilp l -> ~~(nilp ((DP_splitb l).2)).
Proof.
move => sa sb.
move:(DP_splitb_lastT (false :: DP_lower l)).
rewrite rcons_cons -/(DP_raise _)  (DP_lower_DyckK sa sb).
by case: (DP_splitb l).2 => //.
Qed.
  
Lemma DP_splitb_prop2a l (v:= (DP_splitb l).2) : Dyck_path l -> ~~nilp l ->
  DP_raise (DP_lower v) = v.
Proof.
move => dl nl. 
move /andP: (DP_splitb_Dyck12 dl) => [_ d2].
exact:(DP_lower_DyckK d2 (DP_splitb_prop1 dl nl)).
Qed.

Lemma DP_splitb_race1 s1 s2: Dyck_path s2 -> ~~ nilp s2 -> 
    (DP_splitb (s1 ++ s2)).2 = (DP_splitb s2).2.
Proof.
move => ha hb; elim:s1 => //a l H /=.
case: (nilp (DP_splitb (l ++ s2)).1) => //.
rewrite H; move/andP:(DP_splitb_Dyck12 ha) =>[_ /andP [->]] /= _.
by rewrite -(DP_splitb_prop2a ha hb).
Qed.

Lemma DP_splitb_race2 l (v:= (DP_splitb l).2): Dyck_path l -> ~~ nilp l -> 
   (DP_splitb v).2 = v.
Proof.
move => h1 h2.
move/andP:(DP_splitb_Dyck12 h1) => [_ d2].
have hb:= (DP_splitb_prop1 h1 h2).
by move: (DP_splitb_race1 (DP_splitb l).1 d2 hb); rewrite(DP_splitb_recover). 
Qed.

Lemma DP_splitb_prop3 l: Dyck_path l -> ~~nilp l -> Dyck_irred (DP_splitb l).2.
Proof.
move => dl nl.
have sa:= (DP_splitb_prop2a dl nl). 
move /andP:(DP_splitb_Dyck12 dl) => [_ /andP[ua' _]].
rewrite /Dyck_irred /Dyck_path - DP_count_catTF sa ua' eqxx /= DP_splita_pos1.
move:(DP_splita_correct (DP_lower (DP_splitb l).2)); simpl.
case ww: (nilp _) => //= /andP[ua ub]. 
move: sa; rewrite - (DP_splita_recover (DP_lower _)).
set A := _.1; set B := _.2.
rewrite /DP_raise rcons_cat -cat_cons (lastI false A)  cat_rcons.
have ->: (last false A = false) by move/eqP:ua; rewrite -/A;case: A.
set s := false :: rcons B true => ee.
move:(Dyck_path_augment ub); rewrite -/B -/s => ds.
have ns:  ~~ nilp s by rewrite /s /nilp.
have: size (DP_splitb s).2 <= size s
  by rewrite-{2}(DP_splitb_recover s) size_cat leq_addl.
move:(DP_splitb_race1 (belast false A) ds ns).
rewrite ee (DP_splitb_race2 dl nl) => <-.
rewrite - ee size_cat size_belast -{2}(add0n (size s)) leq_add2r leqn0.
by rewrite -/(nilp A) ww.
Qed.


Lemma DP_splitb_prop4 l1 l2 (s := l1 ++ DP_raise l2):
   Dyck_path l1 -> Dyck_path l2 ->
   [&& Dyck_path s, (DP_splitb s).1 == l1 & (DP_splitb s).2 ==  DP_raise l2 ].
Proof.
move => sa sb; set s':= DP_raise l2.
have sc:=(Dyck_path_augment sb).
rewrite (Dyck_path_cat sa sc).
suff: (DP_splitb s).2 == s'.
  move => /eqP eq1.
  by move /eqP:(DP_splitb_recover s); rewrite eq1 {2}/s eqseq_catr eqxx => ->.
suff: (DP_splitb s').2 == s'.
  rewrite /s; clear s sa => ww; elim:l1 => // a l H /=.
  case ha: (nilp _) => //;rewrite (eqP H) /=; move/andP:sc => [ -> //].
move: (DP_splitb_recover s');case (DP_splitb s').1; first  by move /eqP.
move => a u /eqP; rewrite /s' cat_cons eqseq_cons => /andP/proj2.
have nn: ~~(nilp s') by rewrite /s' /nilp.
move/andP :(DP_splitb_prop3 sc nn) => []; set v := DP_lower _ => /eqP -> hb.
rewrite /DP_raise -rcons_cons - rcons_cat eqseq_rcons => /andP /proj1 hc.
move/andP:(DP_prop2 (size u) sb) => /proj1; rewrite -(eqP hc) drop_size_cat //.
move/andP:hb => [ /eqP];rewrite /DP_balanced /DP_Tcount /DP_Fcount /= => ->.
by rewrite ltnn.
Qed.

Lemma Dyck_irrred_nnil l: Dyck_irred l -> ~~ nilp l.
Proof. by move => /andP[/eqP -> _]. Qed.

Lemma Dyck_irrred_prop1 l1 l2: Dyck_path l1 -> Dyck_path l2 ->
  Dyck_irred (l1++l2) -> (nilp l1 ) || (nilp l2).
Proof.
move => sa sb /andP[sc sd].
case nl: (nilp l2);  rewrite ?orbT ?orbF //.
have dd: Dyck_path [::] by [].
move: (DP_splitb_prop4 dd sd)=>/and3P[_ _]; rewrite cat0s - (eqP sc).
move: (DP_splitb_race1 l1 sb (negbT nl)) => ->.
rewrite -{2} (DP_splitb_recover l2) catA - {1}(cat0s (DP_splitb l2).2).
rewrite eqseq_catr; case l1 => //.
Qed.

Lemma Dyck_irrred_prop2 l: Dyck_path l -> ~~ nilp l ->
  (forall l1 l2, Dyck_path l1 -> Dyck_path l2 -> l = l1 ++ l2 ->
     (nilp l1 ) || (nilp l2)) ->
  Dyck_irred l.
Proof.
move => dl nl H.
have ha:=(DP_splitb_prop3 dl nl).
have hb:= (DP_splitb_recover l).
move /andP:(DP_splitb_Dyck12 dl) => [hc hd].
move:(H _ _ hc hd (esym hb)).
by rewrite (negbTE (Dyck_irrred_nnil ha)) orbF - {2} hb => /nilP ->.
Qed.

Definition DP_splitb_size l := (size (DP_lower(DP_splitb l).2))./2.


Lemma DP_splitb_size_correct l n (k :=  DP_splitb_size l):
  Dyck_path l -> size l = n.+1.*2 ->
  (size (DP_splitb l).2 == k.*2.+2) && (k <= n).
Proof.
move => sa sb.
have nn: ~~ nilp l by rewrite /nilp sb.
move/andP:(DP_splitb_prop3 sa nn) => [/eqP /(f_equal size) /= sc sd].
move: sc; rewrite size_rcons (Dyck_size_even sd) -/(DP_splitb_size l) -/k => ha.
move/(f_equal size):(DP_splitb_recover l);rewrite sb size_cat ha eqxx /= => hb.
by rewrite - ltnS - leq_double - hb leq_addl.
Qed.

Lemma Dyck_path_exists1 n (l := (nseq n false) ++  (nseq n true)):
   (DP_Tcount l == n) && (Dyck_path l).
Proof.
have H1 m (v:bool)  p: count p (nseq m v) = m * (p v).
  by elim:m => // m /= ->; rewrite mulSn.
rewrite /Dyck_path /DP_balanced/DP_Tcount/DP_Fcount {1 2 3} /l.
rewrite !count_cat !H1 /= muln0 muln1 addn0 eqxx /=.
move:(leqnn n); rewrite /l; clear l; elim:{1 3}n.
  move => _ /=; elim:n => // n /= ->; rewrite /DP_Fcount /DP_Tcount !H1 //=.
  rewrite muln0 //.
move => k H lkn /=; rewrite (H (ltnW lkn)) /= /DP_Tcount/DP_Fcount !count_cat.
by rewrite !H1 /= !muln1 !muln0 // addn0.
Qed.

Lemma eqn_double m n: (m.*2  == n.*2) = (m == n).
Proof. by rewrite - !muln2 eqn_mul2r. Qed.

(* noter *)
Lemma size_DP_raise l: size (DP_raise l) = (size l).+2.
Proof. by rewrite /DP_raise /= size_rcons. Qed.


Lemma Dyck_path_exists2 n m (ln := (nseq n false) ++  (nseq n true))
  (lm := (nseq m false) ++  (nseq m true)) (l := ln ++ DP_raise lm):
  [&& size l == (n+m).+1.*2, (Dyck_path l) &  DP_splitb_size l == m].
Proof.  
have sz: size (DP_raise lm) = (m.+1).*2. 
  by rewrite size_DP_raise  size_cat !size_nseq addnn.
have ss: size l =  ((n + m).+1).*2. 
  by rewrite {1}/l/ln /= size_cat sz size_cat !size_nseq addnn -doubleD addnS.
move: (Dyck_path_exists1 n) (Dyck_path_exists1 m).
rewrite -/ln -/lm; move => /andP[ha hb]/andP[hc hd].
move:(DP_splitb_prop4 hb hd); rewrite -/l =>/and3P[qa qb /eqP qc].
rewrite ss eqxx qa; move/andP:(DP_splitb_size_correct qa ss) => [/eqP wa wb].
by rewrite - eqSS  -eqn_double /= doubleS - wa qc sz eqxx. 
Qed.

Lemma catalan_rec2 n:
  catalan n.+1 = \sum_(i<n.+1) catalan i * catalan (n-i).
Proof.
transitivity (\sum_(i in 'I_n.+1) catalan i * catalan (n-i)) => //. 
rewrite - cardinal_Dyck_path. 
set I :=  (n.*2.+2).-tuple bool.
pose h (s: I) := (@inord n (DP_splitb_size s)).
set f := (fun t:I => Dyck_path t). 
rewrite - sum1dep_card (partition_big_imset h f) /=.
have ->: [set h x | x in f] = [set:  'I_n.+1 ].
  apply/setP => i; rewrite inE;apply/imsetP.  
  have lin: i <= n by rewrite - ltnS //.
  move: (Dyck_path_exists2 (n-i) i) => /=; set l := _ ++ _.
  rewrite (subnK  lin); move/and3P=> [ha hb hc]. 
  set x := Tuple ha; exists x; first by rewrite /f unfold_in.
  by rewrite /h /x /= (eqP hc) inord_val.
apply: eq_big => // i /=; rewrite !inE // => _.
have lin: i <= n by rewrite - ltnS //.
transitivity (#|[set s:I | f s && (h s == i) ]|).
   by rewrite sum1dep_card; apply:eq_card => s; rewrite !inE.
rewrite - cardinal_Dyck_path. 
rewrite - cardinal_Dyck_path. rewrite - cardsX.
set I1 :=  i.*2.-tuple bool.
set I2 :=  ((n-i).*2).-tuple bool.
symmetry.
set B1 := [set s:I1 | Dyck_path s].
set B2 := [set s:I2 | Dyck_path s]. 
pose g1 (p: I1 * I2) := p.2 ++ DP_raise (p.1).
have gs  p: size (g1 p) == n.+1.*2.
  by rewrite /g1/= size_cat size_DP_raise !size_tuple !addnS - doubleD subnK.
pose g p := Tuple (gs p).
have injg: injective g.
  move => s1 s2 /(f_equal (@tval (n.*2.+2) bool)); rewrite /= /g1 => /eqP.
  rewrite (eqseq_cat) ?size_tuple // => /andP [sa]; rewrite DP_raise_inj => sb.
  rewrite (surjective_pairing s1) (surjective_pairing s2).
  move /eqP:sa => /val_inj ->; move /eqP:sb => /val_inj -> //.
rewrite card_set_pred -(card_imset _  injg) ;apply: eq_card => x.
  rewrite !inE; apply/imsetP/idP => [ [y yp yv] | cx].
  rewrite yv /f/g /=.
  move: yp; rewrite !inE => /andP[ dp1 dp2].
  move:(DP_splitb_prop4 dp2 dp1) => /and3P [ha hb hc]; rewrite ha /h /=.
  by rewrite/DP_splitb_size (eqP hc) DP_raiseK size_tuple// doubleK inord_val.
move/andP:cx; rewrite /f/h ; move => [sa sb].
have sx: size x = n.+1.*2 by rewrite size_tuple.
move:(DP_splitb_size_correct sa sx); rewrite -ltnS; move/andP=> [/eqP sc sd].
have se: DP_splitb_size x = i by rewrite - (eqP sb) (inordK sd).
have nn:~~ nilp x by rewrite /nilp size_tuple.
move:(DP_splitb_prop3 sa nn)  => /andP[ra rb].
move: (DP_splitb_recover x); rewrite (eqP ra) => eqa.
move: (f_equal size (DP_splitb_recover x)); rewrite size_cat sx sc se => /eqP.
rewrite 2!addnS {2} (doubleS n) 2!eqSS -{3} (subnK lin) doubleD eqn_add2r => su.
have sv: size (DP_lower ((DP_splitb x).2))  == i.*2.
  by move: sc; rewrite se/DP_lower 2! size_behead size_belast => ->.
exists (Tuple sv,Tuple su); last by apply:val_inj;rewrite /= - {1} eqa.
by rewrite !inE /= rb; move/andP:(DP_splitb_Dyck12 sa) =>[-> //].
Qed.


Lemma size_ind (A:Type) (P: seq A -> Prop): 
 (forall l, (forall s, size s < size l -> P s) -> P l) -> 
 (forall l, P l). 
Proof.
move => hb l;  move:{2} (size l) (leqnn (size l)) => n; elim: n l.
  by move=> l h; apply:hb => s ss; move: (leq_trans ss h); rewrite ltn0.
move => n Hr l; rewrite leq_eqVlt => /orP; case => kp2; last by apply: Hr.
by apply: hb =>s; rewrite (eqP kp2) ltnS; apply: Hr.
Qed.

Fixpoint DP_splitc_aux n l:=
  if n is n'.+1 then
    if nilp l then [::] else let uv:= DP_splitb l in
      if nilp uv.2 then [:: l] else rcons (DP_splitc_aux n' uv.1) uv.2     
  else [::].


Definition DP_splitc l:= DP_splitc_aux (size l) l.

Lemma DP_splitb_size_rec s: nilp (DP_splitb s).2 = false ->
  size (DP_splitb s).1 < size s.
Proof.
move => sa; rewrite - {2} (DP_splitb_recover s) size_cat -addn1 leq_add2l.
by rewrite lt0n -/(nilp _) sa.
Qed.


Lemma DP_splitc_rec l:
   DP_splitc l = if nilp l then [::] else
     if nilp (DP_splitb l).2 then  [:: l]
     else rcons (DP_splitc (DP_splitb l).1)  (DP_splitb l).2.
Proof.
have H: forall m n l, n <= m -> size l <= n ->
  DP_splitc_aux n l = DP_splitc_aux m l.
  clear l;elim => [n l | n Hr m l]; first by rewrite leqn0 => /eqP -> //.
  case: m; first by rewrite leqn0 => _ /nilP ->.
  move => m; rewrite ltnS => le1 le2 /=; case nn: (nilp l) => //.
  case nl1: (nilp _) => //. 
  by rewrite (Hr _ _ le1 (leq_trans ( DP_splitb_size_rec nl1) le2)).
rewrite  /DP_splitc {1}/nilp.
move: {-1}(size l) (erefl (size l));case  => //= n eqa.
case nn: (nilp (DP_splitb l).2); rewrite /nilp eqa //=.
move:( DP_splitb_size_rec  nn); rewrite eqa ltnS => sb.
by rewrite (H _ _ _ sb).
Qed.

Lemma DP_splitc_recover l: flatten (DP_splitc l) =  l.
Proof.
elim /size_ind:l => l Hr.
rewrite (DP_splitc_rec l);case nn: (nilp l); first  by move/nilP:nn => ->.
case ha:(nilp (DP_splitb l).2); first by rewrite /= cats0.
rewrite - cats1 flatten_cat (Hr _ (DP_splitb_size_rec ha)) /= cats0.
by rewrite DP_splitb_recover.
Qed.

Lemma DP_splitc_correct l: Dyck_path l -> all Dyck_irred (DP_splitc l).
Proof.
elim /size_ind:l => l Hr dl.
rewrite (DP_splitc_rec l);case nn: (nilp l) => //.
rewrite (negbTE(DP_splitb_prop1 dl (negbT nn))) /= all_rcons.
move /andP: (DP_splitb_Dyck12 dl) => [ha _].
rewrite (DP_splitb_prop3 dl (negbT nn)) /= Hr //.
exact: (DP_splitb_size_rec (negbTE (DP_splitb_prop1 dl (negbT nn)))). 
Qed.

Lemma Dyck_flatten d: all Dyck_irred d -> Dyck_path (flatten d).
Proof.
elim:d => // a l Hr /= /andP[ /Dyck_irred_Dyck ha /Hr hc].
by apply: Dyck_path_cat. 
Qed.
  
Lemma DP_splitc_unique l d: 
  all Dyck_irred d -> flatten d = l -> DP_splitc l =d.
Proof.
elim /size_ind:l d => l Hr d  hb hc.
rewrite DP_splitc_rec; case nl: (nilp l).
   move: nl; rewrite -hc /nilp size_flatten; move/natnseq0P.
   move: hb; case d => // u v /= /andP [/andP[/eqP -> _] hv].
   rewrite size_DP_raise //.
move:(Dyck_flatten hb); rewrite hc => dl.
rewrite (negbTE(DP_splitb_prop1 dl (negbT nl))).
move /andP: (DP_splitb_Dyck12 dl) => [ha _].
have hd:= (DP_splitb_size_rec (negbTE (DP_splitb_prop1 dl (negbT nl)))). 
move: hb hc; case:d; first by move => _ ln; move: nl; rewrite -ln.
move => a' d'; rewrite lastI; set a := last _ _; set d := belast _ _.
rewrite -{1 2} cats1 all_cat flatten_cat /= cats0. 
move => /and3P[hu /andP[/eqP hv1 hv2] _] hw.
have dpd:= (Dyck_flatten hu).
move: (DP_splitb_recover l) => hw'.
move:(DP_splitb_prop4 (Dyck_flatten hu) hv2); rewrite -hv1 hw.
move/and3P => [eq1 /eqP /esym eq2 /eqP eq3].
by rewrite eq3 -(Hr (DP_splitb l).1 hd d  hu eq2).
Qed.

Lemma DP_splitc_cat  l1 l2:  Dyck_path l1 -> Dyck_path l2 ->
  DP_splitc (l1 ++ l2) = DP_splitc l1 ++ DP_splitc l2.
Proof.
move => ha hb; apply:DP_splitc_unique.
  by rewrite all_cat (DP_splitc_correct ha) (DP_splitc_correct hb). 
by rewrite flatten_cat ! DP_splitc_recover.
Qed.

Lemma DP_splitc_irred l:  Dyck_irred l -> DP_splitc l = [:: l].
Proof. by move => h; apply: DP_splitc_unique => //=; rewrite ?h // cats0. Qed.

Lemma DP_irred_size2 l: Dyck_irred l -> size l == 2 -> l = DyckFT.
Proof.
move => /andP [/eqP -> _]; case:(DP_lower l) => // a l'.
by rewrite /DP_raise /= size_rcons //.
Qed.

Fixpoint DP_ph1_aux (d: (list (list bool))) :=
  if d is l::d then
      DP_ph1_aux d && [|| size l == 2, nilp d | size (head nil d) == 2]
  else true.


Definition DP_NH1 l:= all (fun s => size s != 2) (DP_splitc l).
Definition Dyck_NH1 l:= Dyck_path l && DP_NH1 l.
Definition DP_ph1_aux2 l :=
  (l == DyckFT) ||  (~~ nilp l && (Dyck_NH1 l)).
Definition DP_ph1 d:= (DP_ph1_aux d) &&  (all DP_ph1_aux2 d).

Lemma DP_ph1_simp a l:  DP_ph1 (a:: l) = 
    [&& DP_ph1 l, [|| size a == 2, nilp l | size (head nil l) == 2] 
     & DP_ph1_aux2 a].
Proof. by rewrite /DP_ph1 /=  (andbC (DP_ph1_aux2 a)) andbACA. Qed.

Lemma DP_ph1_Dyck_aux l: DP_ph1_aux2 l -> Dyck_path l.
Proof. by case/orP; [move/eqP -> |move/andP=>[_ /andP[]] ]. Qed.

Lemma DP_ph1_Dyck d : DP_ph1 d -> Dyck_path (flatten d).
Proof. 
move/andP=> [_]; elim: d => // a l Hr /= /andP [ha hb].
exact: (Dyck_path_cat (DP_ph1_Dyck_aux ha) (Hr hb)).
Qed.  

Lemma DP_ph1_nonempty d : DP_ph1 d -> all (fun z => ~~ nilp  z) d.
Proof. 
elim:d => // a l Hr. rewrite  DP_ph1_simp => /= /and3P [/Hr -> _].
by rewrite andbT;case/orP;[move => /eqP -> | move/andP => [] ].
Qed.

Lemma DP_ph1_size2 l: DP_ph1_aux2 l -> size l == 2 -> l = DyckFT.
Proof.
move /DP_ph1_Dyck_aux.
by case:l  => // b [ // | a [ | c l //]]; case:a; case: b.
Qed.

Lemma DP_NH1_prop1 x y: Dyck_path y -> ~~ Dyck_NH1 ((y ++ DyckFT) ++ x).
Proof.
move => dpy; apply/negP => /andP [bp2].
have dp1: Dyck_path(y ++ DyckFT) by apply: Dyck_path_cat.
have hh: Dyck_irred DyckFT by [].
rewrite  /DP_NH1(DP_splitc_cat dp1 (Dyck_sub_path dp1 bp2)).
by rewrite (DP_splitc_cat dpy) // 2!all_cat  (DP_splitc_irred hh) /= andbF.
Qed.

Lemma DP_NH1_prop2 x: ~~ Dyck_NH1(DyckFT ++ x).
Proof. by rewrite -(cat0s DyckFT); rewrite DP_NH1_prop1. Qed.

Lemma DP_ph1_unique d1 d2 :
  DP_ph1 d1 -> DP_ph1 d2 -> flatten d1 = flatten d2 -> d1 = d2.
Proof. 
move En: (size d1 + size d2) => n.
have: size d1 <= n by rewrite -En ; apply leq_addr.
have: size d2 <= n by rewrite -En ; apply leq_addl.
have T a l: DP_ph1 (a :: l) -> ~~ nilp (flatten (a :: l)).
  rewrite /nilp /= size_cat; move/DP_ph1_nonempty => /= /andP[] /negbTE => ha _.
  by rewrite negbT // addn_eq0 -/(nilp a) ha.
elim: n d1 d2 {En}.
  by move => d1 d2; rewrite !leqn0 => /nilP -> /nilP.
move => n Hr; case.    
  by case => // a l _ _ _;move/T => sa sb; move: sa; rewrite - sb.
move => a d1; case; first by move => _ _ /T sa _ sb ; move: sa; rewrite  sb.
move => b d2 /=;rewrite 2!ltnS; wlog:a d1 b d2 /size a <= size b.
  move => hh; case /orP:(leq_total (size a) (size b)); first by apply: hh.
  by move => sa sb sc ha hb /esym hc; symmetry; apply:hh.
move => lsab sd2n sd1n ph1 ph2 sv {T}.
have bv: b = a ++ (drop (size a) b).
  move/eqP: sv.
  rewrite - {1 2} (cat_take_drop (size a) b) - catA.
  by rewrite eqseq_cat ?(size_takel lsab)// => /andP[/eqP <-  _]. 
move: ph1 ph2; rewrite 2!DP_ph1_simp => /and3P[pa pb pc]/and3P[qa qb qc].
suff eab: a = b.
  move: sv; rewrite eab => /eqseq_cat1 ha.
  by rewrite (Hr _ _ sd2n sd1n pa qa ha).
move: lsab;rewrite leq_eqVlt => /orP [] lsab.
  by rewrite bv (eqP lsab) drop_size cats0.
have dd x: DP_ph1_aux2 x -> Dyck_path x.
  by case/orP; [move => /eqP ->  | move=> /andP[_ /andP [] ]].
have lsab': (size a).+2 <= size b.
  move: lsab;rewrite(Dyck_size_even (dd _ pc)) (Dyck_size_even (dd _ qc)).
  by rewrite ltn_double -doubleS leq_double.
case/orP:qc => bp1.
  move: lsab'; rewrite (eqP bp1) /= 2!ltnS leqn0 => ae.
  by case/orP: pc; [ move/eqP | rewrite /nilp ae].
move/andP:bp1 => [bp1 bp2].
case av: (a == DyckFT).
   by move/eqP:av => av; move:bp2;rewrite bv av (negbTE (DP_NH1_prop2 _)).
have bv': flatten d1 = drop (size a) b ++ flatten d2.
  by move: sv; rewrite {1} bv - catA => /eqseq_cat1 .
case/or3P: pb => pb.
+ by move: av; rewrite -(DP_ph1_size2 pc pb) eqxx. 
+ move/nilP: pb => pb;  move:(f_equal size sv) lsab.
  by rewrite pb /= cats0 size_cat ltnNge=> -> //; rewrite leq_addr.
+ move:(DP_NH1_prop1 (drop (size a).+2 b) (DP_ph1_Dyck_aux pc)).
  have sz1:size (a ++ DyckFT) = size (take (size a).+2 b).
    by rewrite size_cat addn2 (size_takel lsab').
  suff: b = (a ++ DyckFT) ++ (drop (size a).+2 b) by move => <-; rewrite bp2.
  move/eqP: sv; move: pa pb; case: (d1) => // u v /=; rewrite DP_ph1_simp. 
  move => /and3P [_ _  xx] /(DP_ph1_size2 xx) ->.
  rewrite - {1 2} (cat_take_drop (size a).+2 b) - catA (catA a).
  by rewrite (eqseq_cat _ _ sz1) => /andP[/eqP <-  _]. 
Qed.

Fixpoint DP_split_resize (l: list (list bool)):=
  if l is a :: l then let l' := DP_split_resize l in
   if (size a == 2) then a::l'
   else if l' is u::v then if(size u == 2) then a :: u :: v
  else (a++u) ::v  else [:: a]
  else [::].

Lemma DP_split_resize_flatten l: flatten l = flatten (DP_split_resize l).
Proof.
elim: l => // a l /= ->; case: (_ == _) => //.
by case: (DP_split_resize l) => // b s /=; rewrite fun_if /= catA if_same.
Qed.

Lemma DP_split_resize_correct1 l: DP_ph1_aux (DP_split_resize l).
Proof.
elim:l => // al l Hr /=.
case sz:(size al == 2);first by rewrite /= Hr /= sz.
move: Hr; case: (DP_split_resize l)=> [ /= | b s /=]; first by rewrite orbT.
case sb: (size b == 2); first by rewrite /= andbT sb /= orbT !andbT.
by simpl => /andP[ ha hb]; rewrite ha /= hb orbT.
Qed.

Lemma DP_split_resize_correct2 l: all Dyck_irred l ->
  DP_ph1 (DP_split_resize l).
Proof.
have H a: Dyck_irred a -> DP_ph1_aux2 a.
  move => h; rewrite /DP_ph1_aux2/Dyck_NH1/DP_NH1.
  rewrite (DP_splitc_irred h) /= (Dyck_irred_Dyck h).
  move/andP:h => [/eqP -> _]; rewrite size_DP_raise. 
  by case:(DP_lower a) => // u s /=; rewrite orbT.
rewrite /DP_ph1 => ha;rewrite DP_split_resize_correct1 /=.
elim: l ha => // a l Hr /= /andP[/H ha /Hr hb].
case sz: (size a == 2). by rewrite /= ha  hb.
move: hb. 
case: (DP_split_resize l). by rewrite /= ha .
move=> b s /= /andP[hu hv].
case sb:(size b == 2). simpl. rewrite ha hu hv //.
simpl; rewrite hv andbT /DP_ph1_aux2.
case/orP: ha => ha; first by move:sz; rewrite (eqP ha).
case/orP: hu => hb; first by move:sb; rewrite (eqP hb).
move/andP: ha => [ha1 /andP[ha2 ha3]]; move/andP: hb => [hb1 /andP[hb2 hb3]].
have ->: ~~ nilp (a ++ b). 
  by rewrite /nilp size_cat addn_eq0 -/(nilp a)(negbTE ha1).
apply/orP; right; simpl;apply/andP; split; first exact:(Dyck_path_cat ha2 hb2).
by rewrite /DP_NH1 (DP_splitc_cat ha2 hb2) all_cat; apply/andP.
Qed.


Lemma DP_split_resize_correct3 l (d := (DP_split_resize (DP_splitc l))):
  Dyck_path l -> DP_ph1 d && (flatten d == l).
Proof.
move => ha; rewrite /d -DP_split_resize_flatten DP_splitc_recover.
by rewrite (DP_split_resize_correct2 (DP_splitc_correct ha)) eqxx.
Qed.

Definition starts_withFT l:= if l is [:: false, true & l] then true else false.
Definition DP_FT_DH1 l := starts_withFT l && Dyck_NH1 (drop 2 l).
Definition prependFT l := [:: false, true & l].

Lemma starts_withFT_prop l: 
   starts_withFT l = (l == prependFT (drop 2 l)).
Proof.
by case:l => // a [ | b l];case: a => //; case:b => //=; rewrite drop0 eqxx.
Qed. 

Lemma starts_withFT_alt x: starts_withFT x = ((take 2 x) == DyckFT).
Proof.
by case:x => // a [ | b l]; case:a => //; case:b => //=;rewrite take0.
Qed.

Fixpoint DP_resizeb (l: list (list bool)) :=
  if l is a::l then let l' :=  DP_resizeb l in
    if (nilp l' || (starts_withFT (head nil l'))) then  a::l'
    else  (a ++  (head nil l')):: (behead l')
  else nil.

Lemma DP_resizeb_flatten l: flatten l = flatten (DP_resizeb l).
Proof. 
elim: l => // a l /= ->; case:(DP_resizeb l); rewrite /= ? andbT ? andbF //.
by move => b s /=; rewrite fun_if /= catA if_same.
Qed.

Lemma DP_resizeb_prop1 l: all starts_withFT (behead (DP_resizeb l)).
Proof. 
elim: l => // a l /=; case: (DP_resizeb l) => //.
by move => b s /=; case cv: (starts_withFT b) => //; rewrite /= cv. 
Qed.

Lemma DP_resizeb_prop2 l: all starts_withFT (DP_resizeb(DyckFT ::l)).
Proof.
move:(DP_resizeb_prop1 l) => /=;case: (DP_resizeb l) => // a s //=. 
by rewrite fun_if /= => ->; case:ifP => // ->.
Qed.

Lemma DP_NH1_prop3 b:  starts_withFT b -> ~~(Dyck_NH1 b).
Proof.
rewrite starts_withFT_prop => /eqP ->; exact: (DP_NH1_prop2 (drop 2 b)).
Qed.

Lemma DP_NH1_prop4 a x: Dyck_path a -> starts_withFT x -> 
  ~~(Dyck_NH1 (a ++ x)).
Proof.
rewrite starts_withFT_prop => ha /eqP ->.
by move:(DP_NH1_prop1  (drop 2 x) ha); rewrite - catA.
Qed.

Definition DP_resizeb_condition s :=
  nilp s || ((all DP_FT_DH1 (behead s)) && 
    (DP_FT_DH1 (head nil s) || (DP_ph1_aux2 (head nil s)))).

Lemma DP_resizeb_prop3 d: DP_ph1 d -> DP_resizeb_condition (DP_resizeb d).
Proof.
have eqA l: nilp l = nilp (DP_resizeb l).
  by clear; case:l => // a l /=; rewrite fun_if if_same.
elim: d => // a d Hr /=; rewrite DP_ph1_simp => /and3P[ha hb hc].
move:(Hr ha); clear Hr; rewrite /DP_resizeb_condition.
move: hb; case nd: (nilp d); first by move/nilP: nd => -> /= _; rewrite hc orbT.
move: (nd); rewrite eqA => nrb; rewrite nrb /=.
set b := (head [::] (DP_resizeb d)); set u := behead (DP_resizeb d).
have eq1: (DP_resizeb d)= b :: u.
  by rewrite /b/u; move: nrb; case:(DP_resizeb d).
move => hb /andP[hd he]; apply/orP; right.
case /orP: he => he.
  by move /andP:(he) =>[-> _];rewrite /= eq1 /= hd hc he orbT.
case/orP: he => he; first by rewrite (eqP he) /=  eq1 hc /= hd (eqP he) orbT.
move /andP:he => [he1 he2].
case ww:(starts_withFT b); first by move:(DP_NH1_prop3 ww); rewrite he2.
have hw: ~~ nilp (a ++ b).
  by rewrite /nilp size_cat addn_eq0 -/(nilp b) (negbTE he1) andbF.
case/orP:hb => hb; last first.
  have dv: d = (head [::] d) :: behead d by move: nd; clear; case:d.
  move: ha; rewrite dv /= DP_ph1_simp=> /and3P [_ _ aux1].
  move: (DP_ph1_size2 aux1 hb) => hdv.
  by move:(DP_resizeb_prop2 (behead d)); rewrite -hdv - dv eq1 /= ww.
move:(DP_ph1_size2 hc hb) => av.
by rewrite hd /= /DP_ph1_aux2 hw /= /DP_FT_DH1 av /= drop0 he2.
Qed.


Lemma DP_resizeb_prop4 d:
   DP_ph1 d -> (all DP_FT_DH1 ((DP_resizeb (DyckFT :: d)))).
Proof.
move => h.
move:(DP_resizeb_prop3 h);rewrite /DP_resizeb_condition /=. 
case nl: (nilp (DP_resizeb d)); first by move/nilP: nl ->. 
set b := (head [::] (DP_resizeb d)); set u := behead (DP_resizeb d).
have eq1: (DP_resizeb d)= b :: u.
  by rewrite /b/u; move: nl; case:(DP_resizeb d).
move=> /= /andP[ha hb].
case /orP: hb => hb.
  by move /andP:(hb) =>[-> _];rewrite eq1 /= ha hb.
case/orP: hb => hb; first by rewrite (eqP hb) eq1 /= ha (eqP hb).
move /andP:hb => [he1 he2].
case ww:(starts_withFT b); first by move:(DP_NH1_prop3 ww); rewrite he2.  
by rewrite /= ha /DP_FT_DH1 /= drop0 he2.
Qed.

Lemma DP_split_resizeb_correct l 
  (d := ( DP_resizeb (DP_split_resize (DP_splitc l)))):
  Dyck_path l -> starts_withFT l -> (all DP_FT_DH1 d) && (flatten d == l).
Proof.
rewrite starts_withFT_prop => ha hb. 
have ea: l = [::false ; true] ++ (drop 2 l) by rewrite {1} (eqP hb).
have eb: Dyck_path [::false ; true] by [].
rewrite ea in ha; move:(Dyck_sub_path eb ha) => dd.
move: (DP_split_resize_correct3 dd).
set x := DP_split_resize _; move => /andP[sa sb].
have dv: d = DP_resizeb (DyckFT :: x).
  by rewrite /d {1} ea (DP_splitc_cat eb dd).
by rewrite dv (DP_resizeb_prop4 sa) - DP_resizeb_flatten /= eq_sym (eqP sb).
Qed.


Lemma DP_FT_DH1aux_unique d1 d2:
  DP_resizeb_condition d1 ->  DP_resizeb_condition d2 ->
  flatten d1 = flatten d2 -> d1 = d2.
Proof.
pose q x := (~~ nilp x && Dyck_NH1 x).
have Ht a b u v:  q a -> (prependFT b) ++ u = a ++ v -> false.
  move => /andP[sa sb] sc.
  suff sd: (starts_withFT a) by move:(DP_NH1_prop3 sd); rewrite sb.
  move: sa sb sc; case:a => // [] [] // [] // [] //.
have W x (l: seq bool) n : x = take n l -> 2 <= size x -> take 2 x = take 2 l.
  move => ->; case:l=>// a; case; [by case:n | move => b l]; case:n=> [|n] //.
  by case:n=> //n; rewrite /=!take0.
have He a b l1 (x:= take (size b - size a) (flatten l1)) : size a < size b -> 
   Dyck_path a -> Dyck_path b -> all DP_FT_DH1 l1 -> 
     b = a ++ x -> starts_withFT x.
  move => ha hb hc hd gf.
  rewrite starts_withFT_alt; rewrite gf in hc.   
  have sx: 2 <= size x.
    move: ha; rewrite gf size_cat; move: (Dyck_sub_path hb hc).
    case x; [by rewrite addn0 ltnn | move => a1 [ | //]]; by case:a1.
  rewrite (W _ (flatten l1) (size b - size a) (erefl x) sx).
  move: hd sx; rewrite /x. clear. case: l1 => // aa ll /= /andP[/andP [he _] _].
  by rewrite starts_withFT_prop in he; rewrite /= (eqP he) 2!cat_cons //= take0.
rewrite /DP_resizeb_condition; case: d1;case: d2 => //.
  by case => //l;  rewrite /DP_ph1_aux2 /= andbF.
  by case => // l; rewrite /DP_ph1_aux2 /= andbF.
move => a l1 b l2 /=.
suff aux: forall d1 d2, all DP_FT_DH1 d1 -> all DP_FT_DH1 d2 ->
   flatten d1 = flatten d2 -> d1 = d2.
  have sx x:(DP_FT_DH1 x || DP_ph1_aux2 x) = DP_FT_DH1 x || (q x).
    rewrite /DP_ph1_aux2 /q.
    by case xv: (x == DyckFT) => //; rewrite (eqP xv).
  rewrite sx sx.
  move => /andP [ha hb] /andP[hc hd]; case/orP:hb; case/orP:hd => hb hd.
  + by move => w; apply: aux => //=; [ rewrite ha hd | rewrite hb hc].
  + move/andP:hd =>[]; rewrite  starts_withFT_prop => /eqP -> _ sc.
    by move:(Ht a (drop 2 b)(flatten l2) (flatten l1) hb sc).
  + move/andP:hb =>[]; rewrite  starts_withFT_prop => /eqP -> _ /esym sc.
    by move:(Ht b (drop 2 a)(flatten l1) (flatten l2) hd sc).
  + move => eq1.
    suff eab: a = b. 
      by move: eq1; rewrite eab => /eqseq_cat1 hab; rewrite (aux _ _ ha hc hab).
      wlog lsab: a b l1 l2 ha hc hb hd eq1/ size a <= size b.
      move => hh; case /orP:(leq_total (size a) (size b)) => xx. 
       by apply: (hh _ _ _ _ ha hc hb hd eq1 xx).
      symmetry; apply:(hh _ _ _ _ hc ha hd hb (esym eq1) xx).
    move: (f_equal (take (size b)) eq1); rewrite take_size_cat //.
    rewrite take_cat ltnNge lsab /=.
    move: lsab;rewrite leq_eqVlt => /orP; case => lsab.
      by rewrite (eqP lsab) subnn take0 cats0.
   set x := take (size b - size a) (flatten l1) => xp.
   have dpa: Dyck_path a by  move/andP:hb => [_ /andP[]]. 
   move/andP:hd => [_  ww]; move/andP:(ww) => [dpb _].
   move: (He a b l1 lsab dpa dpb hc xp) => sftx.
   by move:(DP_NH1_prop4 dpa sftx); rewrite - xp ww.
clear a b l1 l2.
move => d1 d2.
move En: (size d1 + size d2) => n.
have: size d1 <= n by rewrite -En ; apply leq_addr.
have: size d2 <= n by rewrite -En ; apply leq_addl.
have T a l: all DP_FT_DH1 (a :: l) -> ~~ nilp (flatten (a :: l)).
   by move=> /= /andP[/andP[]]; case:a => //.
elim: n d1 d2 {En}.
  by move => d1 d2; rewrite !leqn0 => /nilP -> /nilP.
move => n Hr; case. 
  by case => // a l _ _ _;move/T => sa sb; move: sa; rewrite - sb.
move => a d1; case; first by move => _ _ /T sa _ sb ; move: sa; rewrite  sb.
move => b d2 /=;rewrite 2!ltnS; wlog:a d1 b d2 /size a <= size b.
  move => hh; case /orP:(leq_total (size a) (size b)); first by apply: hh.
  by move => sa sb sc ha hb /esym hc; symmetry; apply:hh.
move => lsab sd2n sd1n /andP[ph1 ph2] /andP[ph3 ph4] sv {T}.
suff eab: a = b.
  move /eqP: sv; rewrite eab eqseq_cat // eqxx /= => /eqP ha.
  by rewrite (Hr _ _ sd2n sd1n ph2 ph4 ha). 
move: (f_equal (take (size b)) (esym sv)); rewrite take_size_cat //.
rewrite take_cat ltnNge lsab /=.
move: lsab;rewrite leq_eqVlt => /orP; case => lsab.
  by rewrite (eqP lsab) subnn take0 cats0.
move: ph1 ph3 lsab; rewrite /DP_FT_DH1 !starts_withFT_prop.
move => /andP [/eqP {2 3 4} -> /andP [dpa pa]].
move=> /andP[/eqP {2 3 4} -> ww]; move/andP:(ww)=>[dpb pb].
rewrite /= 2!ltnS => lsab; case => xp.
have sftx:= (He _ _  d1 lsab dpa dpb ph2 xp).
by move:(DP_NH1_prop4 dpa sftx); rewrite - xp ww. 
Qed.




Lemma DP_FT_DH1_unique d1 d2:
  all DP_FT_DH1 d1 -> all DP_FT_DH1 d2 -> flatten d1 = flatten d2 -> d1 = d2.
Proof.
move => pa pb; apply:DP_FT_DH1aux_unique; rewrite /DP_resizeb_condition.
+ by move: pa;case: d1 => // b l /=; move/andP => [-> ->].
+ by move: pb;case: d2 => // b l /=; move/andP => [-> ->].
Qed.

Definition Dyck_lp_aux l := prependFT (DP_lower l).
Definition Dyck_rp_aux l := DP_raise (drop 2 l).

Lemma Dyck_lp_auxK l: Dyck_irred l ->  Dyck_rp_aux(Dyck_lp_aux l) = l.
Proof.
by move => /andP[/eqP pa _]; rewrite / Dyck_rp_aux/Dyck_lp_aux /= drop0 - pa.
Qed.

Lemma Dyck_rp_auxK l: starts_withFT l ->
   Dyck_lp_aux (Dyck_rp_aux l) = l.
Proof.
by rewrite /Dyck_rp_aux/Dyck_lp_aux DP_raiseK starts_withFT_prop => /eqP.
Qed.

Definition DP_NH2 l:= 
   all (fun s => (DP_NH1 (DP_lower s))) (DP_splitc l).
Definition Dyck_NH2 l:= Dyck_path l && DP_NH2 l.

Definition Dyck_lp l :=
  drop 2 (flatten [seq  Dyck_lp_aux s | s <- DP_splitc l]).

Definition Dyck_rp_aux2 l := 
  DP_resizeb (DP_split_resize (DP_splitc (prependFT l))).

Definition Dyck_rp l := 
  (flatten [seq  Dyck_rp_aux s | s <- Dyck_rp_aux2 l]).

Lemma Dyck_rp_prop l (u:= Dyck_rp_aux2 l) (u' := [seq Dyck_rp_aux s | s <- u]) :
  Dyck_path l -> 
  [&& all DP_FT_DH1 u, flatten u == prependFT l, DP_splitc (flatten u') == u' &
   [seq Dyck_lp_aux s | s <- u'] == u ].
Proof.
move => dl.
have ha:Dyck_path (prependFT l) by exact:(Dyck_path_cat DyckFT_Dyck dl).
have hb: starts_withFT (prependFT l) by [].
move:(DP_split_resizeb_correct  ha hb). 
 rewrite -/u;  move/andP => [up flu]; rewrite up flu /=.
have hu': (all Dyck_irred u').
  apply/allP => x /mapP [y /(allP up) /andP [_ /andP [sa2 _]] ->]. 
  by rewrite /Dyck_rp_aux /Dyck_irred DP_raiseK sa2 eqxx.
rewrite /Dyck_lp (DP_splitc_unique hu' (erefl (flatten u'))) eqxx - map_comp.
simpl; apply/eqP;apply: map_id_in => x  /(allP up) /andP [ sa sb]. 
by apply:Dyck_rp_auxK.
Qed.

Lemma Dyck_rp_aux_size x: starts_withFT x -> size (Dyck_rp_aux x) = size x.
Proof. 
by rewrite starts_withFT_prop /Dyck_rp_aux /= size_rcons => /eqP{2} ->.  
Qed.

Lemma Dyck_lp_size n l: Dyck_path l -> size l = n.+1.*2 ->
  size (Dyck_lp l) = n.*2.
Proof.
move => h.
rewrite -{1}(DP_splitc_recover l). 
rewrite /Dyck_lp size_drop !size_flatten.
set A := shape _; set B := shape _; suff: A = B by move => -> ->; rewrite subn2.
rewrite /A/B; move:(DP_splitc_correct h);elim: (DP_splitc l) => // a s Hr.
move => /= /andP [/andP[/eqP {2} -> _] /Hr <-]. 
by rewrite /DP_raise /= size_rcons.
Qed.

Lemma Dyck_rp_size  l: Dyck_path l -> size (Dyck_rp l) = (size l).+2.
Proof.
move => dp.
move:(Dyck_rp_prop dp) => /and4P[ha /eqP hb _ _].
move/(f_equal size): hb; rewrite[size (prependFT l)] /= => <-.
rewrite 2!size_flatten /shape -map_comp /comp; congr sumn; apply/ eq_in_map.
by move => t /(allP ha)/andP[tu _]; apply:Dyck_rp_aux_size. 
Qed.

Lemma Dyck_lp_Dyck n l: Dyck_path l -> size l = n.+1.*2 ->
  Dyck_path (Dyck_lp l).
Proof.
move => ha hb; rewrite /Dyck_lp.
move:(DP_splitc_recover l)(DP_splitc_correct ha); case:(DP_splitc l).
   by move => hc; move:hb; rewrite -hc.
move=> a s _ /= /andP[/andP [_ hd] he]; rewrite drop0;apply: (Dyck_path_cat hd).
move: he; clear; elim:s => // a l Hr.
move => /= /andP[ha hb] /=; rewrite - 2!cat_cons (Dyck_path_cat _ (Hr hb)) //.
move/andP: ha =>[_ ha']; apply:(Dyck_path_cat DyckFT_Dyck ha').
Qed.


Lemma Dyck_rp_Dyck l: Dyck_path l ->  Dyck_path (Dyck_rp l).
Proof.
have H s:  (all Dyck_path s) -> Dyck_path (flatten s).
  elim:s => // a s H /= /andP[ha hb]; apply: (Dyck_path_cat ha (H hb)).
have K x:DP_FT_DH1 x -> Dyck_path (Dyck_rp_aux x).
  move/andP => [sft /andP [hu hv]]; exact:(Dyck_path_augment hu).
rewrite/Dyck_rp => dp; apply: H.
have ha:Dyck_path (prependFT l) by exact:(Dyck_path_cat DyckFT_Dyck dp).
have hb: starts_withFT (prependFT l) by [].
move:(DP_split_resizeb_correct  ha hb) => /andP[hc hd].
rewrite all_map; apply/allP => x /(allP hc) /=; apply:K.
Qed.


Lemma Dyck_rpK l: Dyck_path l -> Dyck_lp (Dyck_rp l) = l.
Proof.
move => dl;rewrite /Dyck_rp/Dyck_lp.
move: (Dyck_rp_prop dl) => /and4P [ha hb hc hd].
by rewrite (eqP hc) (eqP hd) (eqP hb) /= drop0.
Qed.

Lemma Dyck_rp_H2 l: Dyck_path l -> Dyck_NH2 (Dyck_rp l).
Proof.
move => dl.
rewrite /Dyck_NH2/DP_NH2 (Dyck_rp_Dyck dl) /=.
move:(Dyck_rp_prop dl) => /and4P; rewrite /Dyck_rp.
set u:=Dyck_rp_aux2 l; set v := [seq Dyck_rp_aux s | s <- u].
move => [ha hb hc hd]; rewrite (eqP hc).
apply/allP => x /mapP [y /(allP ha) /andP[pa /andP[pb pc]] ->].
by move:pc; rewrite - {1} (Dyck_rp_auxK pa) /Dyck_lp_aux /= drop0.
Qed.

Lemma Dyck_lpK n l: Dyck_NH2 l -> size l = n.+1.*2 ->
   Dyck_rp (Dyck_lp l) = l.
Proof.
move => /andP[ha hb] hc. 
have dlp:=(Dyck_lp_Dyck ha hc).
have hd:= (DP_splitc_correct ha).
move: hc;rewrite - {1 3} (DP_splitc_recover l).
set sl := (DP_splitc l).
case nl: (nilp sl); first by move/nilP:nl ->.
move => _; clear n.
have slv: sl = (head nil sl) :: behead sl by move: nl; clear; case:sl => //.
rewrite /Dyck_lp/Dyck_rp /Dyck_rp_aux2 -/sl.
set s1 := (flatten [seq Dyck_lp_aux s | s <- sl]).
have s1v: s1 = (prependFT (drop 2 s1)) by rewrite /s1 -/sl slv /= drop0//.
rewrite - s1v.
have pa: Dyck_path s1.
  move:dlp;rewrite /Dyck_lp -/s1 {2} s1v => su.
  exact:(Dyck_path_cat DyckFT_Dyck su).
have pb: starts_withFT s1 by rewrite s1v.
move:(DP_split_resizeb_correct pa pb).
set u := DP_resizeb _; move/andP=>[pc pd].
have ff: flatten u = flatten [seq Dyck_lp_aux s | s <- sl] by rewrite (eqP pd).
have pc' : all DP_FT_DH1 [seq Dyck_lp_aux s | s <- sl]. 
   apply/allP => x /mapP [y ysl ->]; rewrite/Dyck_lp_aux.
   move/(allP hd): (ysl) => /andP[_ qa2].
   by move/(allP hb): ysl => qb; rewrite /DP_FT_DH1 /= drop0 /Dyck_NH1 qa2 qb.
rewrite (DP_FT_DH1_unique pc pc' ff) - map_comp /comp map_id_in //.
by move => x /(allP hd) /Dyck_lp_auxK. 
Qed.


Lemma cardinal_Dyck_NH2 n: 
  #|[set s: (n.+1.*2).-tuple bool | Dyck_NH2  s ]| = catalan n.
Proof.
rewrite - cardinal_Dyck_path. symmetry.
set T1:= (n.*2).-tuple bool; set T2:= (n.+1.*2).-tuple bool.
pose hack (l: seq bool) := take (n.+1.*2) (l ++ (nseq  (n.+1.*2.+1) false)).
have hack1 l: size l = (n.+1.*2) -> hack l = l. 
  by move => ss; rewrite /hack take_size_cat.
have hack2 l: size (hack l) =  (n.+1).*2.
  by rewrite /hack size_take size_cat size_nseq addnS ltnS leq_addl.
have ha (x:T1) : size (hack (Dyck_rp x)) == (n.+1.*2).
   by rewrite hack2. 
have hb (x:T1): Dyck_path x -> hack(Dyck_rp x) = (Dyck_rp x).
  by move => h; apply:hack1; rewrite (Dyck_rp_size h) /= size_tuple.
pose f l := Tuple (ha l);set lhs := [set s | _].
have aux: {in lhs &, injective (fun x => (Tuple (ha x)))}.
  move => u v; rewrite !inE => du dv; case; rewrite hb // hb // => eq.
  by apply/val_inj; rewrite /= -(Dyck_rpK du) -(Dyck_rpK dv) eq.
rewrite - (card_in_imset aux); apply:eq_card => x; rewrite !inE.
apply/imsetP/idP. 
   by move => [y]; rewrite inE => dy ->; rewrite /= hb //; apply:Dyck_rp_H2.
move => h2; move/andP:(h2) => [dpx _].
have sx:size x = n.+1.*2 by rewrite size_tuple.
move:(Dyck_lpK h2 sx)=> hh.
have dl:=(Dyck_lp_Dyck dpx sx).
move:(Dyck_lp_size dpx sx) => /eqP ss.
exists (Tuple ss); first by rewrite inE. 
by apply:val_inj; rewrite /= (Dyck_lpK h2 sx) hack1.
Qed.

(* --------------- *)

(* nombre de functions [1,n] -> [1,n] avec f(1)=1 et f(i+1)<= f(i)+1
  ou nombre de functions In -> In avec f(0)=0 et f(i+1)<= f(i)+1 *)
(* nombre de functions [1,n] -> [0,n], Sfi<=i, Sfn =n
   avec Sfi = \sum_(1<=k<=i) f i
*)

(* number of derangements *)
Fixpoint nder_rec n :=
  if n is n1.+1 then
    if n1 is n2.+1 then n1 *(nder_rec n1 + nder_rec n2)
    else 0
  else 1.

Definition nder := nosimpl nder_rec.

Lemma nderE : nder = nder_rec.
Proof. by []. Qed.

Lemma nder0: nder 0 = 1.  Proof. by []. Qed.
Lemma nder1: nder 1 = 0.  Proof. by []. Qed.
Lemma nderS n : nder (n.+2) = (n.+1) * (nder n.+1 + nder n).  
Proof. by []. Qed.

Lemma nbder_gt0 n: 0 < nder n.+2.
Proof. by elim:n => // n ha;  rewrite nderS muln_gt0 addn_gt0 ha. Qed.

Lemma nbder_even_gt0 n: ~~ odd n -> 0 < nder n.
Proof. case:n => // [] // [] // n _; apply: nbder_gt0 n. Qed.

Lemma nderS' n (m := (n.+1) *(nder n)): 
   nder (n.+1) = if (odd n) then m.+1 else m.-1. 
Proof.
rewrite/m; clear;elim:n => //n Hr.
rewrite nderS Hr /= mulnDr (mulSn n.+1) addnC; case on: (odd n).
  by rewrite addSn.
by rewrite /= -addSn prednK // muln_gt0 /= nbder_even_gt0 // on.
Qed.

(* ne sert pas *)
Lemma split_sum_even_odd (F: nat -> nat) n:
  \sum_(i<n) (F i) = \sum_(i< (n.+1)./2) (F i.*2) + \sum_(i< n./2) (F i.*2.+1).
Proof.
have H k: \sum_(i<k.*2) (F i) = \sum_(i< k) (F i.*2) + \sum_(i< k) (F i.*2.+1).
  elim:k; first by rewrite !big_ord0.
  by move => k Hr; rewrite doubleS !big_ord_recr /= Hr addnACA addnA.
have: n = (n./2).*2.+1 \/ n = (n./2).*2.
  by rewrite -{1 3} (odd_double_half n);case: (odd n); [left | right].
by case => ->; rewrite (half_bit_double n./2 true) -? doubleS
   doubleK ? big_ord_recr H // addnAC. 
Qed.

Lemma nder_sum n: \sum_(i< n.+1) 'C(n,i) * nder i = n `!.
Proof.
elim:n; first by rewrite big_ord_recl big_ord0 //.
move => n Hr.
have np: 0< n.+1 by [].
rewrite big_ord_recl /= bin0 nder0 mul1n (bigID (fun i : 'I_n.+1 => odd i)) /=.
have ->: \sum_(i < n.+1 | odd i) 'C(n.+1, bump 0 i) * nder (bump 0 i) =
  \sum_(i < n.+1 | odd i) 'C(n.+1,i.+1) +
  \sum_(i < n.+1 | odd i) 'C(n.+1,i.+1) * ((i.+1) *(nder i)).
  rewrite addnC -big_split /=.
  by apply:eq_big=> //[[i lin]] /= oi; rewrite nderS' oi /bump add1n addnC mulnS.
rewrite 2! addnA.
have <-:  2^n = 1 + \sum_(i < n.+1 | odd i) 'C(n.+1, i.+1).
  rewrite - (F25 np) big_mkcond big_ord_recl /= bin0 // -big_mkcond; congr addn.
  by apply:eq_big=> // i /=; case: odd.
have ->:2 ^ n  = \sum_(i < n.+1 | ~~ odd i) 'C(n.+1, i.+1).
  rewrite - (F24 np) big_mkcond big_ord_recl /= add0n  -big_mkcond //.
rewrite addnAC  -big_split /=.
have ->: \sum_(i < n.+1 | ~~ odd i)
      ('C(n.+1, i.+1) + 'C(n.+1, bump 0 i) * nder (bump 0 i)) = 
  \sum_(i < n.+1 | ~~odd i) 'C(n.+1, i.+1) * (i.+1 * nder i).
  apply: eq_big => // [[i lin]] /= oi; rewrite  nderS' (negbTE oi).
  by rewrite - mulnS prednK // muln_gt0 /= nbder_even_gt0.
rewrite addnC - (bigID (fun i : 'I_n.+1 => odd i) predT) /=.
transitivity ( \sum_(i < n.+1)  (n.+1) * ('C(n, i) *nder i)).
  by apply:eq_big => // [[i lin]] /= _; rewrite !mulnA mul_bin_diag (mulnC i.+1).
by rewrite - big_distrr /= Hr factS.
Qed.



Lemma DP_splita_pos2 l: DP_pos (DP_splita l).2.
Proof.
elim:l => // a l Hr /=.
case ha: (nilp (DP_splita l).1) => //. 
move: (DP_splita_recover l) Hr; move/nilP: ha => -> /= -> H. 
by case: leqP => //= ->; rewrite H.
Qed.

(** ---- Compute the sum of binomial coefficients with alternate signs  *)

(** --- Exercise5_4 : 
The number of functions [ f:'I_m -> 'I_(n.+1) ]
 such that [\sum_(i<m) (f i)<=n]  is  ['C(n+m,m) ]. If the condition is 
replaced by [\sum_(i<m) (f i) = n ], the number becomes [ 'C(n+m,m) ] *)

Definition Ftype m n := {ffun 'I_m -> 'I_n.+1}.

Definition monomial_lt m n (f:Ftype m n) :=  \sum_(i<m) (f i) < n.
Definition monomial_le m n (f:Ftype m n) :=  \sum_(i<m) (f i) <= n.
Definition monomial_eq m n (f:Ftype m n) :=  \sum_(i<m) (f i) == n.

Lemma G3_a (m n: nat): #|[set f:Ftype m n  | monomial_le  f ]| 
  =  #|[set f:Ftype m n  | monomial_eq f ]|
  +  #|[set f:Ftype m n  | monomial_lt f ]|.
Proof.
symmetry; rewrite ! card_set_pred.
rewrite -  (cardID  [pred f | monomial_eq f]  [pred f | monomial_le f]).
congr (_ + _).
  apply: eq_card => f; rewrite !inE /monomial_eq /monomial_le.
  by case: eqP; [ move => -> //=; rewrite leqnn | rewrite andbF].
by apply: eq_card => f; rewrite !inE  /monomial_lt ltn_neqAle.
Qed.


Lemma G3_b (m n: nat):  
  #|[set f:Ftype m n.+1  | monomial_lt f ]| =
  #|[set f:Ftype m n  | monomial_le  f ]|. 
Proof.
pose R (f:Ftype m n) :=  [ffun i:'I_m => widen_ord (leqnSn n.+1) (f i)].
have injR: (injective R). 
   move => f g ; rewrite - ffunP - ffunP => sr i; apply: ord_inj.
   move: (sr i); rewrite /R !ffunE => eq1.
   by move: (f_equal (@nat_of_ord n.+2) eq1).
symmetry; rewrite card_set_pred - (card_image injR [pred f | monomial_le f]).
rewrite - imset_card.
apply: eq_card=> s; rewrite in_set; apply /imsetP; case:ifP.
  rewrite /monomial_lt => les.
  have vln: forall i, s i < n.+1.
    move => i; move: les; rewrite (bigD1 i) //=.
    apply: leq_trans;apply: leq_addr.
  pose x:=  [ffun i:'I_m => Ordinal (vln i)].
  exists x. 
    rewrite inE /=; move: les; rewrite /monomial_le  ltnS.
    have -> //: \sum_(i < m) s i = \sum_(i < m) x i.
    by apply: eq_big => // i _; rewrite /x ffunE.
  by rewrite /R -ffunP => i; rewrite ffunE ffunE; apply: ord_inj.
move=> lef [x]; rewrite inE /=; move => lex sr; move: lef lex.
rewrite /monomial_lt /monomial_le sr /R /= ltnS.
set s1 := \sum_(i < m) _; set s2 := \sum_(i < m) _.
have : s1 = s2 => [ | -> -> // ].
by apply:  congr_big => // i _; rewrite ffunE.
Qed.


Lemma G3_c (n: nat): #|[set f:Ftype 0 n  | monomial_le  f ]| = 1.
Proof.
set f0: (Ftype 0 n):= [ffun  _ => ord0].
apply /eqP/cards1P; exists f0; rewrite -setP => g; rewrite in_set1 in_set.
by apply/eqP; case:ifP; [ rewrite big_ord0 | case/eqP /ffunP; case].
Qed.

Lemma G3_d (m: nat): #|[set f:Ftype m 0  | monomial_le  f ]| = 1.
Proof.
set f0: (Ftype m 0):= [ffun  _ => ord0].
apply /eqP/cards1P; exists f0; rewrite -setP => g; rewrite in_set1 in_set. 
apply/eqP; case:ifP.
  by move /eqP => ->; rewrite subn0 big1 => // => i _; rewrite /f0 ffunE.
move /eqP; case; rewrite - ffunP;  move => t; rewrite /f0 ffunE. 
by apply: val_inj; case: (g t); case. 
Qed.

Lemma G3_e (m n: nat): #|[set f:Ftype m.+1 n  | monomial_eq  f ]| 
  =  #|[set f:Ftype m n  | monomial_le f ]|.
Proof.
set T:= Ftype m.+1 n.
pose restr (f:T):= [ffun z:'I_m => f (widen_ord (leqnSn m) z)].
have restr_pr1: forall f: T,  monomial_eq f ->
   n =  \sum_(i<m) ((restr f) i) + f ord_max.
  move => f; rewrite /monomial_eq; move /eqP => le1. 
  rewrite -{1}le1 big_ord_recr /restr; congr( _ + _) =>//=.
  by apply: congr_big => // i _ /=; rewrite  ffunE.
have restr_pr2: forall f: T,  monomial_eq f -> monomial_le (restr f).
  move => f feq; rewrite /monomial_le; move: (restr_pr1 _ feq).
  move: (\sum_(i < m) restr f i) => n0 Hn.
  by rewrite Hn; apply: leq_addr.
have restr_inj: {in [pred f | (monomial_eq f)] &, injective restr}. 
  move => f1 f2.
  rewrite !inE  => meq1 meq2 sr;rewrite - ffunP =>  i.
  move: (ltn_ord i); rewrite ltnS leq_eqVlt; case /orP => lim.
    have -> : i = ord_max by apply: ord_inj;by move:lim; move /eqP => ->.
    apply: ord_inj.
    by apply: (@addnI (\sum_(i < m) (restr f1) i)); rewrite {2} sr - !restr_pr1.
  move: sr;rewrite - ffunP => sr; move:  (sr (Ordinal lim)).
  rewrite !ffunE.  
  have -> // : (widen_ord (leqnSn m) (Ordinal lim)) = i; by exact: ord_inj.
move: (card_in_imset restr_inj); rewrite - card_set_pred.
rewrite - [in X in (_ = X)]card_set_pred; move => <-.
apply:eq_card => f; rewrite in_set in_set; apply /imsetP. 
case: ifP => lef; last first.
   by move=> [x]; rewrite inE  => meq fr; move:lef; rewrite fr restr_pr2.
move: (leq_subr (\sum_(i < m) f i)  n); rewrite -ltnS => le2.
pose g : {ffun ordinal_finType m.+1 -> ordinal_finType n.+1} :=
  [ffun i:'I_(m.+1) => if (unlift ord_max i)  is Some j then f j
    else (Ordinal le2)].
have gi : forall i: 'I_m, g (widen_ord (leqnSn m) i) = f i.
  move => i; rewrite /g ffunE. 
  have -> : (widen_ord (leqnSn m) i) = (lift ord_max i).
      by apply: ord_inj; rewrite lift_max.
   by rewrite  liftK.
have gs: \sum_(i < m) g (widen_ord (leqnSn m) i) =  \sum_(i < m) f i.
    by apply: congr_big => // i _; move: (gi i) => /= ->.
exists g.
   rewrite !inE /monomial_eq big_ord_recr gs /g ffunE unlift_none /=. 
   by rewrite addnC subnK.
by rewrite - ffunP => i; rewrite ffunE gi.
Qed.

Lemma G3_f m n:  #|[set f:Ftype m n  | monomial_le  f ]|  = 'C(n+m,m).
Proof. 
move:n;elim: m; first by move => n; rewrite bin0 G3_c.
move => n hrec.
elim; first by rewrite add0n binn  G3_d.
by move => m hrec1;rewrite G3_a G3_b G3_e addnC hrec1 hrec !addnS binS.
Qed.


Lemma subseq_iota a n b m :  b <=a -> a + n <= b + m ->
    subseq (iota a n) (iota b m).
Proof.
move => ba.
move: (subnK ba); rewrite addnC => <-; rewrite - addnA leq_add2l => le1.
move: (leq_trans (leq_addr n (a-b)) le1) => aux.
move: (iotaD b (a-b)(m -(a-b))); rewrite addnC (subnK aux) => ->.
rewrite -{1}(cat0s (iota (b + (a - b)) n)); apply: cat_subseq => //.
  apply: sub0seq.
have nm: n <= (m - (a - b)) by rewrite -(leq_add2l (a-b)) subnKC //.
set c := (b + (a - b)); move: (iotaD  c n ((m - (a - b)) - n)).
rewrite addnC (subnK nm) => ->.
rewrite -{1}(cats0 (iota c n)); apply: cat_subseq => //; apply: sub0seq.
Qed.

Lemma subseq_iota1 i m: i<m -> subseq ([:: i;  i.+1]) (iota 0 m.+1).
Proof.
have  ->: [:: i;  i.+1] = iota i 2 by  [].
by move => im; apply: subseq_iota => //; rewrite add0n addn2 ltnS.
Qed.


Lemma sorted_prop  f m:
   sorted ltn (mkseq f m.+1) <-> (forall i, i<m -> f i < f (i.+1)).
Proof.
split.
  move => h i im.
  move: (map_subseq f (subseq_iota1 im)); rewrite -/(mkseq f m.+1) => pb.
  have tr_ltn: (transitive ltn) by  move => a b c ; apply: ltn_trans.
  by move: (subseq_sorted tr_ltn pb h)=> /=; rewrite andbT.
move => fi. simpl.
move: m f fi; elim => [  //= | n hrec f fi /=].
rewrite (fi 0 (ltn0Sn n)) /=.
set f' := f \o (addn 1).
have fi': (forall i, i < n -> f' i < f' i.+1) by move => i lin; rewrite fi.
move: (hrec _ fi'); rewrite map_comp /f' /= addn0 - iotaDl //.
Qed.

(* Variant *)
Lemma G3_f' (m n: nat):
 #|[set f:Ftype m n  | monomial_le  f ]| = 'C(n+m,m).
Proof.
case:m; first by rewrite bin0  G3_c.
move => m.
rewrite addnS - card_ltn_sorted_tuples.
set Ta:= Ftype m.+1 n.
pose toseq (f:Ta) :=  map_tuple [ffun z:'I_(m.+1) => 
               @inord (n+m) (\sum_(i<(m.+1) | i<=z) (f i) + z)] 
  (ord_tuple (m.+1)).
pose ps (f:Ta) z := \sum_(i<(m.+1) | i<=z) (f i) + z.
have ps0: forall (f: Ta), ps f 0 = f ord0.
  move => f; rewrite /ps addn0 (big_pred1 ord0) //= => t /=.
  by rewrite /leq subn0.
have psr: forall (f: Ta), forall z (H: z.+1 < m.+1),
    ps f z.+1 = (ps f z) + (f (Ordinal H)) +1.
    move => f z h; rewrite /ps.
    rewrite addnS - addn1; congr (_ + 1); rewrite addnAC;  congr (_ + z).
    rewrite addnC (bigD1 (Ordinal h)) //=; congr (_ + _).
    by apply: eq_bigl => s; rewrite -(ltnS s z) ltn_neqAle andbC.
have psi: forall f g, (forall i, i< m.+1 -> ps f i = ps g i) -> f = g.
  move => f g fgi; rewrite - ffunP; case => i => ile; move: ile; case:i.
    move => h //. 
    have ->: Ordinal h = ord0 by  apply: ord_inj.
    by apply: ord_inj; rewrite -  (ps0 f) - (ps0 g) fgi.
  move => i ile; apply: ord_inj.
  move: (fgi _ ile); rewrite psr psr - (fgi _ (leq_trans (leqnSn i) ile)). 
  by move /eqP; rewrite eqn_add2r eqn_add2l; move /eqP.
have toseq1: forall f:Ta,  monomial_le f ->
     forall z: 'I_(m.+1),  ps f z <= n + m.
  move =>f mle z; apply: leq_add; last by move: z => [z] i //=.
  apply: leq_trans mle.
  rewrite (bigID (fun i:'I_(m.+1) => i <= z) xpredT) /= ; apply: leq_addr.
have toseq2: forall f:Ta,  monomial_le f -> forall z: 'I_(m.+1),
   nat_of_ord (@inord (n+m) (ps f z)) = ps f z.
   by move => f mle z; move: (toseq1 f mle z) => le2 /=; rewrite insubdK.
have toseq3: forall f:Ta,  monomial_le f -> forall z: 'I_(m.+1),
  nat_of_ord (tnth (toseq f) z) = ps f z.
  by move => f mle z; rewrite tnth_map tnth_ord_tuple ffunE toseq2.
have toseq_inj: {in [pred f | (monomial_le f)] &, injective toseq}. 
  move => f1 f2; rewrite  !inE /= => fle1 fle2 sseq; apply: psi => i lim.
  move: (toseq3 _ fle1 (Ordinal lim)) => /= <-.
  by rewrite sseq  (toseq3 _ fle2 (Ordinal lim)).
have toseq4:  forall f:Ta,  monomial_le f -> 
   (map val (toseq f)) = mkseq (ps f) m.+1.
  move => f mle.
  have s1: size (map val (toseq f)) = m.+1.
    by rewrite size_map size_map size_tuple.
   apply: (eq_from_nth (x0:=0)).
     by rewrite  s1 size_mkseq. 
  move => i; rewrite s1 => lim.
  set k := (tnth_default (toseq f) (Ordinal lim)).
  have lim1: i < size (toseq f) by rewrite size_map size_tuple.
  rewrite (nth_mkseq _ _ lim) (nth_map k 0) //.
  have  ->: (nth k (toseq f) i) =  tnth (toseq f) (Ordinal lim) by [].
  by move: (toseq3 f mle (Ordinal lim)) => /= <-.
have toseq_ord: forall f:Ta,  
  monomial_le f ->  sorted ltn (map val (toseq f)).
  move => f mle.
  rewrite (toseq4 _ mle) sorted_prop => i im.
  by rewrite psr; rewrite addn1 ltnS leq_addr.
rewrite  card_set_pred - (card_in_image toseq_inj).
rewrite - card_set_pred; apply: eq_card => g.
rewrite ! in_set; apply/mapP.
case: ifP; last first.
   move=> lef [x]; rewrite mem_enum inE /= => meq fr.
   by move:lef; rewrite fr; move /negP; apply; apply: toseq_ord.
pose v1 i := val (tnth g (inord  i)).
have v1p: forall i:'I_m.+1, v1 i = val (tnth g i).
  move => i; rewrite /v1 inord_val ;  congr (tnth g _) => /=; apply: val_inj. 
have ->: (map val g) = mkseq v1 m.+1.
  rewrite - map_tnth_enum -map_comp /mkseq - val_enum_ord -(map_comp v1).
  by apply /eq_in_map => i _ => /=; rewrite v1p.
rewrite sorted_prop => vi.
pose v2 i := v1 (i.+1) - v1 (i) -1.
have v2p: forall i, i<m -> v1 i.+1 = v1 i + v2 i +1.
  move => i im; move: (vi _ im); rewrite /v2 => cp1.
  by rewrite addnAC - subnDA addn1 - {1}(subnKC cp1).
pose v2' i := if i is j.+1 then v2 j else v1 0.
pose v3 z := (\sum_(i<(m.+1) | i<=z) (v2' i) + z).
have v30: v3 0 = v1 0.
   rewrite /v3 addn0 (big_pred1 ord0)  //= => t /=.
   by rewrite /leq subn0.
have v3r: forall z, z < m -> v3 z.+1 = v3 z + (v2 z) +1.
    move => z h; rewrite /v3; rewrite - ltnS in h.
    rewrite addnS - addn1; congr (_ + 1); rewrite addnAC;  congr (_ + z).
    rewrite addnC (bigD1 (Ordinal h)) //=; congr (_ + _).
    by apply: eq_bigl => s; rewrite -(ltnS s z) ltn_neqAle andbC.
have v31: forall z, z < m.+1 -> v3 z = v1 z.
  elim => [ // | i hrec]; rewrite  ltnS => im.
  by rewrite (v3r _ im) (v2p _ im) hrec //; apply:(ltn_trans im (ltnSn m)).
  have v3m: v3 m = (\sum_(i<(m.+1)) (v2' i) + m).
     by rewrite /v3; congr ( _ + m); apply: congr_big => //; case.
have v1in: forall i, i<m.+1 -> v1 i < (n + m).+1.
  by move => i lim; rewrite /v1; set x := tnth _ _; case x => [j] imn.
have svln: \sum_(i < m.+1) (v2' i) <= n.
  by rewrite - (leq_add2r m) - v3m (v31 m (ltnSn m)) -ltnS (v1in m (ltnSn m)).
have vln: forall i, i < m.+1 -> v2' i < n.+1.
  move => i lim; rewrite ltnS; move: svln.
  rewrite (bigD1 (Ordinal lim)) //=; apply: leq_trans;apply: leq_addr.
set f:= [ffun i:'I_(m.+1) => (Ordinal (vln _ (ltn_ord i)))].
have sf: \sum_(i < m.+1) f i = \sum_(i < m.+1) v2' i.
  by apply: congr_big => //; move => [i] im _; rewrite ffunE. 
exists f; first by rewrite mem_enum inE /= /monomial_le sf.
apply: eq_from_tnth => i.
apply: val_inj; rewrite -v1p tnth_map tnth_ord_tuple ffunE.
have -> : \sum_(i0 < m.+1 | i0 <= i) f i0 + i = v3 i.
  by rewrite /v3; congr(_ + i); apply: congr_big => // j ji; rewrite ffunE//.
symmetry; rewrite v31 => //; rewrite inord_val //.
Qed.

