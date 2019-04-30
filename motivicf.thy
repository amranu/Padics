theory motivicf
  imports "~~/src/HOL/Computational_Algebra/Formal_Power_Series"  
          "~~/src/HOL/Computational_Algebra/Polynomial"  
          "~~/src/HOL/Computational_Algebra/Polynomial_FPS"
          "~~/src/HOL/Algebra/Valued_Fields/pochhammer_monomials"
begin

abbreviation "Xp \<equiv> [:0, 1:]"

fun(in comm_ring_1) numer:: "nat \<Rightarrow> 'a" where
"numer 0 = zero "|
"numer (Suc n) = one + (numer n)"

definition(in comm_ring_1) int_numer:: "int\<Rightarrow> 'a" where
"int_numer n \<equiv> if (n \<ge>0) then (numer (nat n)) else - (numer (nat (-n)))"

(*maps p(n) and the series \<Sum>a_n to the series \<Sum>p(n)a_n  *)

definition pn:: "('a::comm_ring_1) poly \<Rightarrow> 'a fps \<Rightarrow> 'a fps" where
"pn p f =Abs_fps ( \<lambda>(n::nat). (poly p (numer n))*((fps_nth f) n))"

declare [[ smt_oracle = false ]]

(*if p is the polynomial p(x) = 1, then "f = pn p f" holds.*)
lemma pn_corr:
  assumes "f1 = pn p f0"
  assumes "p = Abs_poly (\<lambda>n. if n=0 then 1 else 0)"
  shows "f1 = f0"
proof-
  have "fps_nth f1 = fps_nth f0"
  proof
  fix n::nat
  show "fps_nth f1 n = fps_nth f0 n"
    proof-
     have "f1 = Abs_fps ( \<lambda>(n::nat). (poly p (numer n))*((fps_nth f0) n))" 
      using assms(1) by (simp add: pn_def) 
    then have "fps_nth f1 = fps_nth ( Abs_fps ( \<lambda>(n::nat). (poly p (numer n))*((fps_nth f0) n)))" 
      by simp 
    then have "fps_nth f1 = ( \<lambda>(n::nat). (poly p (numer n))*((fps_nth f0) n))" 
      by (simp add: Abs_fps_inverse)
    then have X: "fps_nth f1 n = (poly p (numer n))*((fps_nth f0) n)"
      by auto
    have A: "coeff p n \<equiv> if (n = 0) then 1 else 0" using assms(2) Abs_poly_inverse MOST_mono coeff degree_1 lead_coeff_1 mem_Collect_eq 
      by smt 
    then have D: "degree p = 0" using degree_def assms(2)
      by (smt Abs_poly_inverse MOST_mono coeff degree_0 degree_1 leading_coeff_0_iff mem_Collect_eq zero_neq_one)
    then have "(poly p (numer n)) = (\<Sum>i\<le>degree p. coeff p i * (numer n) ^ i)"  
      using poly_altdef by blast 
    then have "(poly p (numer n)) = (\<Sum>i\<le>0. coeff p i * (numer n) ^ i)"  
      using poly_altdef using D by simp 
    then have S: "(poly p (numer n)) = ( coeff p 0 * (numer n) ^ 0)" 
      by simp
    have "coeff p 0 = 1" using A 
      by (smt Abs_poly_inverse MOST_mono assms(2) coeff degree_1 lead_coeff_1 mem_Collect_eq) 
    then have "(poly p (numer n)) =  ( 1* (numer n) ^ 0)" using A S
      by simp 
    then have  "(poly p (numer n)) =  1" by simp
    then have "fps_nth f1 n = (fps_nth f0) n" using X 
      by simp 
    then show ?thesis  by auto
  qed
qed
  from this show "f1 = f0" 
    by (simp add: expand_fps_eq)
qed



(*Power series for inverses of (1 -x)^n*)

definition nat_geom_series:: "nat \<Rightarrow> nat fps" ("natgs _") where
"nat_geom_series n = fps_nth_deriv n (Abs_fps (\<lambda>k. 1))"


(*nat-valued function for generating coefficients of geometric series*)

fun nat_gcf:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
nat_gcf0: "nat_gcf 0 = (\<lambda>n. 1)"|
nat_gcfSuc :"nat_gcf (Suc n) = (\<lambda> k. pochhammer (k+1) (Suc n))" 

lemma nat_gcf_rec:
"nat_gcf (Suc n) k = (nat_gcf n k)*(k + Suc n)"
proof(induction n)
  case 0
  then show ?case by simp 
next
  case (Suc n)
  then show ?case 
    by (metis Suc_eq_plus1 add_Suc 
        add_Suc_right nat_gcf.simps(2)
        id_apply of_nat_eq_id pochhammer_Suc) 
qed

lemma nat_geom_series_alt_def: 
"nat_geom_series n = Abs_fps (\<lambda>k. nat_gcf n k) "
proof(induction n)
  case 0
  then show ?case 
    using nat_gcf0 by (simp add: nat_geom_series_def) 
next 
  case (Suc n)
  fix n
  assume IH: "(natgs n) = Abs_fps (nat_gcf n) "
  show "(natgs (Suc n)) = Abs_fps  (nat_gcf (Suc n))"
  proof-
    have "fps_nth (natgs (Suc n)) = nat_gcf (Suc n)"
    proof
      fix k::nat
      have P0: "fps_nth (natgs n) = nat_gcf n" using IH 
        by auto 
      then have "(natgs (Suc n)) = fps_deriv (natgs n)" 
        using fps_nth_deriv_commute nat_geom_series_def by auto 
      then have "fps_nth (natgs (Suc n)) k = (k+1)*(fps_nth (natgs n) (k+1))"
        by simp 
      then have "fps_nth (natgs (Suc n)) k = (k+1)*(nat_gcf n (k+1))" 
        using P0 by auto
      then have "fps_nth (natgs (Suc n)) k = pochhammer (k+1) (Suc n)"
        by (metis One_nat_def nat_gcf.elims mult.right_neutral
            pochhammer_1 pochhammer_rec) 
      then show "fps_nth (natgs (Suc n)) k = nat_gcf (Suc n) k"
        by simp 
    qed
    then show ?thesis 
      by (simp add: expand_fps_eq) 
  qed
qed

(*map a natural number power series into power series over an arbitrary semirings with 1 *)

definition of_nat_fps:: "nat fps \<Rightarrow> ('a::semiring_1) fps" where
"of_nat_fps f = Abs_fps (\<lambda>k. of_nat (fps_nth f k))"

(*of_nat_fps  is additive*)

lemma of_nat_fps_add:
"of_nat_fps (f + g) =(of_nat_fps f) + (of_nat_fps g)"
proof-
  let ?SUM = "fps_nth (of_nat_fps (f + g))"
  let ?F = "fps_nth (of_nat_fps f)"
  let ?G = "fps_nth (of_nat_fps g)"
  have P: "?SUM =(\<lambda> k. (?F k) + (?G k))"
  proof
    fix k
    show "?SUM k = ?F k + ?G k"
      by (simp add: of_nat_fps_def) 
  qed
  then show ?thesis 
    by (simp add: P fps_eq_iff) 
qed

(*of_nat_fps is multiplicative*)

lemma(in semiring_1) of_nat_fps_mult:
"of_nat_fps (f * g) =(of_nat_fps f) * (of_nat_fps g)"
proof-
  let ?PROD = "fps_nth (of_nat_fps (f * g))"
  let ?F = "fps_nth (of_nat_fps f)"
  let ?G = "fps_nth (of_nat_fps g)"
  have P: "?PROD = (\<lambda> k. \<Sum>i=0..k. ?F i * ?G (k - i))"
  proof
    fix k
    have P: "?PROD k = of_nat (fps_nth (f*g) k)"
      by (simp add: of_nat_fps_def) 
    then have P0: "?PROD k = of_nat (\<Sum>i=0..k. ((fps_nth f) i) * ((fps_nth g) (k - i)))"
      by (smt comm_monoid_add_class.sum.cong fps_mult_nth) 
    then have "?PROD k = (\<Sum>i=0..k. (of_nat ((fps_nth f) i)*((fps_nth g) (k - i))))"
      proof -
        have "of_nat (\<Sum>n = 0..k. fps_nth f n * fps_nth g (k - n)) = fps_nth (Abs_fps (\<lambda>n. of_nat (fps_nth (f * g) n)::nat)) k"
          by (metis (mono_tags, lifting) P P0 fps_nth_Abs_fps) 
        then have "(\<Sum>n = 0..k. of_nat (fps_nth f n) * fps_nth g (k - n)) = fps_nth (Abs_fps (\<lambda>n. of_nat (fps_nth (f * g) n))) k"
          by auto
        then show ?thesis
          by (simp add: of_nat_fps_def)
      qed
    then have P1: "?PROD k = (\<Sum>i=0..k. (of_nat ((fps_nth f) i))*(of_nat ((fps_nth g) (k - i))))"   
      using P0 by auto
    have P2: "?F =  (\<lambda> k. of_nat ((fps_nth f) k))"
      by (simp add: of_nat_fps_def Abs_fps_inverse) 
    have P3: "?G =  (\<lambda> k. of_nat ((fps_nth g) k))"
      by (simp add: of_nat_fps_def Abs_fps_inverse)
    then show "?PROD k = (\<Sum>i=0..k. (?F i)*(?G (k - i)))"    
      using P1 P2 P3 
    by (metis (mono_tags, lifting) comm_monoid_add_class.sum.cong) 
    qed
  have Q: "fps_nth ((of_nat_fps f) * (of_nat_fps g)) =(\<lambda> k. \<Sum>i=0..k. ?F i * ?G (k - i))"
    proof
      fix n 
      show "fps_nth ((of_nat_fps f) * (of_nat_fps g)) n = (\<Sum>i = 0..n. (?F i) * (?G (n - i))) "
        using fps_mult_nth  by blast 
    qed
  then show ?thesis 
    by (simp add: P Q expand_fps_eq) 
qed

(*of_nat_fps preserves derivatives*)

lemma(in semiring_1) of_nat_fps_deriv:
"fps_deriv (of_nat_fps f) = of_nat_fps (fps_deriv f)"
proof-
  let ?F = "fps_nth (fps_deriv (of_nat_fps f))"
  let ?G = "fps_nth (of_nat_fps (fps_deriv f))"
  have "?F = ?G"
  proof
    fix k
    show "?F k = ?G k"  
    proof-
      have "?F k =  (of_nat (k + 1) * (fps_nth (of_nat_fps f) (k + 1)))"
        by simp 
      then have  "?F k =  of_nat ((k + 1) *(fps_nth f (k + 1)))"
        by (smt fps_nth_Abs_fps of_nat_fps_def semiring_1_class.of_nat_mult) 
      then show ?thesis
        by (simp add: of_nat_fps_def)
    qed
  qed
  then show ?thesis
    using fps_nth_inject by blast
qed

lemma(in semiring_1)of_nat_fps_higher_deriv:
"fps_nth_deriv n  (of_nat_fps f) = of_nat_fps (fps_nth_deriv n f)"
proof(induction n)
  case 0
  then show ?case by simp 
next
  case (Suc n)
  then show ?case 
    by (metis fps_nth_deriv_commute of_nat_fps_deriv) 
qed

lemma of_nat_X:
"(of_nat_fps fps_X) = (fps_X ::('a::semiring_1) fps)"
  by (simp add: fps_ext of_nat_fps_def)

(*Geometric Series over different base rings. Proofs proceed mainly by transferring 
results from the nat case using the differential ring homomorphism of_nat_fps. The 
reason for doing nat first was to avoid having to grapple with type
differences in coefficients during proofs.*)

definition geom_series:: "nat \<Rightarrow> ('a::semiring_1) fps" ("gs _") where
"geom_series n = fps_nth_deriv n (Abs_fps (\<lambda>k. 1))"

(*Lemmas to show that geom_series agrees with the nat version*)

lemma geom_series_alt_def0: 
"(gs n) = of_nat_fps (natgs n)"
proof-
  let ?F = "fps_nth (gs n)"
  let ?G = "fps_nth (of_nat_fps (natgs n))"
  have "?F = ?G"
  proof
    fix k
    show "?F k = ?G k"
    proof -
      have f1: "\<forall>n. Abs_fps (nat_gcf n) = fps_nth_deriv n (Abs_fps (\<lambda>n. 1))"
        using nat_geom_series_alt_def nat_geom_series_def by presburger
      have "\<forall>n f. Abs_fps (\<lambda>na. of_nat (fps_nth (fps_nth_deriv n f) na)) = fps_nth_deriv n (Abs_fps (\<lambda>n. of_nat (fps_nth f n)::'c))"
        by (metis of_nat_fps_def of_nat_fps_higher_deriv)
      then show ?thesis
        using f1 by (simp add: geom_series_def nat_geom_series_alt_def of_nat_fps_def)
    qed 
  qed
  then show ?thesis
    using fps_nth_inject by blast
qed

fun gcf:: "nat \<Rightarrow> nat \<Rightarrow> ('a::comm_semiring_1)" where
gcf0: "gcf 0 = (\<lambda>n. 1)"|
gcfSuc :"gcf (Suc n) = (\<lambda> k. pochhammer (of_nat (k+1)) (Suc n))" 

lemma gcf_alt_def:
"gcf n k = of_nat (nat_gcf n k)"
  by (metis gcf.elims nat_gcf.elims
      of_nat_0 of_nat_0_neq of_nat_1
      pochhammer_of_nat) 

lemma gcf_rec:
"gcf (Suc n) k = (gcf n k)*(k + Suc n)"
proof(induction n)
  case 0
  then show ?case by simp 
next
  case (Suc n)
  then show ?case 
    using nat_gcf_rec by auto
qed

lemma geom_series_alt_def1: 
"geom_series n = Abs_fps (\<lambda>k. gcf n k) "
proof-
  let ?F = "fps_nth (gs n)"
  let ?G = "(\<lambda>k. gcf n k)"
  have P: "?F = ?G"
  proof
    fix k
    have "?F k = fps_nth ( of_nat_fps (natgs n)) k"
      by (simp add: geom_series_alt_def0) 
    then show "?F k = ?G k"
      by (simp add: gcf_alt_def 
          nat_geom_series_alt_def of_nat_fps_def) 
  qed
  then show ?thesis 
    by (metis fps_nth_inverse)
qed

(*Lemma for decomposing sums*)

lemma(in semiring_0) sum_decomp:
  assumes "k > (j::nat)"
  shows "(\<Sum>i=0..k. (f i)) = (\<Sum>i=0..j. (f i)) + (\<Sum>i=(j+1)..(k). (f i))"
proof-
  let ?m = "(0::nat)"
  let ?p = "k -j"
  let ?n = "j"
  have "(\<Sum>i=?m..(?n + ?p). (f i)) = (\<Sum>i=0..?n. (f i)) + (\<Sum>i=(?n+1)..(?n + ?p). (f i))" 
    by (smt Suc_eq_plus1 Suc_le_mono add_diff_inverse_nat
        assms atLeastLessThanSuc_atLeastAtMost
        less_imp_le_nat linorder_not_le
        local.sum.atLeastLessThan_concat zero_le) 
  then show ?thesis 
    by (simp add: assms less_imp_le_nat)
qed

(*If f evaluates to 0 for n > j, then summing up to n is the same as summing up to j*)
lemma(in semiring_0) sum_simplify:
  assumes "k > (j::nat)"
  assumes " \<And>n::nat. n > j \<Longrightarrow> f n = 0"
  shows "(\<Sum>i=0..k. (f i)) = (\<Sum>i=0..j. (f i))"
proof-
  have P0:"(\<Sum>i=0..k. (f i)) = (\<Sum>i=0..j. (f i)) + (\<Sum>i=(j+1)..(k). (f i))"
    using sum_decomp assms(1) by auto
  have P1: "k > j \<and>(\<Sum>i=(j+1)..(k). (f i) ) = 0" 
    using assms(1) assms(2) by auto 
  then show ?thesis 
    by (simp add: P0)
qed

definition one_minus_X::"('a::comm_ring_1) fps" where
"one_minus_X = fps_of_poly [:1, -1:]"

lemma one_minus_X_alt_def:
"one_minus_X = Abs_fps (\<lambda> k. (if k = 0 then (1::('a::comm_ring_1)) else (if k = 1 then (-1::'a) else (0::'a))))"
proof-
  have 0: "fps_nth one_minus_X (0::nat) = (1::('a::comm_ring_1))"
    using fps_of_poly_nth by (simp add: one_minus_X_def)
  have 1: "fps_nth one_minus_X (1::nat) = (-1::('a::comm_ring_1))"
    using fps_of_poly_nth by (simp add: one_minus_X_def)
  have "fps_nth (one_minus_X) =  (\<lambda> k. (if k = 0 then (1::'a) else (if k = 1 then (-1::'a) else (0::'a))))"
  proof
    fix k
    show "fps_nth (one_minus_X) k = (if k = 0 then (1::'a) else (if k = 1 then (-1::'a) else (0::'a)))"
      using fps_of_poly_nth one_minus_X_def by (metis (no_types, lifting)
          "0" "1" Suc_pred degree_pCons_eq_if
          diff_is_0_eq' le_degree le_zero_eq linorder_not_le
          one_neq_zero pCons_eq_0_iff) 
  qed
  then show ?thesis by (simp add: expand_fps_eq) 
qed



lemma one_minus_X_id:
"one_minus_X = (1::('a::comm_ring_1) fps)  + (-1)*fps_X"
proof-
  let ?F = "fps_nth one_minus_X"
  let ?G = "fps_nth (1  + (-1)*fps_X)"
  have "?F = ?G"
  proof
    fix k
    have 0:"?G 0 = (1::('a::comm_ring_1))" 
      by simp 
    have 1: "?G 1 = (-1::('a::comm_ring_1))" 
      by simp 
    then have A: "?G k = (if k=0 then (1::('a::comm_ring_1)) else 
                      (if (k = 1) then (-1::'a) else 
                      (0::'a)))"
      by simp
    then show "?F k = ?G k" 
      by (simp add: one_minus_X_alt_def) 
  qed
  then show ?thesis 
    by (smt fps_eq_iff fps_nth_Abs_fps) 
qed

lemma one_minus_X_id0:
"one_minus_X = (1::('a::comm_ring_1) fps) - fps_X"
  using one_minus_X_id by simp 

lemma X_times_natgeom:
"fps_X*(natgs 0) = Abs_fps (\<lambda> k. (if (k = 0) then 0 else 1))"
proof-
  let ?F = "fps_nth fps_X"
  let ?G = "fps_nth (natgs 0)"
  have "fps_nth (fps_X*(natgs 0))= (\<lambda> k. (if (k = 0) then 0 else 1))"
  proof
    fix n
    have "fps_nth (fps_X*(natgs 0)) n  = (\<Sum>i=0..n. ?F i * ?G (n - i))"
      using fps_mult_nth by blast 
    then show "fps_nth (fps_X*(natgs 0)) n = (if (n = 0) then 0 else 1)"
      by (simp add: nat_geom_series_def) 
  qed
  then show ?thesis 
    by (metis fps_eq_iff fps_nth_Abs_fps)
qed

lemma X_times_geom: 
"fps_X*((gs 0)::('a::comm_semiring_1) fps) = Abs_fps (\<lambda> k. (if (k = 0) then (0::'a) else (1::'a)))"
proof-
  have "of_nat_fps (fps_X*(natgs 0)) =(of_nat_fps fps_X)* (of_nat_fps (natgs 0))"
    by (simp add: of_nat_fps_mult) 
  then have "(of_nat_fps fps_X)* (of_nat_fps (natgs 0)) 
            = of_nat_fps (Abs_fps (\<lambda> k. (if (k = 0) then 0 else 1)))"
    using  X_times_natgeom by smt 
  then have P:"(of_nat_fps fps_X)* (of_nat_fps (natgs 0)) 
            = (Abs_fps  (\<lambda> k. of_nat (if (k = 0) then 0 else 1)))"
    by (simp add: of_nat_fps_def) 
  then have "(Abs_fps  (\<lambda> k. of_nat (if (k = 0) then 0 else 1)))
            = (Abs_fps  (\<lambda> k. (if (k = 0) then (0::'a) else (1::'a))))"
  proof -
    have "(\<forall>n. ((1::'a) = of_nat (if (n::nat) = 0 then 0 else 1) \<or> 0 = n) 
               \<and> ((0::'a) = of_nat (if n = 0 then 0 else 1) \<or> 0 \<noteq> n))
               \<or> Abs_fps (\<lambda>n. of_nat (if n = 0 then 0 else 1)) 
                  = Abs_fps (\<lambda>n. if n = 0 then 0::'a else 1)"
      by simp
    then show ?thesis
      by metis
  qed
  then have Q:"(of_nat_fps fps_X)* (of_nat_fps (natgs 0)) = (Abs_fps  (\<lambda> k. (if (k = 0) then (0::'a) else (1::'a))))"
    by (simp add: P) 
  then have R: "(of_nat_fps fps_X)* (of_nat_fps (natgs 0)) = fps_X * (gs 0)" 
    by (simp add: geom_series_alt_def0 of_nat_X) 
  then show ?thesis using Q 
    by metis 
qed

lemma geom_series_inv0: "((gs 0)::('a::comm_ring_1) fps) *(one_minus_X) = 1"
proof-
  let ?G = "((gs 0)::'a fps)"
  have "?G*(one_minus_X) = ?G* ((1::('a::comm_ring_1) fps) - fps_X)"
    by (simp add: one_minus_X_id0)
  then have "?G*(one_minus_X) = ?G + (?G )*( - fps_X)" 
    by (metis mult.commute semiring_normalization_rules(3) uminus_add_conv_diff) 
  then have P: "?G*(one_minus_X) = ?G - (fps_X * ?G)" 
    by simp 
  let ?f = "fps_nth (?G - (fps_X * ?G))"
  have "?f = (\<lambda> k. (if k = 0 then 1 else 0))"
  proof
    fix k
    have "?f k = ((fps_nth ?G) k) - (fps_nth (fps_X * ?G) k)"
      using fps_sub_nth by blast 
    then show "?f k = (if k = 0 then 1 else 0)" 
    proof(cases "k = 0")
      case True
      then show ?thesis
        using X_times_geom  by (simp add: geom_series_alt_def1) 
    next
      case False 
      then show ?thesis
        using X_times_geom  by (simp add: geom_series_alt_def1)
    qed
  qed
  then have "fps_nth (?G*(one_minus_X)) = (\<lambda> k. (if k = 0 then 1 else 0))"
    using P by simp
  then have "fps_nth (?G*(one_minus_X)) = fps_nth 1" 
    by auto 
  then show ?thesis 
    by  (simp add: fps_nth_inject) 
qed

lemma one_minus_X_rep: "one_minus_X = 1 - fps_X"
  using one_minus_X_def by (metis (no_types, lifting) 
      diff_0 diff_0_right diff_pCons fps_of_poly_1'
      fps_of_poly_diff fps_of_poly_fps_X minus_pCons) 

lemma geom_series_invn:
"((geom_series n)::('a::comm_ring_1) fps)*(one_minus_X)^(n+1) = pochhammer 1 n"
proof(induction n)
  case 0
  then show ?case 
    by (simp add: geom_series_inv0) 
next
  case (Suc n)
  fix n
  assume IH: "((gs n)::'a fps) * one_minus_X ^ (n + 1) = pochhammer 1 n"
  show "(gs (Suc n)) * one_minus_X ^ ((Suc n) + 1) = ((pochhammer 1 (Suc n))::'a fps)"
  proof-
    have "fps_deriv (((gs n)::'a fps) * one_minus_X ^ (n + 1)) = (fps_deriv (gs n)) * one_minus_X ^ (n + 1) 
                                          + (gs n) * fps_deriv (one_minus_X ^ (n + 1))"
      by auto 
    then have A: "fps_deriv (((gs n)::'a fps) * one_minus_X ^ (n + 1)) = (gs (Suc n)) * one_minus_X ^ (n + 1) 
                                          + (gs n) *(of_nat (n+1))*(one_minus_X ^n)*(fps_deriv one_minus_X)"
      by (smt ab_semigroup_mult_class.mult_ac(1) add_diff_cancel_right' fps_deriv_power fps_nth_deriv_commute fps_of_nat geom_series_def mult.commute)
    have D: "fps_deriv (pochhammer 1 n) = 0"
      by (metis fps_deriv_of_nat of_nat_1 pochhammer_of_nat) 
    then have "fps_deriv (((gs n)::'a fps)  * one_minus_X ^ (n + 1) ) = 0" 
      using IH by simp 
    then have B: "(gs (Suc n)) * one_minus_X ^ (n + 1) 
                    + ((gs n)::'a fps) *(of_nat (n+1))*(one_minus_X ^n)*(fps_deriv one_minus_X) = 0" 
      using A by simp  
    have Z: "fps_deriv(one_minus_X) = -1" 
      by (simp add: one_minus_X_rep) 
    then have  "(gs (Suc n)) * one_minus_X ^ (n + 1) 
                   + ((gs n)::'a fps) *(of_nat (n+1))*(one_minus_X ^n)*(-1) = 0" 
      using B by(simp add: Z)
    then have "(gs (Suc n)) * one_minus_X ^ (n + 1) 
                   = ((gs n)::'a fps) *(of_nat (n+1))*(one_minus_X ^n)"
      by auto
    then have C: "(gs (Suc n)) * one_minus_X ^ (n + 1) * one_minus_X
                   = ((gs n)::'a fps) *(of_nat (n+1))*(one_minus_X ^n)*one_minus_X"
      by simp  
    have D: "one_minus_X ^ (n + 1) * one_minus_X = one_minus_X ^ (n + 2)"
      by simp 
    have E: "(one_minus_X ^n) *(one_minus_X ) = (one_minus_X ^(n+1))"
      by simp
    then have "(gs (Suc n)) * one_minus_X ^ (n + 2) 
                   = ((gs n)::'a fps) *(of_nat (n+1))*(one_minus_X ^(n+1))"
      using D C by (simp add: E ab_semigroup_mult_class.mult_ac(1)) 
    then have "(gs (Suc n)) * one_minus_X ^ (n + 2)  = (of_nat (n+1))*(((gs n)::'a fps) *(one_minus_X ^(n+1)))"
      by auto 
    then have "(gs (Suc n)) * one_minus_X ^ (n + 2)  = (of_nat (n+1))* ((pochhammer 1 n)::'a fps)"
      using IH by simp
    then show "(gs (Suc n)) * one_minus_X ^ ((Suc n) + 1)  = ((pochhammer 1 (Suc n))::'a fps)"
      by (simp add: pochhammer_rec') 
  qed
qed

lemma coeff_fact_nat:
  fixes n::nat
  shows "((n+k) choose k)*(pochhammer 1 n)  = pochhammer (k+1) n"
  using  binomial_fact_lemma  pochhammer_fact pochhammer_product'
  by (metis (no_types, lifting) add.commute add_diff_cancel_left'
      diff_le_self fact_nonzero id_apply mult.assoc
      mult.commute mult_cancel_left of_nat_eq_id)


lemma L1:
  fixes n::nat
  shows "pochhammer (1:: ('a::comm_ring_1)) n = of_nat (pochhammer 1 n)"
  by (metis of_nat_1 pochhammer_of_nat) 

lemma L2:
  fixes n::nat
  fixes k::nat
  shows "pochhammer (of_nat k:: ('a::comm_ring_1)) n = of_nat (pochhammer k n)"
  by (simp add: pochhammer_of_nat) 

lemma coeff_fact:
  fixes n::nat
  assumes "n>0"
  shows "(of_nat ((n+k) choose k))*(pochhammer (1:: ('a::comm_ring_1)) n)  = gcf n k"
proof-
  have "(of_nat ((n+k) choose k))*(pochhammer (1:: ('a::comm_ring_1)) n)  = pochhammer (of_nat (k+1)) n"
    using L1 L2 coeff_fact_nat by (metis of_nat_mult) 
  then show ?thesis by (metis assms gcf.elims neq0_conv) 
qed


(*This definition is off by one. Change the name of it!*)
definition normalized_gs::"nat \<Rightarrow> (('a::comm_ring_1) fps)" where
"normalized_gs n = Abs_fps (\<lambda>k. of_nat ((n+k) choose k))"

lemma gs_normalized_gs:
"(normalized_gs n)*(pochhammer (1:: ('a::comm_ring_1) fps ) n) = gs n"
proof-
  let ?f = "fps_nth ((normalized_gs n)*(pochhammer (1:: ('a::comm_ring_1) fps ) n))"
  let ?g = "fps_nth (gs n)"
  have "?f = ?g"
  proof
    fix k
    have "?f k = (of_nat ((n+k) choose k))*(pochhammer (1::'a) n)" 
      by (metis (no_types, lifting) L2 fps_mult_left_const_nth
        fps_nth_Abs_fps fps_of_nat mult.commute 
        normalized_gs_def of_nat_1) 
    then show "?f k = ?g k"
      using geom_series_alt_def1 coeff_fact 
      by (metis add_cancel_right_left binomial_n_n
          fps_nth_Abs_fps gcf.elims mult.right_neutral
          neq0_conv of_nat_1 pochhammer_0)
qed
  then show ?thesis 
    by (simp add: expand_fps_eq) 
qed

lemma normalized_gs_inv:
  "((normalized_gs n)::('a::{idom, ring_char_0}) fps )*(one_minus_X)^(n+1) =1"
proof-
  have "(normalized_gs n)*(pochhammer (1::'a fps) n)*(one_minus_X)^(n+1) = ( gs n )*(one_minus_X)^(n+1)"
    by (simp add: gs_normalized_gs) 
  then have "(normalized_gs n)*(pochhammer (1::'a fps) n)*(one_minus_X)^(n+1) = (pochhammer (1::'a fps) n)"
    using geom_series_invn by metis 
  then have P: "(normalized_gs n)*(one_minus_X)^(n+1)*(pochhammer (1::'a fps) n) =1* (pochhammer (1::'a fps) n)"
    by auto
  have "(pochhammer (1::'a fps) n) \<noteq>0" 
  proof(induction n)
    case 0 
    then show ?case by simp
  next
    case (Suc n)
    fix n
    assume IH: "pochhammer (1::'a fps) n \<noteq> 0"
    then have A: "pochhammer (1::'a fps) (Suc n) =( (of_nat (Suc n))::'a fps)*(pochhammer (1::'a fps) n)" 
      by (simp add: pochhammer_rec') 
    have "((of_nat (Suc n))::'a fps) \<noteq>0"
    proof-
      have A1: " ((of_nat (Suc n))::'a)\<noteq>0"
        using of_nat_neq_0 by blast
      have A2: " ((of_nat (Suc n))::'a fps) 
        = Abs_fps (\<lambda> k. if k=0 then ((of_nat (Suc n))::'a) else (0::'a))" 
        by (metis fps_of_nat fps_const_def) 
      then have A3: "fps_nth ((of_nat (Suc n))::'a fps) 0 \<noteq> fps_nth 0 0"
        using A1 by simp 
      then show ?thesis  by metis 
    qed
    then show "pochhammer (1::'a fps) (Suc n) \<noteq>0" 
      using IH divisors_zero by (simp add: A)
  qed
  then show ?thesis 
    using P mult_cancel_right by blast 
qed


(* Maps the polynomial p to the series \<Sum>p(n)*)

definition gen_series:: "('a::comm_ring_1) poly \<Rightarrow> 'a fps" where
"gen_series  p = Abs_fps (\<lambda>m. ((poly p) (of_nat m)))"

lemma gen_series_add:
"gen_series (p+q)  = (gen_series p) + (gen_series q)"
proof-
  let ?f = "fps_nth (gen_series (p+q))"
  let ?g = "fps_nth ((gen_series p) + (gen_series q))"
  have "?f = ?g"
  proof
    fix k
    show "?f k = ?g k"
      by (simp add: gen_series_def) 
  qed
  then show ?thesis
    using fps_nth_inject by blast
qed

(* Maps a polynomial to a rational expression which will
be proved to be equal to gen_series:*)

definition rat_gen_term:: "nat \<Rightarrow> ('a::{idom, ring_char_0} poly) \<Rightarrow> 'a fps" where
"rat_gen_term n p = (fps_const (poly (\<Delta>[n] p) 0))*(fps_X)^n * (normalized_gs n)"

lemma pochhammer_monom_rat_gen_term:
  assumes A: "a \<noteq>0"
  assumes B: "p = pochhammer_monom (a::('a::{ring_char_0,idom})) d"
  shows "rat_gen_term n p =( if (n = d) then (rat_gen_term n p ) else 0)"
proof(cases "n = d")
  case True
  then show ?thesis
    by simp 
next
  case False 
  then show ?thesis
  proof(cases "n <d")
    case True
    then have P0: "poly (PM (a::'a) (d  - n)) 0 = 0"
      using pochhammer_zero_root 
      by (metis Suc_diff_Suc) 
    have"(\<Delta>[n] p )
                = (pochhammer (of_nat ((d-1) + 2 - n)) n)*(PM (a::'a) (d - n))"
      using B diff_pow_pochhammer_monom 
      by (metis A One_nat_def Suc_diff_Suc 
          Suc_eq_plus1 True diff_zero neq0_conv not_less0)  
    then show ?thesis
      using P0 by (metis fps_const_0_eq_0
          mult_not_zero poly_mult rat_gen_term_def) 
  next
    case F: False
    then have "d < n"
      using F False using nat_neq_iff by blast 
    then have "(fps_const (poly (\<Delta>[n] p) 0)) = 0"
      by (simp add: diff_pow_greater_deg A B) 
    then show ?thesis 
      by (metis mult_zero_left rat_gen_term_def) 
  qed
qed


 definition rat_gen_series:: "('a::{idom, ring_char_0} poly) \<Rightarrow> 'a fps" where
"rat_gen_series p = (\<Sum>i= 0..(degree p). rat_gen_term i p)"

lemma rat_gen_term_fact:
  assumes "n> degree p"
  shows "rat_gen_term n p = 0"
  using diff_pow_zero 
  by (simp add: diff_pow_zero assms rat_gen_term_def) 

lemma rat_gen_term_add:
"rat_gen_term n (p + q) = (rat_gen_term n p) + (rat_gen_term n q)"
proof-
  have "(fps_const (poly (\<Delta>[n] (p+q)) 0)) = (fps_const ((poly (\<Delta>[n] p)) 0))
                                          + (fps_const ((poly (\<Delta>[n] q)) 0))"
    by (simp add: diff_pow_additive) 
  then have "rat_gen_term n (p + q) = ((fps_const ((poly (\<Delta>[n] p)) 0))
                                      + (fps_const ((poly (\<Delta>[n] q)) 0)))
                                        *(fps_X)^n * (normalized_gs n)"
    by (simp add: rat_gen_term_def) 
  then have "rat_gen_term n (p + q) = (fps_const ((poly (\<Delta>[n] p)) 0))*(fps_X)^n * (normalized_gs n)
                                      + (fps_const ((poly (\<Delta>[n] q)) 0)) *(fps_X)^n * (normalized_gs n)"
    by (metis comm_semiring_class.distrib) 
  then show ?thesis 
    by (simp add: rat_gen_term_def) 
qed

lemma fact:
"n \<ge> degree p \<Longrightarrow> (\<Sum>i= 0..n. (rat_gen_term i p) ) = rat_gen_series p"
proof(cases "n = degree p")
  case True
  then show ?thesis 
    by (simp add: rat_gen_series_def) 
next
  case False
  assume "n \<ge> degree p"
  then have "n > degree p" 
    using False by linarith
  then have "(\<Sum>i= 0..n. (rat_gen_term i p)) =(\<Sum>i= 0..(degree p). rat_gen_term i p)"
     by (simp add: rat_gen_term_fact sum_simplify) 
  then show ?thesis
    by (simp add: rat_gen_series_def)
qed

lemma rat_gen_series_add:
"rat_gen_series (p+(q::('a::{idom, ring_char_0} poly))) = rat_gen_series p + rat_gen_series q"
proof-
  have "rat_gen_series ((p::'a poly)+q) = (\<Sum>i= 0..(degree (p+q)). (rat_gen_term i (p + q)) )" 
    by(simp add:rat_gen_series_def)
  then have "rat_gen_series ((p::'a poly)+q) = (\<Sum>i= 0..(degree (p+q)). (rat_gen_term i p) + (rat_gen_term i q) )" 
    by(simp add: rat_gen_term_add)
  then have "rat_gen_series ((p::'a poly)+q) = (\<Sum>i= 0..(degree (p+q)). (rat_gen_term i p)) 
                                             + (\<Sum>i= 0..(degree (p+q)). (rat_gen_term i q))"
    using sum.distrib by force 
  then have "rat_gen_series ((p::'a poly)+q) = (\<Sum>i= 0..(degree p). (rat_gen_term i p)) 
                                             + (\<Sum>i= 0..(degree q). (rat_gen_term i q))"
  proof-
    let ?n = "max (degree p) (degree q)"
    have "?n \<ge> degree (p+q)" 
      by (simp add: degree_add_le_max) 
    then have P0: "(\<Sum>i= 0..(degree (p+q)). (rat_gen_term i (p + q)) ) = (\<Sum>i= 0..?n. (rat_gen_term i (p + q)) )"
      by (metis fact rat_gen_series_def) 
    have "?n \<ge>degree p" by auto 
    then have P1: "(\<Sum>i= 0..(degree p). (rat_gen_term i p)) = (\<Sum>i= 0..?n. (rat_gen_term i p)) "
      by (metis fact rat_gen_series_def) 
    have "?n \<ge>degree q" by auto
    then have P2: "(\<Sum>i= 0..(degree q). (rat_gen_term i q)) = (\<Sum>i= 0..?n. (rat_gen_term i q)) "
      by (metis fact rat_gen_series_def) 
    have "(\<Sum>i= 0..?n. (rat_gen_term i (p + q)) ) = (\<Sum>i= 0..?n. (rat_gen_term i p)) + (\<Sum>i= 0..?n. (rat_gen_term i q))"
      using sum.distrib  by (metis (no_types, lifting) rat_gen_term_add sum.cong)
    then show ?thesis 
      using P0 P1 P2 by (simp add: rat_gen_series_def) 
  qed
  then show ?thesis 
    by (simp add: rat_gen_series_def) 
qed
    
(*When p is a pochhammer monomial, then every term of (rat_gen_series p) is 0, hence: *)

lemma rat_gen_series_const:
  assumes A: "degree p = 0"
  shows "rat_gen_series p = gen_series p"
proof-
  let ?f = "fps_nth (rat_gen_series p)"
  let ?g = "fps_nth (gen_series p)"
  have "?f = ?g"
  proof
    fix k
    have "rat_gen_series p =  rat_gen_term 0 p"
      using A by(simp add: rat_gen_series_def)
    then have "rat_gen_series p  = (fps_const (poly (\<Delta>[0] p) 0)) * (normalized_gs 0)"
      by (simp add: rat_gen_term_def) 
    then have "rat_gen_series p  = (fps_const (poly (p) 0)) * (normalized_gs 0)"
      by simp 
    then have "?f k = (poly p 0)" 
      by (simp add: normalized_gs_def) 
    then have "?f k = (poly p (of_nat k))" 
      using A by (metis degree_eq_zeroE 
          mult_zero_right poly_0 poly_pCons) 
    then show "?f k = ?g k" 
      by (simp add: gen_series_def) 
  qed
  then show ?thesis 
    using fps_nth_inject by blast 
qed

lemma pochhammer_monom_rat_gen_series0:
  assumes A: "a \<noteq>0"
  assumes B: "p = pochhammer_monom (a::('a::{ring_char_0,idom})) d"
  assumes C: "d \<noteq>0"
  shows "rat_gen_series p = (rat_gen_term d p)"
proof-
  have Deg: "d = degree p" 
    by (simp add: A B pochhammer_monom_degree) 
  have P0: "\<And> i.( i \<le> (d -1) \<Longrightarrow> (rat_gen_term i p) = 0)"
  proof-
    fix i::nat
    assume D: "i \<le> (d -1) "
    then have Ne: "i \<noteq>d" 
      using C by linarith 
    have "(rat_gen_term i (p::'a poly)) = ( if (i = d) then (rat_gen_term i p ) else 0)"
      using A B D pochhammer_monom_rat_gen_term by blast 
    then show "(rat_gen_term i (p::'a poly)) = 0" 
      using Ne by auto 
  qed
  then have P1:"(\<Sum>i= 0..((degree p) - 1). rat_gen_term i p) = 0" 
    using Deg by auto 
  have "rat_gen_series p = (\<Sum>i= 0..(d - 1). rat_gen_term i p) + (rat_gen_term d p)"
    by (metis (mono_tags, lifting) C Deg One_nat_def
        Suc_diff_Suc diff_zero neq0_conv
        rat_gen_series_def sum.atLeast0_atMost_Suc) 
  then show ?thesis using P1 
    by (simp add: Deg) 
qed

lemma pochammer_gen_series: 
  assumes "(a::('a::{idom, ring_char_0})) \<noteq>0"
  assumes "d \<noteq>0"
  shows "gen_series (PM a d) =  (fps_const (a*(pochhammer (of_nat 1) d)))*(fps_X)^d * (normalized_gs d)"
proof-
  let ?f = "fps_nth ((fps_X)^d * (normalized_gs d))"
  have P0:"?f = (\<lambda>k. if (k < d) then 0 else ( of_nat (k choose (k-d))))"
  proof
    fix k
    show "?f k = (if (k < d) then 0 else ( of_nat (k choose (k - d))))"
    proof(cases "k<d")
      case True
      then show ?thesis 
        by (simp add: fps_X_power_mult_nth) 
    next
      case False
      then show ?thesis 
      by (simp add: fps_X_power_mult_nth normalized_gs_def) 
    qed
  qed
  let ?g = "fps_nth (gen_series (PM a d))" 
  have P1:"?g = (\<lambda> k. (poly (PM a d) (of_nat k)))"
    using gen_series_def by (metis fps_nth_Abs_fps) 
  have P2: "?g = (\<lambda>k. if (k < d) then 0 else ((a*(pochhammer (of_nat 1) d))*( of_nat (k choose (k-d)))))"
  proof
    fix k
    show "?g k = ( if (k < d) then 0 else ((a*(pochhammer (of_nat 1) d))*( of_nat (k choose (k-d)))))"
    proof(cases "k<d")
      case True
      then show ?thesis 
         by (simp add: pochhammer_roots P1) 
     next
       case False
       have "?g k = (poly (PM a d) (of_nat k))"
          by (simp add: P1)   
       then have "?g k =  a * (of_nat (k choose d))*(pochhammer 1 d)" 
         using False pochhammer_eval_nat assms(1) by fastforce 
       then show ?thesis 
         by (metis False binomial_symmetric
             mult.assoc mult.commute not_le of_nat_1) 
     qed
  qed
  let ?h = "fps_nth ((fps_const (a*(pochhammer (of_nat 1) d)))*(fps_X)^d * (normalized_gs d))"
  have "?h = ?g"
  proof
    fix k
    show "?h k = ?g k"
    proof-  
      have "?h k = a*(pochhammer (of_nat 1) d)*(?f k)" 
        by (simp add: mult.assoc) 
      then show ?thesis 
        by (simp add: P0 P2) 
    qed
  qed
  then show ?thesis 
    by (simp add: fps_nth_inject) 
qed

lemma pochhammer_monom_rat_gen_series:
  assumes A: "a \<noteq>0"
  assumes B: "p = pochhammer_monom (a::('a::{ring_char_0,idom})) d"
  assumes C: "d \<noteq>0"
  shows "rat_gen_series p = gen_series p"
proof-
  have "rat_gen_series p = (rat_gen_term d p)"
    using A B C pochhammer_monom_rat_gen_series0 by blast 
  then have P0: "rat_gen_series p = (fps_const (poly (\<Delta>[d] p) 0))*(fps_X)^d * (normalized_gs d)"
    by (simp add: rat_gen_term_def) 
  have "(\<Delta>[d] p) = (pochhammer (of_nat (1)) d)*(PM a 0)"
    using B diff_pow_pochhammer_monom1 by blast  
  then   have "(\<Delta>[d] p) = (pochhammer (of_nat (1)) d)*[:a:]"
    by (simp add: pochhammer_monom_alt_def) 
  then have  "rat_gen_series p = 
       (fps_const ((poly ((pochhammer (of_nat (1)) d)) 0)*a))*(fps_X)^d * (normalized_gs d)"
    by (simp add: P0) 
  then have "rat_gen_series p =  
      (fps_const (a*(pochhammer (of_nat (1)) d)))*(fps_X)^d * (normalized_gs d)"
    by (metis L2 add.right_neutral mult.commute
        mult_not_zero of_nat_poly poly_pCons) 
  then show ?thesis
    using pochammer_gen_series by (simp add: pochammer_gen_series A B C) 
qed

(*This is a technical preliminary lemma because I didn't know how else to
do a proof by strong induction in Isabelle...*)
lemma poly_gen_series_is_rat0:
  fixes n::nat
  shows "degree p \<le>n \<Longrightarrow> rat_gen_series (p::('a::{idom, ring_char_0} poly)) = gen_series p"
proof-
  show "(degree (p::'a poly) \<le> n) \<Longrightarrow> rat_gen_series p= gen_series p"
  proof(induct n arbitrary:p)
    case 0
    then show ?case 
      using rat_gen_series_const by blast 
  next
    case (Suc n)
    fix n
    fix p::"'a poly"
    assume IH: "\<And>(p::'a poly). degree p \<le> n \<Longrightarrow> rat_gen_series p = gen_series p"
    assume P: "degree p \<le> Suc n"
    show "rat_gen_series p = gen_series p"
    proof(cases "degree p = 0")
      case True
      then show ?thesis 
        using rat_gen_series_const by blast
    next
      case False
      obtain q where "p = q + (pochhammer_lt p)" and "degree q < degree p"
        using pochhammer_leading_term_decomp using False by blast 
      have P0: "(rat_gen_series q) = (gen_series q)"
      proof-
        have "degree q \<le> n \<Longrightarrow> rat_gen_series q = gen_series q"
          using IH by simp 
        then show ?thesis  using P \<open>degree q < degree p\<close> by linarith 
      qed
      let ?l = "(pochhammer_lt p)"
      have P1:"(rat_gen_series ?l) = (gen_series ?l)"
        using pochhammer_monom_rat_gen_series pochhammer_lt_def 
        by (metis False degree_0 leading_coeff_0_iff) 
      have L_Decomp: "rat_gen_series p = (rat_gen_series q) + (rat_gen_series ?l)"
        using rat_gen_series_add  by (metis \<open>p = q + pochhammer_lt p\<close>) 
      have R_Decomp: "gen_series p = (gen_series q) + (gen_series ?l)"
        using gen_series_add  by (metis \<open>p = q + pochhammer_lt p\<close>) 
      then show ?thesis 
        using L_Decomp R_Decomp P0 P1 by auto
    qed
  qed
qed

(*The actual lemma - rationality of polynomial generating series over a char 0 integral domain*)

lemma poly_gen_series_is_rat:
"rat_gen_series (p::('a::{idom, ring_char_0} poly)) = gen_series p"
proof-
  let ?n = "degree p"
  have "degree p \<le>?n"
    by auto
  then show ?thesis 
    using poly_gen_series_is_rat0 by auto
qed

end