theory p_adic_fields
  imports 
Main
 "HOL-Computational_Algebra.Primes"
 "HOL-Algebra.QuotRing"
"~~/src/HOL/Algebra/Valued_Fields/Ordered_Abelian_Group"
                "~~/src/HOL/Algebra/Ring"
                "~~/src/HOL/Algebra/Subrings"
                "~~/src/HOL/Algebra/Ideal"
          "~~/src/HOL/Algebra/IntRing"
          "~~/src/HOL/Algebra/RingHom"
          "~~/src/HOL/HOL-Computational_Algebra.Primes"
          "~~/src/HOL/Number_Theory/Residues"
begin

lemma (in ideal) prin_ideal_in_ideal:
  assumes "a \<in> I"
  shows "Idl {a} \<subseteq>I"
  by (simp add: assms genideal_minimal is_ideal) 


(*A characterization of the set "ZMod n m"*)

lemma Zmod_set:
 "(ZMod n m) = {(x::int). (x mod n) = (m mod n)}"
proof
  show "(ZMod n m) \<subseteq> {x::int. x mod n = m mod n}"
  proof
    fix t::int
    assume A: "t \<in> (ZMod n m)"
    obtain y where "y*n + m = t"
      using rcos_zfact A by blast 
    then have "t mod n = m mod n"
      by auto
    then show "t \<in>{x::int. x mod n = m mod n}"
      by auto
  qed
  show "{x. x mod n = m mod n} \<subseteq> ZMod n m "
  proof
    fix t::int
    assume B: "t \<in>{x. x mod n = m mod n}"
    then show "t \<in> ZMod n m" 
      by (metis (mono_tags, lifting) ZMod_eq_mod ZMod_defs(1)
          abelian_subgroup.a_repr_independenceD 
          abelian_subgroupI3 ideal_def int.genideal_ideal 
          int_Zcarr mem_Collect_eq ringE(1) top.extremum) 

  qed
qed



(*restriction maps from Z/mZ for arbitrary m to Z/nZ. Will only be a morphism of rings when n|m.*)

definition res:: "nat \<Rightarrow> int set \<Rightarrow> int set" where
"res n  = (\<lambda> s. ZMod n (rep s))"

(* When n = m, res is the identity map *)

lemma res_id:
  assumes "x \<in> carrier (ZFact (n::int))"
  assumes "n \<noteq>0"
  shows "res n x = x"
  using assms(1) assms(2) by auto

(*res actually maps ZFact n to ZFact m*)

lemma res_range:
"res n s \<in> carrier (ZFact n)"
proof-
  fix n::nat
  fix s::"int set"
  show "res n s \<in> carrier (ZFact n)" using ZFact_def
    by (simp add: int_Idl ZFact_defs(2)
        ZMod_defs(1) int.a_rcosetsI res_def) 
qed


(*Ideal formulation of universal property of kernels of ring homomorphims*)

lemma (in ring) quot_ring_factor:
  assumes "ideal I R"
  assumes "ideal J R"
  assumes "I \<subseteq> J"
  obtains h where "h \<in> ring_hom (R Quot I) (R Quot J)" and "\<And> x. x \<in> carrier R \<Longrightarrow> h (I +> x) = J +> x"
proof-
  have A0: "\<And> y z. \<lbrakk> (y \<in>carrier R); (z \<in>carrier R); (I +> y) = (I +> z)\<rbrakk> \<Longrightarrow>  (J +> y) = (J +> z)"
  proof-
    fix y z
    assume "y \<in>carrier R"
    assume "z \<in>carrier R"
    assume A: "(I +> y) = (I +> z)"
    then show "(J +> y) = (J +> z)"
    proof-
      have "z \<in> (I +> y)" using A a_r_coset_def' 
        using \<open>z \<in> carrier R\<close> abelian_subgroup.a_repr_independenceD
          abelian_subgroupI3 assms(1) ideal.axioms(1) is_abelian_group by fastforce 
      then obtain x where "x \<in>I" and "y  \<oplus>\<^bsub>R\<^esub> x = z" using A  assms(1) a_r_coset_def'[of R I y] 
        by (metis \<open>y \<in> carrier R\<close> \<open>z \<in> carrier R\<close> abelian_subgroup.a_rcos_module_imp
            abelian_subgroupI3 add.m_lcomm add.r_inv_ex ideal.axioms(1)
            is_abelian_group minus_equality r_neg1 r_zero) 
      then have "x \<in>J \<and> y  \<oplus>\<^bsub>R\<^esub> x = z" using assms by auto
      then show ?thesis
        by (smt \<open>y \<in> carrier R\<close> a_coset_add_assoc a_r_coset_def
            add.coset_join2 add.m_comm additive_subgroup.a_subgroup
            additive_subgroup.a_subset assms(2) ideal.Icarr ideal.axioms(1)) 
    qed
  qed
  let ?h = "\<lambda> (x:: 'a set). (\<Union> y \<in> x. J +> y)"
  have A1: "\<And> x. x \<in> carrier R \<Longrightarrow> ?h (I +> x) = J +> x"
  proof-
    fix x
    assume "x \<in> carrier R"
    show "?h (I +> x) = J +> x"
    proof
      show " J +> x \<subseteq> (\<Union>y\<in>I +> x. J +> y) " 
        by (metis UN_upper \<open>x \<in> carrier R\<close> a_coset_add_zero 
        a_coset_join1 a_rcosI add.subgroupE(1) additive_subgroup.a_subgroup 
        assms(1) ideal.axioms(1) l_zero zero_closed) 
      show "(\<Union>y\<in>I +> x. J +> y) \<subseteq> J +> x"
      proof
      fix xa
      assume B0: "xa \<in> (\<Union>y\<in>I +> x. J +> y)"
      show " xa \<in> J +> x "
      proof-
        obtain y where "y \<in>I +> x" and "xa \<in> J +>y" 
          using B0 by blast 
        then have "I +>y = I +> x" 
          using \<open>x \<in> carrier R\<close> a_repr_independence additive_subgroup.a_subgroup assms(1) ideal.axioms(1) by blast 
        have "y \<in> carrier R" 
          by (meson \<open>x \<in> carrier R\<close> \<open>y \<in> I +> x\<close> a_r_coset_subset_G
          additive_subgroup.a_subset assms(1) ideal_def subset_iff) 
        then have "J +>y = J +> x" 
          by (simp add: \<open>y \<in> carrier R\<close> A0 \<open>I +> y = I +> x\<close> \<open>x \<in> carrier R\<close>) 
        then show ?thesis 
          using  \<open>xa \<in> J +> y\<close> by blast 
      qed
    qed
    qed
  qed
  have A2: "?h \<in> ring_hom (R Quot I) (R Quot J)"
  proof- 
    let ?R = "(R Quot I)"
    let ?S = "(R Quot J)"
    have hom_closed: "\<And> x. x \<in> carrier ?R ==> ?h x \<in> carrier ?S" 
    proof-
      fix x
      assume B0: "x \<in> carrier (R Quot I)"
      then obtain z where "z \<in> carrier R" and  "x = I +> z"
        unfolding FactRing_def using A_RCOSETS_def'[of R I] by auto
      then show "?h x \<in>carrier ?S" using A1 
      by (simp add: FactRing_def a_rcosetsI 
          additive_subgroup.a_subset 
          assms(2) ideal.axioms(1))
    qed
    have compatible_mult: "\<And>x y. [| x \<in> carrier ?R; y \<in> carrier ?R |] ==> ?h (x \<otimes>\<^bsub>?R\<^esub>  y) = ?h x \<otimes>\<^bsub>?S\<^esub> ?h y"
    proof-
      fix x y
      assume Ax: "x \<in> carrier ?R" and Ay: " y \<in> carrier ?R"
      obtain a where a1: "a \<in> carrier R" and  a2: "x = I +> a"
        using Ax unfolding FactRing_def using A_RCOSETS_def'[of R I] by auto  
      obtain b where b1: "b \<in> carrier R" and  b2: "y = I +> b"
        using Ay unfolding FactRing_def using A_RCOSETS_def'[of R I] by auto  
      show "?h (x \<otimes>\<^bsub>?R\<^esub>  y) = ?h x \<otimes>\<^bsub>?S\<^esub> ?h y"
      proof-
        have "(x \<otimes>\<^bsub>?R\<^esub>  y) = I +> (a \<otimes> b)" 
          using a1 a2 b1 b2 assms(1) ideal.rcos_ring_hom 
            ring_hom_mult by fastforce
        then have "?h (x \<otimes>\<^bsub>?R\<^esub>  y) = J +> (a \<otimes> b)" 
          by (simp add: A1 a1 b1) 
        then show ?thesis 
          by (simp add: A1 a1 a2 assms(2) 
              b1 b2 ideal.rcos_ring_hom ring_hom_mult) 

 
      qed
    qed
    have compatible_add: "\<And>x y. [| x \<in> carrier ?R; y \<in> carrier ?R |] ==> ?h (x \<oplus>\<^bsub>?R\<^esub>  y) = ?h x \<oplus>\<^bsub>?S\<^esub> ?h y"
    proof-
      fix x y
      assume Ax: "x \<in> carrier ?R" and Ay: " y \<in> carrier ?R"
      obtain a where a1: "a \<in> carrier R" and  a2: "x = I +> a"
        using Ax unfolding FactRing_def using A_RCOSETS_def'[of R I] by auto  
      obtain b where b1: "b \<in> carrier R" and  b2: "y = I +> b"
        using Ay unfolding FactRing_def using A_RCOSETS_def'[of R I] by auto  
      show "?h (x \<oplus>\<^bsub>?R\<^esub>  y) = ?h x \<oplus>\<^bsub>?S\<^esub> ?h y"
      proof-
        have "(x \<oplus>\<^bsub>?R\<^esub>  y) = I +> (a \<oplus> b)" 
          using a1 a2 b1 b2 assms(1) ideal.rcos_ring_hom 
            ring_hom_add by fastforce
        then have "?h (x \<oplus>\<^bsub>?R\<^esub>  y) = J +> (a \<oplus> b)" 
          by (simp add: A1 a1 b1) 
        then show ?thesis 
          by (simp add: A1 a1 a2 assms(2) 
              b1 b2 ideal.rcos_ring_hom ring_hom_add) 
      qed
    qed
    have compatible_one: "?h \<one>\<^bsub>?R\<^esub> = \<one>\<^bsub>?S\<^esub>" 
      by (simp add: A1 FactRing_def) 
    then have "ring_hom_ring ?R ?S ?h" 
      using ring_hom_ringI  by (simp add: ring_hom_ringI
          assms(1) assms(2) compatible_add compatible_mult
          hom_closed ideal.quotient_is_ring) 
    then show ?thesis 
      using ring_hom_ring.homh by blast 
  qed
  then show ?thesis 
    using A1 A2  that by auto 
qed

(*technical lemma for showing something is a ring_hom*)

lemma (in ring_hom_ring) equals_ring_hom:
  fixes g
  assumes "\<And>x. x \<in> carrier R \<Longrightarrow> g x = h x"
  shows "g \<in> ring_hom R S"
  using ring_hom_ringI
    by (simp add: assms ring_hom_memI)   

(*When n is a factor of m, the res map is a ring homomorphism*)

lemma res_hom:
  assumes "(m::nat) mod (n::nat) = 0"
  assumes "n \<noteq>0"
  assumes "m \<noteq>0"
  shows "(res n) \<in> ring_hom (ZFact m) (ZFact n)"
proof-
  have "(Idl\<^bsub>\<Z>\<^esub> {m}) \<subseteq>(Idl\<^bsub>\<Z>\<^esub> {n})"
  proof
    fix x
    assume "x \<in> (Idl\<^bsub>\<Z>\<^esub> {m})"
    then obtain k::int where "x = k*m" 
      using int_Idl by auto 
    then have "x mod n = 0" 
      using assms(1)  by auto 
    then show "x \<in>(Idl\<^bsub>\<Z>\<^esub> {n})"
      using Idl_subset_eq_dvd int_Idl_subset_ideal by auto 
  qed
  then obtain h where h1:"h \<in> ring_hom (ZFact m) (ZFact n)" 
                  and h2:"\<And> x. x \<in> carrier \<Z> \<Longrightarrow> h ((Idl\<^bsub>\<Z>\<^esub> {m}) +>\<^bsub>\<Z>\<^esub> x) = (Idl\<^bsub>\<Z>\<^esub> {n}) +>\<^bsub>\<Z>\<^esub> x"
    by (metis UNIV(2) UNIV_I ZFact_def int.genideal_ideal int.quot_ring_factor)
  have P: "ring_hom_ring (ZFact m) (ZFact n) h" 
    using h1 ZFact_is_cring cring_def
      ring_hom_ring_axioms.intro ring_hom_ring_def by blast 
  have  "\<And> x. x \<in> carrier (ZFact m) ==> h x = res n x"
  proof-  
    fix x
    assume A: "x \<in> carrier (ZFact m)"
    then obtain a where "x = (Idl\<^bsub>\<Z>\<^esub> {m}) +>\<^bsub>\<Z>\<^esub> a" 
      using ZMod_def assms(3) rep_prop by fastforce 
    have "h x = (Idl\<^bsub>\<Z>\<^esub> {n}) +>\<^bsub>\<Z>\<^esub> a" 
      by (simp add: \<open>x = Idl\<^bsub>\<Z>\<^esub> {int m} +>\<^bsub>\<Z>\<^esub> a\<close> h2) 
    have "res n x = (Idl\<^bsub>\<Z>\<^esub> {n}) +>\<^bsub>\<Z>\<^esub> rep(x)"
      using res_def by (simp add: ZMod_def) 
    then show "h x = res n x" 
      by (metis UNIV_I ZMod_def A assms(3) h2 int_carrier_eq of_nat_eq_0_iff rep_prop) 
  qed
  then show ?thesis 
    using P ring_hom_ring.equals_ring_hom  by blast 
qed

(*A more convenient presentation of the result for prime powers*)

lemma res_hom_p:
  assumes "m < n"
  assumes "p \<noteq>0"
  shows "(res (p^m)) \<in> ring_hom (ZFact (p^n)) (ZFact (p^m))"
proof-
  have Nonzero_m: "p^m \<noteq>0" 
    by (simp add: assms(2)) 
  have Nonzero_n: "p^n \<noteq>0" 
    by (simp add: assms(2))
  have Mod: "p^n mod p^m = 0" 
    by (simp add: assms(1) le_imp_power_dvd less_imp_le) 
  then show ?thesis 
    using res_hom Nonzero_m Nonzero_n by presburger
qed

(*additivity simp for res_hom*)

lemma res_hom_add:
  assumes "(m::nat) mod (n::nat) = 0"
  assumes "n \<noteq>0"
  assumes "m \<noteq>0"
  assumes "x \<in> carrier (ZFact m)"
  assumes "y \<in> carrier (ZFact m)"
  shows "res n (x \<oplus>\<^bsub>ZFact m\<^esub> y) = (res n x) \<oplus>\<^bsub>ZFact n\<^esub> (res n y)" 
  by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5) res_hom ring_hom_add) 

(*unary negation simp for res_hom*)

lemma res_hom_uminus:
  assumes "(m::nat) mod (n::nat) = 0"
  assumes "n \<noteq>0"
  assumes "m \<noteq>0"
  assumes "x \<in>carrier (ZFact m)"
  shows " res n ( \<ominus>\<^bsub>(ZFact m)\<^esub>  x) = \<ominus>\<^bsub>(ZFact n)\<^esub> (res n x)"       
proof-
  have H: "(res n) \<in> ring_hom (ZFact m) (ZFact n)"
  using assms res_hom ZFact_is_cring 
  by simp
  then have A:" res n (x  \<oplus>\<^bsub>ZFact m\<^esub>  (\<ominus>\<^bsub>(ZFact m)\<^esub>  x)) = (res n x) \<oplus>\<^bsub>ZFact n\<^esub> (res n (\<ominus>\<^bsub>(ZFact m)\<^esub>  x))"
    using ring_hom_memE[simp] assms ZFact_is_cring by (simp add: cring.cring_simprules(3)) 
    then have A0: "(res n (\<ominus>\<^bsub>(ZFact m)\<^esub>  x)) \<oplus>\<^bsub>ZFact n\<^esub> (res n (x  \<oplus>\<^bsub>ZFact m\<^esub>  (\<ominus>\<^bsub>(ZFact m)\<^esub>  x))) = (res n (\<ominus>\<^bsub>(ZFact m)\<^esub>  x)) \<oplus>\<^bsub>ZFact n\<^esub> (res n (x  \<oplus>\<^bsub>ZFact m\<^esub>  (\<ominus>\<^bsub>(ZFact m)\<^esub>  x)))"
      using ZFact_is_cring H by blast
    then have A1: "(res n (\<ominus>\<^bsub>(ZFact m)\<^esub>  x)) \<oplus>\<^bsub>ZFact n\<^esub> (res n (x  \<oplus>\<^bsub>ZFact m\<^esub>  (\<ominus>\<^bsub>(ZFact m)\<^esub>  x))) = (res n  (\<ominus>\<^bsub>(ZFact m)\<^esub>  x))" 
      using H  ZFact_is_cring ring_hom_memE[simp] cring.cring_simprules
      by (smt assms(4)) 
    then have A2: "(res n (\<ominus>\<^bsub>(ZFact m)\<^esub>  x)) \<oplus>\<^bsub>ZFact n\<^esub> (res n (x  \<oplus>\<^bsub>ZFact m\<^esub>  (\<ominus>\<^bsub>(ZFact m)\<^esub>  x))) = (\<ominus>\<^bsub>(ZFact n)\<^esub>  (res n x))"
      using A0 ZFact_is_cring H by (metis A
      cring.cring_simprules(17) cring.cring_simprules(19)
      cring.cring_simprules(9) cring.sum_zero_eq_neg res_range) 
    then show ?thesis using A1 A2 
    by blast 
qed

(*TODO multiplication simp for res_hom*)

(*Inverse Limit construction of p-adics*)

type_synonym padic_int = "(nat \<Rightarrow> int set)"

definition residue_ring :: "nat \<Rightarrow>  nat \<Rightarrow> (int set) ring" where
"residue_ring p n = ZFact (p^n)"

definition padic_set :: "nat \<Rightarrow>  (nat \<Rightarrow> int set) set" where
"padic_set p = {(f::nat \<Rightarrow> int set) .(\<forall>(m::nat). (f m) \<in> (carrier (ZFact (p^m))))
                                    \<and>(\<forall>(n::nat) (m::nat). (n > m \<longrightarrow> (res (p^m) (f n) = (f m)))) }"

(*simp rules for reasoning about padic_set*)

lemma padic_set_simp0:
  assumes "f \<in> padic_set p"
  shows "(f m) \<in> (carrier (ZFact (p^m)))" 
  using assms padic_set_def by auto

lemma padic_set_simp1:
  assumes "f \<in> padic_set p"
  assumes "n \<ge> m"
  assumes "p \<noteq>0"
  shows "res (p^m) (f n) = (f m)"
proof(cases "n = m")
  case True
  then show ?thesis 
    using assms(1) padic_set_simp0
    by (simp add: res_id assms(3))
next 
  case False
  show ?thesis
    using assms(1) assms(2) padic_set_def False by auto
qed

(*Lemma for showing that "f \<in> padic_set p" for some fixed p*)

lemma padic_set_mem:
  fixes f :: "padic_int"
  assumes "\<And>m. (f m) \<in> (carrier (ZFact (p^m)))"
  assumes "(\<And>(m::nat) n. (n > m \<longrightarrow> (res (p^m) (f n) = (f m))))"
  shows "f \<in> padic_set p"
proof-
  have "(\<forall>(m::nat). (f m) \<in> (carrier (ZFact (p^m))))"
  proof
    fix m 
    show "f m \<in> carrier (ZFact (int (p ^ m))) "
      by (simp add: assms(1)) 
  qed
  have "(\<forall>(n::nat) (m::nat). (n > m \<longrightarrow> (res (p^m) (f n) = (f m))))"
    by (simp add: assms(2)) 
  then show ?thesis using \<open>\<forall>m. f m \<in> carrier (ZFact (int (p ^ m)))\<close> padic_set_def by auto 
qed

(*padic_addition*)

definition padic_add :: "nat \<Rightarrow> (nat \<Rightarrow> int set) \<Rightarrow> (nat \<Rightarrow> int set) \<Rightarrow> (nat \<Rightarrow> int set) " 
  where "padic_add p f g \<equiv> (\<lambda> n. (f n) \<oplus>\<^bsub>(ZFact (p^n))\<^esub> (g n))"

lemma padic_add_simp:
"(padic_add p f g) n = (f n) \<oplus>\<^bsub>(ZFact (p^n))\<^esub> (g n)"
  by (simp add: padic_add_def) 

(*padic multiplication*)

definition padic_mult :: "nat \<Rightarrow> (nat \<Rightarrow> int set) \<Rightarrow> (nat \<Rightarrow> int set) \<Rightarrow> (nat \<Rightarrow> int set) " 
  where "padic_mult p f g \<equiv> (\<lambda> n. (f n) \<otimes>\<^bsub>(ZFact (p^n))\<^esub> (g n))"

lemma padic_mult_simp: 
"(padic_mult p f g) n = (f n) \<otimes>\<^bsub>(ZFact (p^n))\<^esub> (g n)"
  by (simp add: padic_mult_def) 

(*padic multiplicative unit*)

definition padic_one :: "nat \<Rightarrow> (nat \<Rightarrow> int set)" where
"padic_one p \<equiv> (\<lambda>n. \<one>\<^bsub>ZFact (p^n)\<^esub>)"

lemma padic_one_simp:
 "padic_one p n =  \<one>\<^bsub>ZFact (p^n)\<^esub>"
  by (simp add: padic_one_def) 

(*padic additive unit*)

definition padic_zero :: "nat \<Rightarrow> (nat \<Rightarrow> int set)" where
"padic_zero p \<equiv> (\<lambda>n. \<zero>\<^bsub>ZFact (p^n)\<^esub>)"

lemma padic_zero_simp:
"padic_zero p n = \<zero>\<^bsub>ZFact (p^n)\<^esub>" 
  by (simp add: padic_zero_def) 


(*padic unary minus*)

definition padic_uminus :: "nat \<Rightarrow>  (nat \<Rightarrow> int set) \<Rightarrow>  (nat \<Rightarrow> int set)" where
"padic_uminus p f \<equiv> \<lambda> n. \<ominus>\<^bsub>ZFact (p^n)\<^esub> (f n)"

lemma padic_uminus_simp:
"padic_uminus p f n\<equiv> \<ominus>\<^bsub>ZFact (p^n)\<^esub> (f n)"
   by (simp add: padic_uminus_def) 

(*padic simp rules bundled together*)

lemma padic_simps:
"padic_zero p n = \<zero>\<^bsub>ZFact (p^n)\<^esub>" 
"padic_uminus p f n \<equiv> \<ominus>\<^bsub>ZFact (p^n)\<^esub> (f n)"
"(padic_mult p f g) n = (f n) \<otimes>\<^bsub>(ZFact (p^n))\<^esub> (g n)"
"(padic_add p f g) n = (f n) \<oplus>\<^bsub>(ZFact (p^n))\<^esub> (g n)"
"padic_one p n =  \<one>\<^bsub>ZFact (p^n)\<^esub>"
  apply (simp add: padic_zero_simp) 
  apply (simp add: padic_uminus_simp)
  apply (simp add: padic_mult_def)
  apply (simp add: padic_add_simp)  
  using padic_one_def by auto

(*padic_one is an element of the padics:*)

lemma padic_one_mem:
  assumes "p \<noteq>0"
  shows "padic_one p \<in> padic_set p"
proof(rule padic_set_mem)
  show "\<And>m. padic_one p m \<in> carrier (ZFact (int p ^ m))"
  proof-
    fix m::nat
    show "padic_one p m \<in> carrier (ZFact (int p ^ m)) "
      by (simp add: ZFact_defs(1) ZFact_defs(2)
          int.a_rcosetsI padic_one_simp) 
  qed
  show "\<And>m n. m < n \<longrightarrow> res (p ^ m) (padic_one p n) = padic_one p m"
  proof-
    fix m n::nat
    show " m < n \<longrightarrow> res (p ^ m) (padic_one p n) = padic_one p m"
    proof
      assume "m <n "
      then have "res (p ^ m) (padic_one p n) = padic_one p m"
        using res_hom_p padic_simps[simp] 
        by (metis assms ring_hom_one)
      then have " m < n \<longrightarrow> res (p ^ m) (padic_one p n) = padic_one p m"  
        by blast 
      then show " m < n \<Longrightarrow> res (p ^ m) (padic_one p n) = padic_one p m"
        by auto
    qed
  qed
qed

(*padic_zero is an element of the padics *)

lemma padic_zero_mem:
  assumes "p \<noteq>0"
  shows "padic_zero p \<in> padic_set p" 
    proof-
      have "padic_zero p \<in> padic_set p"
      proof (rule padic_set_mem)
        show "\<And>m. padic_zero p m \<in> carrier (ZFact (int p ^ m))" 
          using padic_simps[simp] ZFact_is_cring cring_def ring.ring_simprules(2)   
          by (simp add: cring_def ring.ring_simprules(2))
          show "\<And>m n. m < n \<longrightarrow> res (p ^ m) (padic_zero p n) =  padic_zero p m" 
        proof
          fix m n::nat
          assume "m <n"
          have D: "p^n mod p^m = 0"
            by (simp add: \<open>m < n\<close> le_imp_power_dvd less_imp_le) 
          then show "res (p ^ m) (padic_zero p n) = padic_zero p m "
          proof(cases "m = 0")
            case True then show ?thesis 
              by (metis (no_types, lifting) ZFact_one 
                  \<open>\<And>m.  padic_zero p m \<in> carrier (ZFact (int p ^ m))\<close> 
                  empty_iff insert_iff of_nat_1 power_0 res_range) 
        next
          case False 
          then have N: " n \<noteq>0"
            using \<open>m < n\<close> by linarith 
          have Z: "( padic_zero p n) \<in> carrier (ZFact (p^n))" 
            using res_hom by (simp add: padic_zero_def ZFact_is_cring cring.cring_simprules(2)) 
          have "(res (p^m)) \<in> ring_hom (ZFact (int (p^n))) (ZFact (int (p^m)))" 
            by (metis D assms power_not_zero res_hom) 
          then have "res (p ^ m) (\<zero>\<^bsub>ZFact (p^n)\<^esub>) = \<zero>\<^bsub>ZFact (p^m)\<^esub>" 
            by (meson ZFact_is_cring cring_def ring_hom_zero) 
          then show "res (p ^ m) ( padic_zero p n) = padic_zero p m" 
            by( simp add: padic_zero_def)
        qed
      qed
    qed
    then show ?thesis by simp 
    qed

(*padic uminus maps to ZFact*)

lemma padic_uminus_range:
  assumes " p \<noteq>0"
  assumes A : "f \<in> padic_set p"
  assumes "prime p"
  shows "(padic_uminus p f) \<in> padic_set p"
proof(rule padic_set_mem)
  show "\<And>m. padic_uminus p f m \<in> carrier (ZFact (int p ^ m))"
  proof-
    fix m
    have "f m \<in>carrier (ZFact (int p ^ m))" 
      using assms padic_set_def by auto 
    then show "padic_uminus p f m \<in> carrier (ZFact (int p ^ m))"
      using padic_uminus_simp[simp] ZFact_is_cring 
      by (simp add: cring.cring_simprules(3)) 
  qed
  show "\<And>m n. m < n \<longrightarrow> res (p ^ m) (padic_uminus p f n) = padic_uminus p f m"
  proof
    fix m n::nat
    assume "m < n"
    show "res (p ^ m) (padic_uminus p f n) = padic_uminus p f m " 
    proof(cases "m = 0")
      case True
      then show ?thesis 
        by (metis ZFact_one \<open>\<And>m. padic_uminus p f m \<in> carrier (ZFact (int p ^ m))\<close> empty_iff insert_iff of_nat_1 power_0 res_range) 
    next
      case False
      then have N: "n \<noteq>0"
        using \<open>m < n\<close> lessE by blast 
      have "p^n mod p^m = 0" 
        by (simp add: \<open>m < n\<close> le_imp_power_dvd less_imp_le) 
      then show ?thesis
      proof
        assume S: " p ^ m dvd p ^ n"
        have 0: "(p ^ m) \<noteq>0" 
          by (simp add: assms(1)) 
        have 1: "(p ^ n) \<noteq>0"
          by (simp add: assms(1)) 
        show " res (p ^ m) (padic_uminus p f n) = padic_uminus p f m"
          using 0 1 False res_hom padic_uminus_simp res_hom_uminus
        by (smt A \<open>m < n\<close> \<open>p ^ n mod p ^ m = 0\<close> mem_Collect_eq padic_set_def)
    qed
  qed
  qed
qed

(*padic set is closed under multiplication*)

lemma padic_mult_mem:
  assumes "f \<in> (padic_set p)"
  assumes "g \<in> (padic_set p)"
  assumes "p \<noteq>0"
  shows "(padic_mult p f g)\<in> (padic_set p)"
proof(rule padic_set_mem)
  show "\<And>m. padic_mult p f g m \<in> carrier (ZFact (int p ^ m))"
  proof-
    fix m
    show "padic_mult p f g m \<in> carrier (ZFact (int p ^ m))"
      using padic_mult_simp by (metis ZFact_is_cring assms(1)
          assms(2) cring.cring_simprules(5) of_nat_power
          padic_set_simp0)
  qed
  show "\<And>m n. m < n \<longrightarrow> res (p ^ m) (padic_mult p f g n) = padic_mult p f g m"
  proof
    show " \<And>m n. m < n \<Longrightarrow> res (p ^ m) (padic_mult p f g n) = padic_mult p f g m"
    proof-
      fix m n::nat
      assume A: "m < n"
      then show "res (p ^ m) (padic_mult p f g n) = padic_mult p f g m"
      proof-
        have "res (p ^ m) \<in> ring_hom (ZFact (int (p ^ n))) (ZFact (int (p ^ m)))"
          using A res_hom_p assms  by blast 
        then show ?thesis using padic_simps[simp] 
          by (smt A assms(1) assms(2) assms(3) less_imp_le padic_set_simp0 padic_set_simp1 ring_hom_mult)
      qed
    qed
  qed
qed

(*padic valuation. Maps 0 to -1 for now, otherwise is correct*)

definition padic_val :: "nat \<Rightarrow>  (nat \<Rightarrow> int set) \<Rightarrow> int"  where
"padic_val p f \<equiv> if (f = padic_zero p) then -1 else int (LEAST k::nat. (f (Suc k)) \<noteq> \<zero>\<^bsub>ZFact (p^(Suc k))\<^esub>)"

(*characterization of padic_val on nonzero elements*)

lemma val_of_nonzero:
  assumes "f \<in> padic_set p"
  assumes "f \<noteq>padic_zero p"
  shows "f (nat (padic_val p f) + 1) \<noteq>  \<zero>\<^bsub>ZFact (p^((nat (padic_val p f) + 1)))\<^esub>"
        "f (nat (padic_val p f)) =  \<zero>\<^bsub>ZFact (p^((nat (padic_val p f))))\<^esub>"
proof-
  let ?vf = "padic_val p f"
  have 0: "?vf =int (LEAST k::nat. (f (Suc k)) \<noteq> \<zero>\<^bsub>ZFact (p^(Suc k))\<^esub>)"
    using assms(2) padic_val_def by auto    
  have 1: "(\<exists> k::nat. (f (Suc k)) \<noteq> \<zero>\<^bsub>ZFact (p^(Suc k))\<^esub>)"
    proof-
      obtain k where 1: "(f k) \<noteq> (padic_zero p k)"
        using assms(2) by (meson ext) 
    have 2: "k \<noteq>0" 
      by (metis (no_types, lifting) ZFact_is_cring ZFact_one 
        \<open>f k \<noteq> padic_zero p k\<close> assms(1) cring.cring_simprules(2) 
        empty_iff insert_iff mem_Collect_eq of_nat_1
        padic_set_def padic_zero_def power_0)
    then obtain m where "k = Suc m"
      by (meson lessI less_Suc_eq_0_disj)
    then have "(f (Suc m)) \<noteq> \<zero>\<^bsub>ZFact (p^(Suc m))\<^esub>" sledgehammer
      using "1" padic_zero_simp by blast     
    then show ?thesis 
      by auto
  qed
  then have "(f (Suc (nat ?vf))) \<noteq> \<zero>\<^bsub>ZFact (p^(Suc (nat ?vf)))\<^esub>" 
    using 0 by (metis (mono_tags, lifting) LeastI_ex nat_int) 
  then show "f (nat (padic_val p f) + 1) \<noteq>  \<zero>\<^bsub>ZFact (p^((nat (padic_val p f) + 1)))\<^esub>" 
    using 0 1 by simp
  show "f (nat (padic_val p f)) =  \<zero>\<^bsub>ZFact (p^((nat (padic_val p f))))\<^esub>"
  proof(cases "(padic_val p f) = 0")
    case True
    then show ?thesis 
      by (metis (no_types, lifting) Num.of_nat_simps(1)
          ZFact_is_cring ZFact_one assms(1) cring.cring_simprules(2)
          empty_iff insert_iff mem_Collect_eq nat_int of_nat_1 
          padic_set_def power.simps(1)) 
  next
    case False 
    have "\<not> f (nat (padic_val p f)) \<noteq> \<zero>\<^bsub>ZFact (int (p ^ nat (padic_val p f)))\<^esub>"
    proof
      assume "f (nat (padic_val p f)) \<noteq> \<zero>\<^bsub>ZFact (int (p ^ nat (padic_val p f)))\<^esub>"
      obtain k where " (Suc k) = (nat (padic_val p f))" using False 
        using "0" gr0_conv_Suc by auto
      then have "?vf  \<noteq> int (LEAST k::nat. (f (Suc k)) \<noteq> \<zero>\<^bsub>ZFact (p^(Suc k))\<^esub>)"
        using False by (metis (mono_tags, lifting) Least_le 
          \<open>f (nat (padic_val p f)) \<noteq> \<zero>\<^bsub>ZFact (int (p ^ nat (padic_val p f)))\<^esub>\<close>
            add_le_same_cancel2 nat_int not_one_le_zero plus_1_eq_Suc)
      then show False  using "0" by blast
    qed    
    then show "f (nat (padic_val p f)) = \<zero>\<^bsub>ZFact (int (p ^ nat (padic_val p f)))\<^esub>" by auto
  qed
qed

lemma below_val_zero:
  assumes "(p::nat) \<noteq> 0"
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "x (Suc n) \<noteq>  \<zero>\<^bsub>ZFact (p^(Suc n))\<^esub>"
  shows  "of_nat n \<ge> (padic_val p x )"
proof(cases "x = padic_zero p")
  case True
  then show  ?thesis  
    using assms(3) padic_zero_def by auto
next
  case False
  then have "padic_val p x = int (LEAST k::nat. x (Suc k) \<noteq> \<zero>\<^bsub>ZFact (p ^ Suc k)\<^esub>)"
    using padic_val_def by auto  
  then show "of_nat n \<ge> (padic_val p x )"
    by (metis (mono_tags, lifting) Least_le assms(3) nat_int nat_le_iff)
qed

lemma  zero_below_val:
  assumes "p \<noteq>0"
  assumes "x \<in> padic_set p"
  assumes "n \<le> padic_val p x"
  shows  "x n =  \<zero>\<^bsub>ZFact (p^n)\<^esub>"
proof(cases "n=0")
  case True
  then have  "x 0 \<in>carrier (ZFact (p^0))" 
    using assms(2) padic_set_simp0  by blast
  then show ?thesis 
    by (metis True ZFact_defs(1) ZFact_defs(2)  
        ZFact_one empty_iff insert_iff
        int.genideal_one of_nat_power power_0 ring_record_simps(11))
  next
    case False 
    show ?thesis 
    proof(cases "x = padic_zero p")
      case True 
      then show ?thesis 
        by (simp add: padic_zero_simp)
      next
        case F: False
        then have A: "padic_val p x = int (LEAST k::nat. (x (Suc k)) \<noteq> \<zero>\<^bsub>ZFact (p^(Suc k))\<^esub>)" 
          using padic_val_def by auto
        have "\<not> (x n) \<noteq> \<zero>\<^bsub>ZFact (p^n)\<^esub>"
        proof
          assume "(x n) \<noteq> \<zero>\<^bsub>ZFact (p^n)\<^esub>"
          obtain k where "n = Suc k" 
            using False old.nat.exhaust by auto
          then have "k \<ge> padic_val p x" using A 
            by (metis (mono_tags, lifting) Least_le
                \<open>x n \<noteq> \<zero>\<^bsub>ZFact (int (p ^ n))\<^esub>\<close> int_eq_iff 
                nat_le_iff padic_zero_def)
          then have "n > padic_val p x" 
            using \<open>n = Suc k\<close> by linarith
          then show False using assms(3) 
            by linarith
        qed
        then show ?thesis 
          by simp
      qed
qed
(*zero is the only element with valuation equal to -1*)

lemma val_zero:
 assumes P: "f \<in> (padic_set p)"   
 shows "padic_val p f = -1 \<longleftrightarrow>  (f = (padic_zero p))"
proof
  show "padic_val p f = -1 \<Longrightarrow>  (f = (padic_zero p))"
  proof
    assume A:"padic_val p f = -1" 
    fix k
    show "f k = padic_zero p k" 
    proof-
      have  "f k \<noteq> padic_zero p k \<Longrightarrow> False"
      proof-
        assume A0: " f k \<noteq> padic_zero p k"
        have False
        proof-
          have "f 0 \<in> carrier (ZFact 1)" using P padic_set_def 
            by (metis (no_types, lifting) mem_Collect_eq of_nat_1 power_0) 
          then have "f 0 = \<zero>\<^bsub>ZFact (p^0)\<^esub>" using ZFact_defs 
            by (metis ZFact_one empty_iff insert_iff int.genideal_one of_nat_1 power_0 ring_record_simps(11)) 
          then have "k>0" 
            using A0 gr0I padic_zero_def by auto    
          then have "(LEAST k. 0 < k \<and> f (Suc k) \<noteq> padic_zero p (Suc k)) \<ge>0 " 
            by simp
          then have "padic_val p f \<ge>0" 
            using A0 padic_val_def by auto 
          then show ?thesis  using A0 by (simp add: A)  
        qed
        then show ?thesis by blast
      qed
      then show ?thesis 
        by blast
    qed
  qed
  assume B: "f = padic_zero p"
  then show "padic_val p f = -1" 
  using padic_val_def by simp 
qed

(*val turns multiplication into integer addition on nonzero elements*)

lemma val_prod:
  assumes  "prime p"
  assumes "f \<in> (padic_set p)" 
  assumes "g \<in> (padic_set p)"
  assumes "f \<noteq> padic_zero p"
  assumes "g \<noteq> padic_zero p"
  shows "padic_val p (padic_mult p f g) = padic_val p f + padic_val p  g"
proof-
  let ?vp = "padic_val p (padic_mult p f g)"
  let ?vf = "padic_val p f"
  let ?vg = "padic_val p g"
  have 0: "f (nat ?vf + 1) \<noteq>  \<zero>\<^bsub>ZFact (p^(nat ?vf + 1))\<^esub>" 
    using assms(2) assms(4) val_of_nonzero by blast
  have 1: "g (nat ?vg + 1) \<noteq>  \<zero>\<^bsub>ZFact (p^(nat ?vg + 1))\<^esub>" 
    using assms(3) assms(5) val_of_nonzero by blast
  have 2: "f (nat ?vf) =  \<zero>\<^bsub>ZFact (p^(nat ?vf))\<^esub>" 
    using assms(2) assms(4) val_of_nonzero(2) by blast 
  have 3: "g (nat ?vg) =  \<zero>\<^bsub>ZFact (p^(nat ?vg))\<^esub>" 
    using assms(3) assms(5) val_of_nonzero(2) by blast
  let ?nm = "(padic_mult p f g) (Suc (nat (?vf + ?vg)))"    
  let ?n = "f (Suc (nat (?vf + ?vg)))"    
  let ?m = "g (Suc (nat (?vf + ?vg)))"  
  have A: "?nm = ?n \<otimes>\<^bsub>ZFact (p^((Suc (nat (?vf + ?vg))))) \<^esub> ?m" 
    using padic_mult_def by auto
  let ?N = "rep ?n"
  let ?M = "rep ?m"
  let ?NM = "rep ?nm"
  have 5: "f (nat ?vf + 1) = res (p^(nat ?vf + 1)) ?n" 
    proof-
      have "Suc (nat (?vf + ?vg)) \<ge>(nat ?vf + 1)" 
        using assms(5) padic_val_def by auto
      then show ?thesis 
        by (metis assms(1) assms(2) not_prime_0 padic_set_simp1)
    qed
  have 6: "f (nat ?vf) = res (p^(nat ?vf)) ?n" 
    proof-
      have "Suc (nat (?vf + ?vg)) \<ge>(nat ?vf)" 
        using assms(5) padic_val_def by auto
      then show ?thesis 
        by (metis assms(1) assms(2) not_prime_0 padic_set_simp1)
    qed
  have 7: "g (nat ?vg + 1) = res (p^(nat ?vg + 1)) ?m"
    proof-
      have "Suc (nat (?vf + ?vg)) \<ge>(nat ?vg + 1)" 
        using assms(4) padic_val_def by auto
      then show ?thesis 
        by (metis assms(1) assms(3) not_prime_0 padic_set_simp1)
    qed
  have 8: "g (nat ?vg) = res (p^(nat ?vg)) ?m"
    proof-
      have "Suc (nat (?vf + ?vg)) \<ge>(nat ?vg)" 
        using assms(4) padic_val_def by auto
      then show ?thesis 
        by (metis assms(1) assms(3) not_prime_0 padic_set_simp1)
    qed
  have 9:"?N mod (p^(nat ?vf + 1)) \<noteq>0" using 0 5 
    by (smt ZMod_mod assms(1) mod_mod_trivial
        of_nat_0_less_iff prime_gt_0_nat rep_is_mod0 
        rep_pos res_def res_range zero_less_power)
  have 10:"?N mod (p^(nat ?vf)) = 0" 
    using 2 6 by (metis (mono_tags, hide_lams) ZFact_defs(1) ZFact_defs(2)
             ZMod_defs(1) ZMod_eq_mod  int.a_coset_add_zero mod_0
             padic_zero_def res_def ring_record_simps(11) top.extremum)
  have 11:"?M mod (p^(nat ?vg + 1)) \<noteq>0"
    using 1 7  by (smt ZMod_mod assms(1) mod_mod_trivial
        of_nat_0_less_iff prime_gt_0_nat rep_is_mod0
        rep_pos res_def res_range zero_less_power)
  have 12:"?M mod (p^(nat ?vg)) = 0"
    using 3 8  by (metis (mono_tags, hide_lams) ZFact_defs(1)
        ZFact_defs(2) ZMod_defs(1) ZMod_eq_mod  int.a_coset_add_zero
        mod_0  padic_zero_def res_def ring_record_simps(11) top.extremum)
  
  have "\<exists> i. ?N = i*p^(nat ?vf) \<and> \<not> p dvd (nat i)"
  proof-
    have "nat ?N>0"
      using 9 rep_def by auto 
    then obtain i  k where 13: "\<not> p dvd (nat i) \<and> nat ?N = (nat i)*p^k"
      using prime_power_canonical assms(1) by (metis nat_int)
    have "k \<ge> nat ?vf"
    proof-
    have "\<not> k< nat ?vf"
    proof
      assume "k < nat ?vf"
      then have "nat ?N mod (p^(nat ?vf)) \<noteq> 0" using 13 
        by (metis Groups.mult_ac(2) assms(1) mod_eq_0D prime_power_cancel_less)
      then have "?N mod (p^(nat ?vf)) \<noteq> 0"  
        by (smt \<open>0 < nat (rep (f (Suc (nat (padic_val p f + padic_val p g)))))\<close>
            gr_implies_not_zero nat_code(2) nat_int nat_mod_distrib
            of_nat_less_0_iff split_nat)
      then show False
         using 10 by auto
    qed
    then show ?thesis by auto
    qed
    have "k = nat ?vf" 
    proof-
      have "\<not> nat ?vf < k"
      proof
      assume "nat ?vf < k"
      have P: "?N mod (p^k) = 0" using 13 
        by (simp add: rep_def)
      have "(nat ?vf + 1) \<le>k" 
        using \<open>nat (padic_val p f) < k\<close> discrete by blast
      then have "(p^(nat ?vf + 1)) dvd ?N" using P 
        by (metis  mod_0_imp_dvd of_nat_power power_le_dvd)
      then show False
        using 9 by (metis dvd_imp_mod_0)
    qed
      then show ?thesis 
        using \<open>nat (padic_val p f) \<le> k\<close> by linarith 
    qed
    then show ?thesis 
      by (metis "13" mult.commute nat_int rep_def)
  qed
  then obtain i where 13:"?N = i*p^(nat ?vf) \<and> \<not> p dvd (nat i)" 
    by blast
  have "\<exists> i. ?M = i*p^(nat ?vg) \<and> \<not> p dvd (nat i)"
  proof-
    have "nat ?M>0"
      using 11 rep_def by auto 
    then obtain i  k where 13: "\<not> p dvd (nat i) \<and> nat ?M = (nat i)*p^k"
      using prime_power_canonical assms(1) by (metis nat_int)
    have "k \<ge> nat ?vg"
    proof-
    have "\<not> k< nat ?vg"
    proof
      assume "k < nat ?vg"
      then have "nat ?M mod (p^(nat ?vg)) \<noteq> 0" using 13 
        by (metis Groups.mult_ac(2) assms(1) mod_eq_0D prime_power_cancel_less)
      then have "?M mod (p^(nat ?vg)) \<noteq> 0"  
        by (smt \<open>0 < nat (rep (g (Suc (nat (padic_val p f + padic_val p g)))))\<close>
            gr_implies_not_zero nat_code(2) nat_int nat_mod_distrib
            of_nat_less_0_iff split_nat)
      then show False
         using 12 by auto
    qed
    then show ?thesis by auto
    qed
    have "k = nat ?vg" 
    proof-
      have "\<not> nat ?vg < k"
      proof
      assume "nat ?vg < k"
      have P: "?M mod (p^k) = 0" using 13 
        by (simp add: rep_def)
      have "(nat ?vg + 1) \<le>k" 
        using \<open>nat (padic_val p g) < k\<close> discrete by blast
      then have "(p^(nat ?vg + 1)) dvd ?N" using P 
        by (metis "11" dvd_imp_mod_0 mod_0_imp_dvd of_nat_power power_le_dvd)
      then show False
        using 11 by (metis P \<open>nat (padic_val p g) + 1 \<le> k\<close> 
            dvd_imp_mod_0 mod_0_imp_dvd of_nat_power power_le_dvd)
    qed
      then show ?thesis 
        using \<open>nat (padic_val p g) \<le> k\<close> by linarith 
    qed
    then show ?thesis 
      by (metis "13" mult.commute nat_int rep_def)
  qed
  then obtain j where 14:"?M = j*p^(nat ?vg) \<and> \<not> p dvd (nat j)" 
    by blast
  let ?i = "(p^(Suc (nat (?vf + ?vg))))"
  have "?NM mod ?i = ?N*?M mod ?i"
  proof-
    have P1:"?NM = rep (?n \<otimes>\<^bsub>ZFact ?i \<^esub> ?m)"
      using A by simp
    have P2:"(?n \<otimes>\<^bsub>ZFact ?i \<^esub> ?m) = (ZMod ?i (?N)) \<otimes>\<^bsub>ZFact ?i\<^esub>   (ZMod ?i (?M))" 
      using rep_prop by (smt assms(1) assms(2) assms(3)
          of_nat_0_less_iff padic_set_simp0 prime_gt_0_nat
          zero_less_power)
    then have P3:"(?n \<otimes>\<^bsub>ZFact ?i \<^esub> ?m) = (ZMod ?i (?N*?M))" 
      by (simp add: ZFact_defs(1) ZFact_defs(2) ZMod_defs(1) ideal.rcoset_mult_add int.genideal_ideal)
    then show ?thesis 
      by (smt A Euclidean_Division.pos_mod_sign ZMod_eq_mod 
          ZMod_mod assms(1) of_nat_0_less_iff prime_gt_0_nat
          rep_is_mod0 zero_less_power)
  qed
  then have 15: "?NM mod ?i =  i*j*p^((nat ?vf) +(nat ?vg)) mod ?i"
    using 13 14 by (metis of_nat_mult power_add
        semiring_normalization_rules(13) zmod_int) 
  have 16: "\<not> p dvd (i*j)" using 13 14 
    by (simp add: assms(1) prime_dvd_mult_iff)
  have 17: "((nat ?vf) +(nat ?vg)) < (Suc (nat (?vf + ?vg)))" 
    by (simp add: assms(4) assms(5) padic_val_def)
  have 18:"?NM mod ?i \<noteq>0" 
  proof
    assume A: "?NM mod ?i = 0" 
    obtain x where "?NM = x*?i" 
      using "15" "16" A assms(4) assms(5) nat_int_add padic_val_def by auto
    then show False
      using prime_power_cancel_less 15 16 17  
      by (smt A One_nat_def assms(1) discrete mod_0_imp_dvd
          mult.commute mult.right_neutral nat_mult_dvd_cancel_disj
          not_prime_0 of_nat_eq_0_iff power_0 power_Suc power_add
          power_le_dvd power_not_zero)
  qed
  have 19: "(?NM mod ?i ) mod (p^(nat ?vf + nat ?vg)) = 0"
    using 15 by (simp add: assms(4) assms(5) nat_add_distrib padic_val_def)
  then have 20: "?NM mod (p^(nat ?vf + nat ?vg)) = 0" 
    by (metis "17" dvd_triv_right int_dvd_int_iff
        linorder_not_le mod_mod_cancel not_less_eq 
        plus_1_eq_Suc power_add power_le_dvd)
  have 21: "(padic_mult p f g) \<noteq> padic_zero p"
  proof
    assume "(padic_mult p f g) =  padic_zero p"
    then have "(padic_mult p f g) (Suc (nat (padic_val p f + padic_val p g))) =  padic_zero p (Suc (nat (padic_val p f + padic_val p g)))"
      by simp
    then have "?NM  = rep (padic_zero p (Suc (nat (padic_val p f + padic_val p g))))"
      using ZFact_defs ZMod_defs rep_prop rep_is_mod0 padic_simps by simp
    then have "?NM = 0"  
      using rep_zero  assms(1) padic_zero_simp prime_gt_0_nat by auto   
    then show False
      using "18" by auto
  qed
  have 22: "(padic_mult p f g)\<in> (padic_set p)" 
    using padic_mult_mem  by (metis assms(1) assms(2) assms(3) not_prime_0)
  have 23: "\<And> j. j < Suc (nat (padic_val p f + padic_val p g)) \<Longrightarrow> (padic_mult p f g) j = \<zero>\<^bsub>ZFact (p^j)\<^esub>"
  proof-
    fix j
    let ?j = "Suc (nat (padic_val p f + padic_val p g))"
    assume P: "j < ?j"
    show "(padic_mult p f g) j = \<zero>\<^bsub>ZFact (p^j)\<^esub>" 
      proof-
      have P0: "(padic_mult p f g) (nat ?vf + nat ?vg) = \<zero>\<^bsub>ZFact (p^(nat ?vf + nat ?vg))\<^esub>"
        proof-
          let ?k = "(nat ?vf + nat ?vg)"
          have "((padic_mult p f g) ?k) = res (p^?k) ((padic_mult p f g) ?k) " 
            using P 22 padic_set_simp1 by (simp add: assms(1) prime_gt_0_nat)
          then have "((padic_mult p f g) ?k) = res (p^?k) ?nm" 
            by (metis "17" "22" Zero_not_Suc assms(1)
            gr0_conv_Suc nat_less_le padic_set_simp1 prime_gt_0_nat)
          then have "((padic_mult p f g) ?k) = ZMod (p^?k) ?NM" 
            by (simp add: res_def)
          then have "((padic_mult p f g) ?k) = ZMod (p^?k) 0"  
            using 20 rep_prop rep_is_mod0  ZFact_defs by (metis ZMod_mod)
          then show ?thesis using ZFact_defs 
            by (smt ZFact_is_cring assms(1) cring.cring_simprules(2)
                of_nat_0 of_nat_le_0_iff of_nat_less_0_iff power_eq_0_iff
                prime_gt_0_nat rep_prop rep_zero)
        qed
      then show ?thesis 
      proof(cases "j = (nat ?vf + nat ?vg)")
      case True then show ?thesis  
        using P0 by blast
    next
      case B: False
       then have "((padic_mult p f g) j) = res (p^j) ((padic_mult p f g) (nat ?vf + nat ?vg)) " 
         using B P 22 padic_set_simp1 by (simp add: assms(1) assms(4) assms(5) padic_val_def prime_gt_0_nat) 
       then have S: "((padic_mult p f g) j) = res (p^j) \<zero>\<^bsub>ZFact (p^((nat ?vf + nat ?vg)))\<^esub>" 
         by (simp add: P0)
       have "res (p^j) \<in> ring_hom (ZFact (p^((nat ?vf + nat ?vg)))) (ZFact (p^j))"
         using B P assms(1) assms(4) assms(5) 
           padic_val_def prime_gt_0_nat res_hom_p by auto
       then show ?thesis using S 
         by (smt ZFact_is_cring assms(1) cring.cring_simprules(2)
             of_nat_0_less_iff prime_gt_0_nat rep_prop rep_zero res_def zero_less_power)
     qed
    qed
  qed
  have 24: "(padic_mult p f g) (Suc (nat ?vf + nat ?vg)) \<noteq> \<zero>\<^bsub>ZFact (int (p ^ Suc (nat (padic_val p f + padic_val p g))))\<^esub>" 
    using "18" ZFact_is_cring assms(1) cring.cring_simprules(2)
      of_nat_eq_0_iff of_nat_less_0_iff prime_gt_0_nat rep_is_mod0 
      rep_prop rep_zero zero_less_power 
    using assms(4) assms(5) nat_add_distrib padic_val_def by force
  have 25: "padic_val p (padic_mult p f g) = int (LEAST k::nat. ((padic_mult p f g) (Suc k)) \<noteq> \<zero>\<^bsub>ZFact (int p^(Suc k))\<^esub>)"
    using padic_val_def 21 by auto 
  have "(nat (padic_val p f + padic_val p g)) \<in> {k::nat. ((padic_mult p f g) (Suc k)) \<noteq> \<zero>\<^bsub>ZFact (int p^(Suc k))\<^esub>}" using 24 
    using "18" assms(1) prime_gt_0_nat rep_zero by force
  then have "(LEAST k::nat. ((padic_mult p f g) (Suc k)) \<noteq> \<zero>\<^bsub>ZFact (int p^(Suc k))\<^esub>) = (nat (padic_val p f + padic_val p g))"
    by (smt "21" "22" "23" "25" Suc_inject Suc_less_SucD add.commute linorder_neqE_nat mem_Collect_eq nat_int not_less_Least plus_1_eq_Suc val_of_nonzero(1))
  then have "padic_val p (padic_mult p f g) = (nat (padic_val p f + padic_val p g))" 
    using "25" by linarith
  then show ?thesis 
    by (simp add: assms(4) assms(5) padic_val_def)
qed

(*abbreviation for the ring of p_adic integers*)

abbreviation padic_int :: "nat \<Rightarrow> padic_int ring"
  where "padic_int (p::nat) \<equiv> \<lparr>carrier = (padic_set p),
         Group.monoid.mult = (padic_mult p), one = (padic_one p), 
          zero = (padic_zero p), add = (padic_add p)\<rparr>"

(*padic multiplication is associative*)

lemma padic_mult_assoc:
assumes "prime p"
shows  "\<And>x y z.
       x \<in> carrier (padic_int p) \<Longrightarrow>
       y \<in> carrier (padic_int p) \<Longrightarrow> 
       z \<in> carrier (padic_int p) \<Longrightarrow>
       x \<otimes>\<^bsub>padic_int p\<^esub> y \<otimes>\<^bsub>padic_int p\<^esub> z = x \<otimes>\<^bsub>padic_int p\<^esub> (y \<otimes>\<^bsub>padic_int p\<^esub> z)"
proof-
  fix x y z
  assume Ax: " x \<in> carrier (padic_int p)"
  assume Ay: " y \<in> carrier (padic_int p)"
  assume Az: " z \<in> carrier (padic_int p)"
  show "x \<otimes>\<^bsub>padic_int p\<^esub> y \<otimes>\<^bsub>padic_int p\<^esub> z = x \<otimes>\<^bsub>padic_int p\<^esub> (y \<otimes>\<^bsub>padic_int p\<^esub> z)"
  proof
    fix n
    show "((x \<otimes>\<^bsub>padic_int p\<^esub> y) \<otimes>\<^bsub>padic_int p\<^esub> z) n = (x \<otimes>\<^bsub>padic_int p\<^esub> (y \<otimes>\<^bsub>padic_int p\<^esub> z)) n"
  using padic_simps[simp] ZFact_is_cring 
    by (smt Ax Ay Az cring.cring_simprules(11)
        mem_Collect_eq monoid.simps(1) padic_set_def partial_object.select_convs(1))
  qed
  qed

(*The padics are closed under addition*)

lemma add_closed:
  assumes "prime p"
  shows  "\<And>x y. x \<in> carrier (padic_int p) \<Longrightarrow> y \<in> carrier (padic_int p) \<Longrightarrow> x \<oplus>\<^bsub>(padic_int p)\<^esub> y \<in> carrier (padic_int p)"
 proof
      fix x::"padic_int"
      fix y::"padic_int"
      assume Px: "x \<in>carrier (padic_int p) "
      assume Py: "y \<in>carrier (padic_int p)"
      show "x \<oplus>\<^bsub>(padic_int p)\<^esub> y \<in> carrier (padic_int p)"
      proof-
        let ?f = "x \<oplus>\<^bsub>(padic_int p)\<^esub> y"
        have 0: "(\<forall>(m::nat). (?f m) \<in> (carrier (ZFact (p^m))))"
        proof fix m
          have A1 : "?f m = (x m) \<oplus>\<^bsub>(ZFact (p^m))\<^esub> (y m)"
             by (simp add: padic_add_def)  
          have A2: "(x m) \<in>(carrier (ZFact (p^m)))" 
            using Px by (simp add: padic_set_def) 
          have A3: "(y m) \<in>(carrier (ZFact (p^m)))" 
            using Py by (simp add: padic_set_def) 
          then show "(?f m) \<in> (carrier (ZFact (p^m)))" 
            using padic_zero_def ZFact_is_cring A2
                cring.cring_simprules(1) A1 by fastforce  
        qed
        have 1: "(\<forall>(n::nat) (m::nat). (n > m \<longrightarrow> (res (p^m) (?f n) = (?f m))))" 
        proof 
          fix n::nat
          show "(\<forall>(m::nat). (n > m \<longrightarrow> (res (p^m) (?f n) = (?f m))))" 
          proof
            fix m::nat
            show "(n > m \<longrightarrow> (res (p^m) (?f n) = (?f m)))"
              proof
                assume A: "m < n"
                show "(res (p^m) (?f n) = (?f m))"
                proof(cases "m = 0")
                  case True 
                  then show ?thesis
                    using A by (metis (no_types, lifting)
                        "0" ZFact_one empty_iff insert_iff
                        of_nat_1 power_0 res_range) 
                next
                  case False
                  then have  "m \<noteq>0" using A by linarith
                  have D: "p^n mod p^m = 0" using A 
                    using assms divides_primepow_nat dvd_imp_mod_0 less_imp_le by blast 
                  let ?LHS = "res (p ^ m) ((x \<oplus>\<^bsub>padic_int p\<^esub> y) n)"
                  have A0: "?LHS = res (p ^ m) ((x n)\<oplus>\<^bsub>ZFact (p^n)\<^esub>( y n))" 
                    by (simp add: padic_add_def)  
                  have "res (p^m) \<in> ring_hom (ZFact (int (p^n))) (ZFact (int (p^m)))"
                    by (metis D assms not_prime_0 power_not_zero res_hom) 
                  then have "res (p ^ m) ((x n)\<oplus>\<^bsub>ZFact (p^n)\<^esub>( y n)) = (res (p ^ m) (x n))\<oplus>\<^bsub>ZFact (p^m)\<^esub>((res (p ^ m) (y n)))"  
                    by (metis (no_types, lifting) Px Py mem_Collect_eq padic_set_def partial_object.select_convs(1) ring_hom_add) 
                  then have "?LHS =(res (p ^ m) (x n))\<oplus>\<^bsub>ZFact (p^m)\<^esub>((res (p ^ m) (y n)))" 
                    using A0 by force 
                  then show ?thesis
                    using A Px Py padic_set_def by (simp add: padic_add_def) 
                qed
              qed
            qed
          qed
          then show ?thesis
            using "0" padic_set_mem by auto 
        qed
        then have "  x \<oplus>\<^bsub>padic_int p\<^esub> y \<in> (padic_set p)" 
        by simp
      then show "carrier (padic_int p) \<subseteq> carrier (padic_int p)" 
        by blast  
    qed

(*padic addition is associative*)

lemma padic_add_assoc:
assumes "prime p"
shows  " \<And>x y z.
       x \<in> carrier (padic_int p) \<Longrightarrow>
       y \<in> carrier (padic_int p) \<Longrightarrow> z \<in> carrier (padic_int p)
       \<Longrightarrow> x \<oplus>\<^bsub>padic_int p\<^esub> y \<oplus>\<^bsub>padic_int p\<^esub> z = x \<oplus>\<^bsub>padic_int p\<^esub> (y \<oplus>\<^bsub>padic_int p\<^esub> z)"
proof-
  fix x y z
  assume Ax: "x \<in> carrier (padic_int p)"
  assume Ay: "y \<in> carrier (padic_int p)"
  assume Az: "z \<in> carrier (padic_int p)"
  show " (x \<oplus>\<^bsub>padic_int p\<^esub> y) \<oplus>\<^bsub>padic_int p\<^esub> z = x \<oplus>\<^bsub>padic_int p\<^esub> (y \<oplus>\<^bsub>padic_int p\<^esub> z)"
    proof
      fix n
      show "((x \<oplus>\<^bsub>padic_int p\<^esub> y) \<oplus>\<^bsub>padic_int p\<^esub> z) n = (x \<oplus>\<^bsub>padic_int p\<^esub> (y \<oplus>\<^bsub>padic_int p\<^esub> z)) n "
      proof-
        have Ex: "(x n) \<in> carrier (ZFact (p^n))" 
          using Ax padic_set_def by auto 
        have Ey: "(y n) \<in> carrier (ZFact (p^n))" 
          using Ay padic_set_def by auto 
        have Ez: "(z n) \<in> carrier (ZFact (p^n))" 
          using Az padic_set_def by auto 
        let ?x = "(x n)"
        let ?y = "(y n)"
        let ?z = "(z n)"
        have P1: "(?x \<oplus>\<^bsub>ZFact (p^n)\<^esub> ?y) \<oplus>\<^bsub>ZFact (p^n)\<^esub> ?z = (x n) \<oplus>\<^bsub>ZFact (p^n)\<^esub> ((y \<oplus>\<^bsub>padic_int p\<^esub> z) n)"
          using ZFact_is_cring Ex Ey Ez 
          by (simp add: cring.cring_simprules(7) padic_add_def) 
        have " ((y n)) \<oplus>\<^bsub>ZFact (p^n)\<^esub> z n =((y \<oplus>\<^bsub>padic_int p\<^esub> z) n)"
          using padic_add_def by simp 
        then have P0: "(x n) \<oplus>\<^bsub>ZFact (p^n)\<^esub> ((y \<oplus>\<^bsub>padic_int p\<^esub> z) n) = ((x n) \<oplus>\<^bsub>ZFact (p^n)\<^esub> ((y n) \<oplus>\<^bsub>ZFact (p^n)\<^esub> z n))"
          using padic_add_def by simp 
        have "((x \<oplus>\<^bsub>padic_int p\<^esub> y) \<oplus>\<^bsub>padic_int p\<^esub> z) n = ((x  \<oplus>\<^bsub>padic_int p\<^esub> y) n) \<oplus>\<^bsub>ZFact (p^n)\<^esub> z n"
          using padic_add_def  by simp
        then have  "((x \<oplus>\<^bsub>padic_int p\<^esub> y) \<oplus>\<^bsub>padic_int p\<^esub> z) n =((x n) \<oplus>\<^bsub>ZFact (p^n)\<^esub> (y n)) \<oplus>\<^bsub>ZFact (p^n)\<^esub> z n"
          using padic_add_def  by simp 
        then have  "((x \<oplus>\<^bsub>padic_int p\<^esub> y) \<oplus>\<^bsub>padic_int p\<^esub> z) n =((x n) \<oplus>\<^bsub>ZFact (p^n)\<^esub> ((y n) \<oplus>\<^bsub>ZFact (p^n)\<^esub> z n))"
          using Ex Ey Ez P1 P0 by blast 
        then have  "((x \<oplus>\<^bsub>padic_int p\<^esub> y) \<oplus>\<^bsub>padic_int p\<^esub> z) n = (x n) \<oplus>\<^bsub>ZFact (p^n)\<^esub> ((y \<oplus>\<^bsub>padic_int p\<^esub> z) n)"
          using P0  by blast
        then show ?thesis by (simp add: padic_add_def) 
      qed
    qed
   qed

(*padic addition is commutative*)
lemma padic_add_comm:
  assumes "prime p"
  shows " \<And>x y. x \<in> carrier (padic_int p) \<Longrightarrow> y \<in> carrier (padic_int p) \<Longrightarrow> x \<oplus>\<^bsub>padic_int p\<^esub> y = y \<oplus>\<^bsub>padic_int p\<^esub> x"
    proof-
      fix x y
      assume Ax: "x \<in> carrier (padic_int p)" assume Ay:"y \<in> carrier (padic_int p)"
      show "x \<oplus>\<^bsub>padic_int p\<^esub> y = y \<oplus>\<^bsub>padic_int p\<^esub> x"
      proof fix n
        show "(x \<oplus>\<^bsub>padic_int p\<^esub> y) n = (y \<oplus>\<^bsub>padic_int p\<^esub> x) n " 
          using Ax Ay padic_add_def ZFact_is_cring 
          by (simp add: cring.cring_simprules(10) padic_set_def) 
      qed
    qed

(*padic_zero is an additive identity*)
lemma padic_add_zero:
assumes "prime p"
shows "\<And>x. x \<in> carrier (padic_int p) \<Longrightarrow> \<zero>\<^bsub>padic_int p\<^esub> \<oplus>\<^bsub>padic_int p\<^esub> x = x"
proof-
  fix x
  assume Ax: "x \<in> carrier (padic_int p)"
  show " \<zero>\<^bsub>padic_int p\<^esub> \<oplus>\<^bsub>padic_int p\<^esub> x = x " 
  proof fix n
    show "(\<zero>\<^bsub>padic_int p\<^esub> \<oplus>\<^bsub>padic_int p\<^esub> x) n = x n" 
      using Ax padic_zero_def padic_add_def ZFact_is_cring 
      by (simp add: cring.cring_simprules(8) padic_set_def) 
  qed
qed

(*padic_zero is closed under additive inverses*)
lemma padic_add_inv:
  assumes "prime p"
  shows "\<And>x. x \<in> carrier (padic_int p) \<Longrightarrow> \<exists>y\<in>carrier (padic_int p). y \<oplus>\<^bsub>padic_int p\<^esub> x = \<zero>\<^bsub>padic_int p\<^esub>"
proof-
  fix x
  assume Ax: " x \<in> carrier (padic_int p)"
  show "\<exists>y\<in>carrier (padic_int p). y \<oplus>\<^bsub>padic_int p\<^esub> x = \<zero>\<^bsub>padic_int p\<^esub>"
    proof
      let ?y = "(padic_uminus p) x"
      show "?y \<oplus>\<^bsub>padic_int p\<^esub> x = \<zero>\<^bsub>padic_int p\<^esub>"
      proof 
        fix n
        show  "(?y \<oplus>\<^bsub>padic_int p\<^esub> x) n = \<zero>\<^bsub>padic_int p\<^esub> n" 
          using Ax padic_simps[simp] ZFact_is_cring 
          by (simp add: cring.cring_simprules(9) padic_set_def) 
      qed
      then show "padic_uminus p x \<in> carrier (padic_int p)" 
        using padic_uminus_range
          Ax assms prime_gt_0_nat by auto 
    qed
  qed

(*The ring of padic integers forms an abelian group under addition*)

lemma padic_is_abelian_group:
assumes "prime p"
shows "abelian_group (padic_int p)"
  proof (rule abelian_groupI)
    show "\<And>x y. x \<in> carrier (padic_int p) \<Longrightarrow> y \<in> carrier (padic_int p) \<Longrightarrow> x \<oplus>\<^bsub>(padic_int p)\<^esub> y \<in> carrier (padic_int p)"
      using add_closed  by (simp add: assms)
    show zero: "\<zero>\<^bsub>padic_int p\<^esub> \<in> carrier (padic_int p)" 
      by (metis assms not_prime_0 padic_zero_mem
          partial_object.select_convs(1) ring_record_simps(11))
    show add_assoc: " \<And>x y z.
       x \<in> carrier (padic_int p) \<Longrightarrow>
       y \<in> carrier (padic_int p) \<Longrightarrow> z \<in> carrier (padic_int p)
       \<Longrightarrow> x \<oplus>\<^bsub>padic_int p\<^esub> y \<oplus>\<^bsub>padic_int p\<^esub> z = x \<oplus>\<^bsub>padic_int p\<^esub> (y \<oplus>\<^bsub>padic_int p\<^esub> z)"
      using assms padic_add_assoc by auto
    show comm: " \<And>x y. x \<in> carrier (padic_int p) \<Longrightarrow> y \<in> carrier (padic_int p) \<Longrightarrow> x \<oplus>\<^bsub>padic_int p\<^esub> y = y \<oplus>\<^bsub>padic_int p\<^esub> x"
      using assms padic_add_comm by blast
    show "\<And>x. x \<in> carrier (padic_int p) \<Longrightarrow> \<zero>\<^bsub>padic_int p\<^esub> \<oplus>\<^bsub>padic_int p\<^esub> x = x"
      using assms padic_add_zero by blast
    show "\<And>x. x \<in> carrier (padic_int p) \<Longrightarrow> \<exists>y\<in>carrier (padic_int p). y \<oplus>\<^bsub>padic_int p\<^esub> x = \<zero>\<^bsub>padic_int p\<^esub>"
      using assms padic_add_inv by blast
  qed

(*padic_one is a multiplicative identity*)

lemma padic_one_id:
assumes "prime p"
assumes "x \<in> carrier (padic_int p)"
shows  "\<one>\<^bsub>padic_int p\<^esub> \<otimes>\<^bsub>padic_int p\<^esub> x = x"
proof
  fix n
  show "(\<one>\<^bsub>padic_int p\<^esub> \<otimes>\<^bsub>padic_int p\<^esub> x) n = x n "
    by (metis ZFact_is_cring assms(2) cring.cring_simprules(12)
        monoid.select_convs(1) monoid.select_convs(2) 
        padic_set_simp0 padic_simps(3) padic_simps(5)
        partial_object.select_convs(1))
qed

(*padic multiplication is commutative*)

lemma padic_mult_comm:
assumes "prime p"
assumes "x \<in> carrier (padic_int p)"
assumes "y \<in> carrier (padic_int p)"
shows "x \<otimes>\<^bsub>padic_int p\<^esub> y = y \<otimes>\<^bsub>padic_int p\<^esub> x"
proof
  fix n
  have Ex: "(x n) \<in> carrier (ZFact (p^n))" 
    using padic_set_def assms(2) by auto
  have Ey: "(y n) \<in>carrier (ZFact (p^n))"
    using padic_set_def assms(3) padic_set_simp0 by auto
  show "(x \<otimes>\<^bsub>padic_int p\<^esub> y) n = (y \<otimes>\<^bsub>padic_int p\<^esub> x) n"
    using padic_simps[simp] ZFact_is_cring 
      Ex Ey cring.cring_simprules(14) by fastforce 
qed
  
lemma padic_is_comm_monoid:
assumes "prime p"
shows "Group.comm_monoid (padic_int p)"
proof(rule comm_monoidI)
  show  "\<And>x y. x \<in> carrier (padic_int p) \<Longrightarrow> y \<in> carrier (padic_int p) \<Longrightarrow> x \<otimes>\<^bsub>padic_int p\<^esub> y \<in> carrier (padic_int p)"
    by (metis assms monoid.select_convs(1) not_prime_0 padic_mult_mem partial_object.select_convs(1))
  show "\<one>\<^bsub>padic_int p\<^esub> \<in> carrier (padic_int p)" 
    by (metis assms monoid.select_convs(2) 
        not_prime_0 padic_one_mem 
          partial_object.select_convs(1))
  show "\<And>x y z. x \<in> carrier (padic_int p) \<Longrightarrow>
                y \<in> carrier (padic_int p) \<Longrightarrow> 
                z \<in> carrier (padic_int p) \<Longrightarrow>
                x \<otimes>\<^bsub>padic_int p\<^esub> y \<otimes>\<^bsub>padic_int p\<^esub> z = x \<otimes>\<^bsub>padic_int p\<^esub> (y \<otimes>\<^bsub>padic_int p\<^esub> z)"
    using assms padic_mult_assoc by auto
  show "\<And>x. x \<in> carrier (padic_int p) \<Longrightarrow> \<one>\<^bsub>padic_int p\<^esub> \<otimes>\<^bsub>padic_int p\<^esub> x = x"
    using assms padic_one_id by blast
  show "\<And>x y. x \<in> carrier (padic_int p) \<Longrightarrow>
              y \<in> carrier (padic_int p) \<Longrightarrow>
              x \<otimes>\<^bsub>padic_int p\<^esub> y = y \<otimes>\<^bsub>padic_int p\<^esub> x"
    using padic_mult_comm  by (simp add: assms)
qed

(*The padic integers form a commutative ring when p is prime*)

lemma padic_int_is_cring:
  assumes "prime (p::nat)"
  shows "cring (padic_int p)"
proof (rule cringI)
  show "abelian_group (padic_int p)"
    by (simp add: assms padic_is_abelian_group)
  show "Group.comm_monoid (padic_int p)"
    by (simp add: assms padic_is_comm_monoid)
  show "\<And>x y z.
       x \<in> carrier (padic_int p) \<Longrightarrow>
       y \<in> carrier (padic_int p) \<Longrightarrow>
       z \<in> carrier (padic_int p) \<Longrightarrow>
       (x \<oplus>\<^bsub>padic_int p\<^esub> y) \<otimes>\<^bsub>padic_int p\<^esub> z = x \<otimes>\<^bsub>padic_int p\<^esub> z \<oplus>\<^bsub>padic_int p\<^esub> y \<otimes>\<^bsub>padic_int p\<^esub> z "
  proof-
    fix x y z
    assume Ax: " x \<in> carrier (padic_int p)"
    assume Ay: " y \<in> carrier (padic_int p)"
    assume Az: " z \<in> carrier (padic_int p)"
    show "(x \<oplus>\<^bsub>padic_int p\<^esub> y) \<otimes>\<^bsub>padic_int p\<^esub> z = x \<otimes>\<^bsub>padic_int p\<^esub> z \<oplus>\<^bsub>padic_int p\<^esub> y \<otimes>\<^bsub>padic_int p\<^esub> z"
    proof
      fix n
      have Ex: " (x n) \<in> carrier (ZFact (p^n))" 
        using Ax padic_set_def by auto
      have Ey: " (y n) \<in> carrier (ZFact (p^n))" 
        using Ay padic_set_def by auto
      have Ez: " (z n) \<in> carrier (ZFact (p^n))" 
        using Az padic_set_def by auto
      show "( (x \<oplus>\<^bsub>padic_int p\<^esub> y) \<otimes>\<^bsub>padic_int p\<^esub> z) n = (x \<otimes>\<^bsub>padic_int p\<^esub> z \<oplus>\<^bsub>padic_int p\<^esub> y \<otimes>\<^bsub>padic_int p\<^esub> z) n "
        using padic_simps[simp] ZFact_is_cring
          Ex Ey Ez cring.cring_simprules(13) by fastforce
    qed
  qed
qed

(*The padic ring has no nontrivial zero divisors*)

lemma padic_no_zero_divisors:
assumes "prime p"
assumes "a \<in> carrier (padic_int p)"
assumes "b \<in>carrier (padic_int p)"
assumes "a \<noteq>\<zero>\<^bsub>padic_int p\<^esub> "
assumes "b \<noteq>\<zero>\<^bsub>padic_int p\<^esub> "
shows "a \<otimes>\<^bsub>padic_int p\<^esub> b \<noteq> \<zero>\<^bsub>padic_int p\<^esub> "
proof
  assume C: "a \<otimes>\<^bsub>padic_int p\<^esub> b = \<zero>\<^bsub>padic_int p\<^esub>"
  show False
  proof-
    have 0: "a = \<zero>\<^bsub>padic_int p\<^esub> \<or> b = \<zero>\<^bsub>padic_int p\<^esub>"
    proof(cases "a = \<zero>\<^bsub>padic_int p\<^esub>")
      case True
      then show ?thesis by auto
    next
      case False
      have "\<not> b  \<noteq>\<zero>\<^bsub>padic_int p\<^esub>"
      proof
        assume "b \<noteq> \<zero>\<^bsub>padic_int p\<^esub>"
        have "padic_val p (a \<otimes>\<^bsub>padic_int p\<^esub> b) = (padic_val p a) + (padic_val p b)" 
          using False assms(1) assms(2) assms(3) assms(5) val_prod by auto
          then have "padic_val p (a \<otimes>\<^bsub>padic_int p\<^esub> b) \<noteq> -1" 
          using False \<open>b \<noteq> \<zero>\<^bsub>padic_int p\<^esub>\<close> padic_val_def by auto
        then show False 
          using C padic_val_def by auto      
        qed
      then show ?thesis 
        by blast
    qed
    show ?thesis 
      using "0" assms(4) assms(5) by blast
  qed
qed

(*padic integers form an integral domain*)

lemma padic_int_is_domain:
  assumes "prime (p::nat)"
  shows "domain (padic_int p)"
proof(rule domainI)
  show "cring (padic_int p)" 
    using padic_int_is_cring assms(1) by auto
  show "\<one>\<^bsub>padic_int p\<^esub> \<noteq> \<zero>\<^bsub>padic_int p\<^esub>"
  proof
    assume "\<one>\<^bsub>padic_int p\<^esub> = \<zero>\<^bsub>padic_int p\<^esub> "
    then have "(\<one>\<^bsub>padic_int p\<^esub>) (1::nat) = \<zero>\<^bsub>padic_int p\<^esub> 1" by auto
    show False using assms(1) padic_simps[simp] ZFact_prime_is_domain 
      by (metis \<open>\<one>\<^bsub>padic_int p\<^esub> = \<zero>\<^bsub>padic_int p\<^esub>\<close>
          domain.one_not_zero monoid.simps(2)
          prime_nat_int_transfer ring.simps(1)
          semiring_normalization_rules(33))
  qed
  show "\<And>a b. a \<otimes>\<^bsub>padic_int p\<^esub> b = \<zero>\<^bsub>padic_int p\<^esub> \<Longrightarrow> a \<in> carrier (padic_int p) \<Longrightarrow> b \<in> carrier (padic_int p)  \<Longrightarrow> a = \<zero>\<^bsub>padic_int p\<^esub> \<or> b = \<zero>\<^bsub>padic_int p\<^esub>"
    using assms padic_no_zero_divisors by blast
qed     

lemma ultrametric:
  assumes "prime p"
  assumes "a \<in> carrier (padic_int p) "
  assumes "b \<in> carrier (padic_int p) "
  assumes "a \<noteq> \<zero>\<^bsub>(padic_int p)\<^esub>"
  assumes "b \<noteq> \<zero>\<^bsub>(padic_int p)\<^esub>"
  assumes  "a \<oplus>\<^bsub>(padic_int p)\<^esub> b \<noteq> \<zero>\<^bsub>(padic_int p)\<^esub>"
  shows "padic_val p (a \<oplus>\<^bsub>(padic_int p)\<^esub> b) \<ge> min (padic_val p a) (padic_val p b)"
proof-
  let ?va = " nat (padic_val p a)"
  let ?vb = "nat (padic_val p b)"
  let ?vab = "nat (padic_val p (a \<oplus>\<^bsub>(padic_int p)\<^esub> b))"
  have " \<not> ?vab < min ?va ?vb"
  proof
    assume P0: "?vab < min ?va ?vb"
    then have "Suc ?vab \<le> min ?va ?vb"
      using Suc_leI by blast
    have "(a \<oplus>\<^bsub>(padic_int p)\<^esub> b) \<in> carrier (padic_int p) " 
      using assms(1) assms(2) assms(3)  add_closed by simp
    then have C: "(a \<oplus>\<^bsub>(padic_int p)\<^esub> b) (?vab + 1) \<noteq>  \<zero>\<^bsub>ZFact (p^(?vab + 1))\<^esub>" 
      using val_of_nonzero(1) assms(6) by (metis partial_object.select_convs(1)
          ring_record_simps(11))
    have S: "(a \<oplus>\<^bsub>(padic_int p)\<^esub> b) (?vab + 1) = (a (?vab + 1)) \<oplus>\<^bsub>ZFact (p^((?vab + 1)))\<^esub> (b ((?vab + 1)))"  
      by (simp add: padic_add_def)
    have "int (?vab + 1) \<le> padic_val p a" 
      using P0  using Suc_le_eq by auto
    then have A: "(a (?vab + 1)) = \<zero>\<^bsub>ZFact (int p^((?vab + 1)))\<^esub> " 
      using assms(1) assms(2) zero_below_val 
      by (smt add.commute below_val_zero of_nat_0_less_iff
          of_nat_1 of_nat_add of_nat_le_0_iff of_nat_power 
          plus_1_eq_Suc prime_gt_0_nat)
    have "int (?vab + 1) \<le> padic_val p b" 
      using P0  using Suc_le_eq by auto
    then have B: "(b (?vab + 1)) = \<zero>\<^bsub>ZFact (int p^((?vab + 1)))\<^esub> " 
      using assms(1) assms(3) zero_below_val 
      by (smt add.commute below_val_zero of_nat_0_less_iff
          of_nat_1 of_nat_add of_nat_le_0_iff of_nat_power 
          plus_1_eq_Suc prime_gt_0_nat)
    then have "(a \<oplus>\<^bsub>(padic_int p)\<^esub> b) (?vab + 1) = \<zero>\<^bsub>ZFact (int p^((?vab + 1)))\<^esub> " 
      using A B ZFact_is_cring by (metis (no_types, lifting) 
          S cring.cring_simprules(2) cring.cring_simprules(8) of_nat_power)
    then show False using C by auto
  qed
  then show ?thesis by (smt assms(6) int_nat_eq
        min_def nat_int nat_less_iff padic_val_def
        ring_record_simps(11))
qed

lemma padic_inv:
  assumes "prime p"
  assumes "a \<in> carrier (padic_int p)"
  shows "\<ominus>\<^bsub>padic_int p\<^esub> a = (\<lambda> n. \<ominus>\<^bsub>ZFact (p^n)\<^esub> (a n))"
proof
  fix n
  have "(\<ominus>\<^bsub>padic_int p\<^esub> a) n \<oplus>\<^bsub>ZFact (p^n)\<^esub> (a n) = \<zero>\<^bsub>ZFact (p^n)\<^esub>" 
    by (metis (no_types, hide_lams) abelian_groupE(6) assms(1) 
        assms(2) cring.sum_zero_eq_neg padic_add_simp 
        padic_int_is_cring padic_is_abelian_group 
        padic_zero_def partial_object.select_convs(1) 
        ring_record_simps(11) ring_record_simps(12)) 
  then show "(\<ominus>\<^bsub>padic_int p\<^esub> a) n = \<ominus>\<^bsub>ZFact (int (p ^ n))\<^esub> a n" 
    by (metis ZFact_is_cring assms(1) assms(2) cring.cring_simprules(3) 
        cring.sum_zero_eq_neg padic_int_is_cring padic_set_simp0
        partial_object.select_convs(1)) 
qed

lemma padic_val_add_inv:
  assumes "prime p"
  assumes "a \<in> carrier (padic_int p)"
  shows "padic_val p a = padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a)"
proof(cases "a = \<zero>\<^bsub>padic_int p\<^esub>")
  case True
  then show ?thesis 
    by (metis assms(1) cring.cring_simprules(22) padic_int_is_cring) 
next
  case False
  have 0: "\<And> n. (a n) = \<zero>\<^bsub>ZFact (p^n)\<^esub> \<Longrightarrow> (\<ominus>\<^bsub>padic_int p\<^esub> a) n = \<zero>\<^bsub>ZFact (p^n)\<^esub>"
    using padic_inv by (metis (no_types, hide_lams) ZFact_is_cring assms(1)
        assms(2) cring.cring_simprules(22)  padic_zero_simp) 
  have 1: "\<And> n. (a n) \<noteq> \<zero>\<^bsub>ZFact (p^n)\<^esub> \<Longrightarrow> (\<ominus>\<^bsub>padic_int p\<^esub> a) n \<noteq> \<zero>\<^bsub>ZFact (p^n)\<^esub>"
    using padic_inv 
    by (metis (no_types, lifting) ZFact_is_cring assms(1) assms(2) 
        cring.cring_simprules(21) cring.cring_simprules(22) 
        cring.cring_simprules(3) padic_int_is_cring) 
  have A:"padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a) \<ge> (padic_val p a)" 
  proof-  
    let ?n = "nat (padic_val p a)"
    have "a (Suc ?n) \<noteq> \<zero>\<^bsub>ZFact (p^(Suc ?n))\<^esub> " 
      using False assms(2) val_of_nonzero(1) by auto
    then have "(\<ominus>\<^bsub>padic_int p\<^esub> a) (Suc ?n) \<noteq> \<zero>\<^bsub>ZFact (p^(Suc ?n))\<^esub> "
      using 1  by blast 
    then show ?thesis using assms(1) assms(2) below_val_zero 
      by (smt "0" One_nat_def add.right_neutral add_Suc_right
          cring.cring_simprules(3) cring.cring_simprules(9)
          nat_int of_nat_0_less_iff of_nat_le_0_iff padic_add_zero
          padic_int_is_cring padic_val_def partial_object.select_convs(1)
          prime_gt_0_nat ring.simps(1) val_of_nonzero(1))                           
  qed
  have B: "padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a) \<le> (padic_val p a)" 
  proof-
   let ?n = "nat (padic_val p a)"
    have "a (Suc ?n) \<noteq> \<zero>\<^bsub>ZFact (p^(Suc ?n))\<^esub> " 
      using False assms(2) val_of_nonzero(1) by auto
    then have "(\<ominus>\<^bsub>padic_int p\<^esub> a) (Suc ?n) \<noteq> \<zero>\<^bsub>ZFact (p^(Suc ?n))\<^esub> "
      using 1  by blast 
    then have  "padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a) \<le> int ?n"  using assms(1) assms(2) below_val_zero  
      by (metis cring.cring_simprules(3) less_eq_nat.simps(1)  not_le padic_int_is_cring prime_gt_0_nat)
    then show ?thesis 
      using False padic_val_def by auto 
  qed
  then show ?thesis using A B by auto
qed
(*The maximal ideal of padic_int*)


end