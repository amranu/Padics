theory padic_field
  imports p_adic_fields
          Localization
          Extended_OAG
extended_int
          fraction_field
begin


locale padic_integers =
fixes Z\<^sub>p:: "_ ring" (structure)
fixes Q\<^sub>p:: "_ ring" (structure)
fixes p
fixes G
defines "G \<equiv> extended_int.int_eoag"
defines "Z\<^sub>p \<equiv> padic_int p"
defines "Q\<^sub>p \<equiv> domain.Frac Z\<^sub>p"
assumes prime: "prime p"

lemma(in padic_integers) Zp_is_domain:
"domain Z\<^sub>p" 
  using  padic_integers_axioms padic_int_is_domain prime  Z\<^sub>p_def by blast  

lemma(in padic_integers) Qp_is_field:
"field Q\<^sub>p"
  by (simp add: Q\<^sub>p_def Zp_is_domain domain.fraction_field_is_field) 

(*choice function for numerator*)
definition(in padic_integers) denom where
"denom = domain.denom Z\<^sub>p"

definition(in padic_integers) numer where
"numer = domain.numer Z\<^sub>p"

definition(in padic_integers) frac where
"frac = domain.frac Z\<^sub>p"     

fun fromSome :: "'a option \<Rightarrow> 'a" where
  "fromSome (Some x) = x"



definition(in padic_integers) val_Zp  where
"val_Zp = (\<lambda>x. (if (x = \<zero>\<^bsub>Z\<^sub>p\<^esub>) then (\<infinity>\<^bsub>G\<^esub>) else (Some (padic_val p x))))"

definition(in padic_integers) ord_Zp where
"ord_Zp = padic_val p"

lemma(in padic_integers) val_ord_Zp:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "a \<noteq> \<zero>"
  shows "Some (ord_Zp a) = val_Zp a" 
  by (simp add: assms(2) ord_Zp_def val_Zp_def) 

lemma(in padic_integers) ord_Zp_mult:
  assumes "x \<in> nonzero Z\<^sub>p"
  assumes "y \<in> nonzero Z\<^sub>p"
  shows "(ord_Zp (x \<otimes>\<^bsub>Z\<^sub>p\<^esub> y)) = (ord_Zp x) + (ord_Zp y)"
proof-
  have 0: "x \<in> padic_set p"
  proof -
    have "x \<in> carrier Z\<^sub>p"
      using assms(1) nonzero_def by fastforce
    then show ?thesis
      by (metis (lifting) Z\<^sub>p_def  partial_object.select_convs(1))
  qed
  have 1: "y \<in> padic_set p"
  proof-
    have "y \<in> carrier Z\<^sub>p"
      using assms(2) nonzero_def by fastforce
    then show ?thesis
      by (metis (lifting) Z\<^sub>p_def  partial_object.select_convs(1))
  qed 
  have 2: "x \<noteq> (padic_zero p)" 
  proof -
    have "\<zero> \<noteq> x"
      using assms(1) nonzero_def by fastforce
    then show ?thesis
      by (metis (no_types) Z\<^sub>p_def ring_record_simps(11))
  qed
  have 3: "y \<noteq> (padic_zero p)"
  proof -
    have "\<zero> \<noteq> y"
      using assms(2) nonzero_def by fastforce
    then show ?thesis
      by (metis (no_types) Z\<^sub>p_def  ring_record_simps(11))
  qed

  show ?thesis using 0 1 2 3 prime val_prod ord_Zp_def  
    by (metis monoid.select_convs(1) Z\<^sub>p_def) 
qed

lemma(in padic_integers) ord_Zp_zero:
 "ord_Zp \<one> = 0"
proof-
  have "ord_Zp \<one> = ord_Zp (\<one>\<otimes>\<one>)" 
    using Zp_is_domain cring.cring_simprules(12)
      cring.cring_simprules(6) domain_def by fastforce 
  then have "ord_Zp \<one> = (ord_Zp \<one>) + (ord_Zp \<one>)" 
    using Localization.submonoid.one_closed Zp_is_domain
      domain.nonzero_is_submonoid ord_Zp_mult by fastforce 
  then show ?thesis 
    by auto 
qed

lemma(in padic_integers) ord_Zp_ultrametric:
  assumes "x \<in> nonzero Z\<^sub>p"
  assumes "y \<in> nonzero Z\<^sub>p"
  assumes "x \<oplus> y \<in> nonzero Z\<^sub>p"
  shows "ord_Zp (x \<oplus> y) \<ge> min (ord_Zp x) (ord_Zp y)"
proof-
  have 0:"x \<in> carrier (padic_int p)"
       "y \<in> carrier (padic_int p)"
       "x \<noteq> \<zero>\<^bsub>padic_int p\<^esub>"
       "y \<noteq> \<zero>\<^bsub>padic_int p\<^esub>"
       "x \<oplus> y \<noteq> \<zero>\<^bsub>padic_int p\<^esub>"
    using assms(1) 
     apply(simp add: Z\<^sub>p_def nonzero_def) 
    using  assms(2)
     apply(simp add: Z\<^sub>p_def nonzero_def)
    using assms(1) 
     apply(simp add: Z\<^sub>p_def nonzero_def)  
    using assms(2)
     apply(simp add: Z\<^sub>p_def nonzero_def) 
    using assms(3)
     apply(simp add: Z\<^sub>p_def nonzero_def) 
    done
  have 1: "min (padic_val p x) (padic_val p y) \<le> padic_val p (x \<oplus>\<^bsub>padic_int p\<^esub> y) \<Longrightarrow> ?thesis"
    apply(simp add: ord_Zp_def)
    apply(simp add: Z\<^sub>p_def)
    done
 
  show ?thesis proof(rule 1)
    show "min (padic_val p x) (padic_val p y) \<le> padic_val p (x \<oplus>\<^bsub>padic_int p\<^esub> y)" 
      using ultrametric 0 1 prime  by (simp add: local.Z\<^sub>p_def) 
  qed
qed

lemma(in padic_integers) val_Zp_mult:
  assumes "x \<in> nonzero Z\<^sub>p"
  assumes "y \<in> nonzero Z\<^sub>p"
  assumes "x \<oplus> y \<in> carrier Z\<^sub>p"
  shows "(val_Zp (x \<otimes>\<^bsub>Z\<^sub>p\<^esub> y)) = (val_Zp x) \<otimes>\<^bsub>G\<^esub> (val_Zp y)"
proof(cases "x \<oplus> y \<noteq> \<zero>")
  case True
  then show ?thesis 
  proof-
    have 0: "(val_Zp (x \<otimes>\<^bsub>Z\<^sub>p\<^esub> y)) = Some (ord_Zp (x \<otimes>\<^bsub>Z\<^sub>p\<^esub> y))"
      using assms(3) val_ord_Zp True  sledgehammer 
      have 1: "val_Zp x = Some (ord_Zp x)"
sledgehammer 

(*Defining the valuation on Qp*)

definition(in padic_integers) ord where
"ord x = (ord_Zp (numer x)) - (ord_Zp (denom x))"

definition(in padic_integers) val where
"val x = (if (x = \<zero>\<^bsub>Q\<^sub>p\<^esub>) then \<infinity>\<^bsub>G\<^esub> else (Some (ord x)))"


definition(in padic_integers) max_ideal :: "padic_int set"   where
"max_ideal = {x \<in> carrier Z\<^sub>p. (ord_Zp x) \<ge> (1::int) \<or> x = \<zero>}"

lemma(in padic_integers) max_ideal_is_ideal:
"ideal max_ideal Z\<^sub>p"
proof(rule idealI)
  show "ring Z\<^sub>p" 
    using cring.axioms(1) padic_int_is_cring
      Z\<^sub>p_def padic_integers_axioms prime by blast
  show "subgroup max_ideal (add_monoid Z\<^sub>p)"
  proof
    show "max_ideal \<subseteq> carrier (add_monoid Z\<^sub>p)" 
      using padic_integers.max_ideal_def padic_integers_axioms max_ideal_def by auto
    show "\<And>x y. x \<in> max_ideal \<Longrightarrow> y \<in> max_ideal \<Longrightarrow> x \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub> y \<in> max_ideal"
    proof-
      fix x y
      assume A1: "x \<in> max_ideal"
      assume A2: "y \<in> max_ideal"
      show "x \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub> y \<in> max_ideal"
      proof(cases "x = \<zero>\<^bsub>Z\<^sub>p\<^esub>")
        case True
        then show ?thesis 
          using \<open>ring Z\<^sub>p\<close> \<open>y \<in> max_ideal\<close> max_ideal_def ring.ring_simprules(8) by fastforce
      next case F1: False
        show ?thesis
        proof(cases "y = \<zero>\<^bsub>Z\<^sub>p\<^esub>") 
          case True
          then show ?thesis 
          using \<open>ring Z\<^sub>p\<close> \<open>x \<in> max_ideal \<close> max_ideal_def ring.ring_simprules(15) by fastforce 
        next case F2: False
          have Cx: "x \<in>carrier Z\<^sub>p" using A1 
            using max_ideal_def by blast
          have Cy: "y \<in>carrier Z\<^sub>p" using A2 
            using max_ideal_def by blast
          show ?thesis
          proof(cases "x \<oplus>\<^bsub>Z\<^sub>p\<^esub> y = \<zero>\<^bsub>Z\<^sub>p\<^esub>")
            case True then show ?thesis 
              by (simp add: \<open>ring Z\<^sub>p\<close> max_ideal_def ring.ring_simprules(2))
          next
            case False
            have "ord_Zp (x \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub> y) \<ge> min (ord_Zp x) (ord_Zp y)"
              using ord_Zp_def Z\<^sub>p_def False prime
                Cx Cy F1 F2 ultrametric by simp
            then have 0: "ord_Zp (x \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub> y) \<ge>1" 
              using max_ideal_def A1 A2  F1 F2 by force
            have "ring Z\<^sub>p" 
              by (simp add: \<open>ring Z\<^sub>p\<close>)
            then have 1: "x \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub> y \<in> carrier Z\<^sub>p" using Cx Cy   
              by (simp add: ring.ring_simprules(1))
            then show ?thesis using 0 1 
              using max_ideal_def by blast
          qed
        qed
      qed
    qed
    show "\<one>\<^bsub>add_monoid Z\<^sub>p\<^esub> \<in> max_ideal " 
      by (simp add: \<open>ring Z\<^sub>p\<close> max_ideal_def ring.ring_simprules(2))
    show "\<And>x. x \<in> max_ideal \<Longrightarrow> inv\<^bsub>add_monoid Z\<^sub>p\<^esub> x \<in> max_ideal"
      using padic_val_add_inv 
      by (smt Zp_is_domain a_inv_def abelian_group_def
          abelian_monoid.a_monoid cring.cring_simprules(3)
          domain_def local.Z\<^sub>p_def max_ideal_def mem_Collect_eq
          monoid.inv_one monoid.select_convs(2) ord_Zp_def padic_is_abelian_group prime) 
  qed
  show "\<And>a x. a \<in> max_ideal \<Longrightarrow> x \<in> carrier Z\<^sub>p \<Longrightarrow> x \<otimes>\<^bsub>Z\<^sub>p\<^esub> a \<in> max_ideal"
  proof
    fix a x
    assume A1: "a \<in> max_ideal"
    assume A2: "x \<in> carrier Z\<^sub>p"
    show "x \<otimes>\<^bsub>Z\<^sub>p\<^esub> a \<in> max_ideal" 
    proof(cases "x = \<zero>\<^bsub>Z\<^sub>p\<^esub>")
      case True
      then show ?thesis 
        using \<open>a \<in> max_ideal\<close> \<open>ring Z\<^sub>p\<close> \<open>x \<in> carrier Z\<^sub>p\<close> max_ideal_def
          ring.ring_simprules(24) by fastforce
      next
        case F1: False
        show ?thesis 
        proof(cases "a = \<zero>\<^bsub>Z\<^sub>p\<^esub>")
          case True then show ?thesis 
            using \<open>a \<in> max_ideal\<close> \<open>ring Z\<^sub>p\<close> \<open>x \<in> carrier Z\<^sub>p\<close>
              ring.ring_simprules(25) by fastforce
        next
          case F2: False 
          have 0: "a \<in> carrier Z\<^sub>p"
            using A1 max_ideal_def by blast
          then have 1: "x \<otimes>\<^bsub>Z\<^sub>p\<^esub> a \<in> carrier Z\<^sub>p" 
            by (simp add: A2 \<open>ring Z\<^sub>p\<close> ring.ring_simprules(5))
          have 2: "ord_Zp (x \<otimes>\<^bsub>Z\<^sub>p\<^esub> a) = (ord_Zp x) + (ord_Zp a)"
            using prime 0 A2 F1 F2 val_prod  
            by (metis monoid.simps(1) Z\<^sub>p_def 
                padic_integers_axioms partial_object.select_convs(1)
                ring.simps(1) ord_Zp_def)
          have 3: "ord_Zp x \<ge>0" 
            using F1 Z\<^sub>p_def padic_integers_axioms padic_val_def ord_Zp_def by fastforce
          have 4: "ord_Zp a \<ge>1" 
            using A1 F2 max_ideal_def by blast
          have "ord_Zp (x \<otimes>\<^bsub>Z\<^sub>p\<^esub> a) \<ge>1" 
            using "2" "3" "4" by linarith 
          then show ?thesis 
            using "1" max_ideal_def by blast
        qed
      qed
      show "\<And>a x. a \<in> max_ideal \<Longrightarrow> x \<in> carrier Z\<^sub>p \<Longrightarrow> max_ideal \<subseteq> max_ideal" 
        by blast
    qed
    show "\<And>a x. a \<in> max_ideal \<Longrightarrow> x \<in> carrier Z\<^sub>p \<Longrightarrow> a \<otimes>\<^bsub>Z\<^sub>p\<^esub> x \<in> max_ideal " 
      by (metis (mono_tags, lifting) \<open>\<And>x a. \<lbrakk>a \<in> max_ideal ; x \<in> carrier Z\<^sub>p\<rbrakk> \<Longrightarrow> x \<otimes>\<^bsub>Z\<^sub>p\<^esub> a \<in> max_ideal \<close> 
          cring.cring_simprules(14) max_ideal_def mem_Collect_eq padic_int_is_cring
          Z\<^sub>p_def padic_integers_axioms prime)
  qed



  