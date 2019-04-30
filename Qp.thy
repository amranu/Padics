theory Qp
  imports p_adic_fields
          Localization
          Extended_OAG
begin

abbreviation nonzero_padic_ints :: "nat \<Rightarrow> padic_int set"
  where "nonzero_padic_ints p \<equiv> {x. x \<in> (padic_set p) \<and> x \<noteq> (padic_zero p)}"

lemma nonzero_is_monoid:
  assumes "prime p"
  shows "submonoid (padic_int p) (nonzero_padic_ints p)"
proof
  show 0: "\<And>x y. x \<in> carrier (padic_int p) \<Longrightarrow> y \<in> carrier (padic_int p) \<Longrightarrow> x \<otimes>\<^bsub>(padic_int p)\<^esub> y \<in> carrier (padic_int p)"
    using padic_int_is_domain 
    by (metis assms monoid.select_convs(1) 
        not_prime_0 padic_mult_mem partial_object.select_convs(1)) 
  show "\<And>x y z. x \<in> carrier  (padic_int p) \<Longrightarrow>
                 y \<in> carrier (padic_int p) \<Longrightarrow>
                 z \<in> carrier  (padic_int p)\<Longrightarrow> 
          x \<otimes>\<^bsub> (padic_int p)\<^esub> y \<otimes>\<^bsub> (padic_int p)\<^esub> z = x \<otimes>\<^bsub> (padic_int p)\<^esub> (y \<otimes>\<^bsub> (padic_int p)\<^esub> z)" 
    using assms padic_mult_assoc by auto
  show "\<one>\<^bsub>(padic_int p)\<^esub> \<in> carrier (padic_int p)" 
    by (metis assms monoid.select_convs(2) not_prime_0
        padic_one_mem partial_object.select_convs(1))
  show "\<And>x. x \<in> carrier (padic_int p) \<Longrightarrow> \<one>\<^bsub>(padic_int p)\<^esub> \<otimes>\<^bsub>(padic_int p)\<^esub> x = x" 
    using assms padic_one_id by auto
  show "\<And>x. x \<in> carrier (padic_int p) \<Longrightarrow> x \<otimes>\<^bsub>(padic_int p)\<^esub> \<one>\<^bsub>(padic_int p)\<^esub> = x" 
    by (meson assms cring_def monoid.r_one padic_int_is_cring ring_def)
  show "nonzero_padic_ints p \<subseteq> carrier (padic_int p)" 
    by (simp add: subset_iff)
  show "\<And>x y. x \<in> nonzero_padic_ints p \<Longrightarrow> 
        y \<in> nonzero_padic_ints p \<Longrightarrow>
         x \<otimes>\<^bsub>(padic_int p)\<^esub> y \<in> nonzero_padic_ints p" 
    using 0 assms padic_no_zero_divisors by auto
  show " \<one>\<^bsub>padic_int p\<^esub> \<in> nonzero_padic_ints p" 
    by (metis (mono_tags, lifting) \<open>\<one>\<^bsub>padic_int p\<^esub> \<in> carrier (padic_int p)\<close>
        assms domain.one_not_zero mem_Collect_eq padic_int_is_domain
        partial_object.select_convs(1) ring_record_simps(11))
qed

lemma thing:
  assumes "prime p"
  shows "eq_obj_rng_of_frac (padic_int p) (nonzero_padic_ints p)" 
proof-
  have 0: "cring (padic_int p)" using padic_int_is_domain 
    using assms padic_int_is_cring by blast
  have 1: "submonoid (padic_int p) (nonzero_padic_ints p)"
    using assms nonzero_is_monoid by auto
  show ?thesis using 0 1 
    using cring_def eq_obj_rng_of_frac.intro
      mult_submonoid_of_crng_def mult_submonoid_of_rng_def by blast
qed

definition padic_field:: "nat \<Rightarrow> _ ring" where 
"padic_field p = eq_obj_rng_of_frac.rec_rng_of_frac (padic_int p) (nonzero_padic_ints p)"

lemma is_ring_padic:
  assumes "prime p"
  shows "ring (padic_field p)"
  using eq_obj_rng_of_frac.rng_rng_of_frac 
  by (simp add: eq_obj_rng_of_frac.rng_rng_of_frac assms padic_field_def thing)

definition padic_rel :: "nat \<Rightarrow> _" where
 "padic_rel p  \<equiv> \<lparr>carrier = ((carrier (padic_int p)) \<times> (nonzero_padic_ints p)), eq = \<lambda>(r, s) (r', s'). (\<exists>t \<in> (nonzero_padic_ints p). t \<otimes>\<^bsub>(padic_int p)\<^esub> (s' \<otimes>\<^bsub>(padic_int p)\<^esub> r \<ominus>\<^bsub>(padic_int p)\<^esub> s \<otimes>\<^bsub>(padic_int p)\<^esub> r') = \<zero>\<^bsub>(padic_int p)\<^esub>)\<rparr>"

fun fromSome :: "'a option \<Rightarrow> 'a" where
  "fromSome (Some x) = x"

locale padic = 
fixes M
fixes S
fixes rel 
assumes "\<exists> (p::nat). (prime p) \<and> M = (padic_int p) \<and> S = nonzero_padic_ints p"
defines "rel \<equiv> \<lparr>carrier = ((carrier M) \<times> S), eq = \<lambda>(r, s) (r', s'). (\<exists>t \<in> S. t \<otimes>\<^bsub>M\<^esub> (s' \<otimes>\<^bsub>M\<^esub> r \<ominus>\<^bsub>M\<^esub> s \<otimes>\<^bsub>M\<^esub> r') = \<zero>\<^bsub>M\<^esub>)\<rparr>"

sublocale padic \<subseteq> submonoid 
  using nonzero_is_monoid padic_axioms padic_def by auto

locale padic_integers = submonoid +
  fixes p::nat
  fixes G 
  fixes val
  fixes ord
  assumes prime: "prime p"
  assumes ring_def: "M = padic_int p"
  assumes group: "G = int_eoag"
  assumes val: "val = (\<lambda>x. (if (x = \<zero>\<^bsub>M\<^esub>) then (\<infinity>\<^bsub>G\<^esub>) else (Some (padic_val p x))))"
  assumes ord: "ord = padic_val p"


  


 definition(in padic_integers) nonzero where
"nonzero = (nonzero_padic_ints p)"

lemma(in padic_integers) v_val:
  assumes "x \<noteq> \<zero>\<^bsub>M\<^esub>"
  assumes "x \<in> carrier M"
  shows "val x = Some (ord x)"
  by (simp add: assms(1) ord val)

definition(in padic_integers) max_ideal :: "padic_int set" ("m")  where
"max_ideal = {x \<in> carrier M. (ord x) \<ge> (1::int) \<or> x = \<zero>\<^bsub>M\<^esub>}" 

lemma(in padic_integers) max_ideal_is_ideal:
"ideal max_ideal M"
proof(rule idealI)
  show "ring M" 
    using cring.axioms(1) padic_int_is_cring
      padic_integers.ring_def padic_integers_axioms prime by blast
  show "subgroup max_ideal (add_monoid M)"
  proof
    show "m \<subseteq> carrier (add_monoid M)" 
      using padic_integers.max_ideal_def padic_integers_axioms max_ideal_def by auto
    show "\<And>x y. x \<in> m \<Longrightarrow> y \<in> m \<Longrightarrow> x \<otimes>\<^bsub>add_monoid M\<^esub> y \<in> m"
    proof-
      fix x y
      assume A1: "x \<in> m"
      assume A2: "y \<in> m"
      show "x \<otimes>\<^bsub>add_monoid M\<^esub> y \<in> m"
      proof(cases "x = \<zero>\<^bsub>M\<^esub>")
        case True
        then show ?thesis 
          using \<open>ring M\<close> \<open>y \<in> m\<close> max_ideal_def ring.ring_simprules(8) by fastforce
      next case F1: False
        show ?thesis
        proof(cases "y = \<zero>\<^bsub>M\<^esub>") 
          case True
          then show ?thesis 
          using \<open>ring M\<close> \<open>x \<in> m\<close> max_ideal_def ring.ring_simprules(15) by fastforce 
        next case F2: False
          have Cx: "x \<in>carrier M" using A1 
            using max_ideal_def by blast
          have Cy: "y \<in>carrier M" using A2 
            using max_ideal_def by blast
          show ?thesis
          proof(cases "x \<oplus>\<^bsub>M\<^esub> y = \<zero>\<^bsub>M\<^esub>")
            case True then show ?thesis 
              by (simp add: \<open>ring M\<close> max_ideal_def ring.ring_simprules(2))
          next
            case False
            have "ord (x \<otimes>\<^bsub>add_monoid M\<^esub> y) \<ge> min (ord x) (ord y)"
              using ord ring_def False prime
                Cx Cy F1 F2 ultrametric by simp
            then have 0: "ord(x \<otimes>\<^bsub>add_monoid M\<^esub> y) \<ge>1" 
              using max_ideal_def A1 A2  F1 F2 by force
            have "ring M" 
              by (simp add: \<open>ring M\<close>)
            then have 1: "x \<otimes>\<^bsub>add_monoid M\<^esub> y \<in> carrier M" using Cx Cy   
              by (simp add: ring.ring_simprules(1))
            then show ?thesis using 0 1 
              using max_ideal_def by blast
          qed
        qed
      qed
    qed
    show "\<one>\<^bsub>add_monoid M\<^esub> \<in> m" 
      by (simp add: \<open>ring M\<close> max_ideal_def ring.ring_simprules(2))
    show "\<And>x. x \<in> m \<Longrightarrow> inv\<^bsub>add_monoid M\<^esub> x \<in> m"
      sorry
  qed
  show "\<And>a x. a \<in> m \<Longrightarrow> x \<in> carrier M \<Longrightarrow> x \<otimes>\<^bsub>M\<^esub> a \<in> m"
  proof
    fix a x
    assume A1: "a \<in> m"
    assume A2: "x \<in> carrier M"
    show "x \<otimes>\<^bsub>M\<^esub> a \<in> m" 
    proof(cases "x = \<zero>\<^bsub>M\<^esub>")
      case True
      then show ?thesis 
        using \<open>a \<in> m\<close> \<open>ring M\<close> \<open>x \<in> carrier M\<close> max_ideal_def
          ring.ring_simprules(24) by fastforce
      next
        case F1: False
        show ?thesis 
        proof(cases "a = \<zero>\<^bsub>M\<^esub>")
          case True then show ?thesis 
            using \<open>a \<in> m\<close> \<open>ring M\<close> \<open>x \<in> carrier M\<close>
              ring.ring_simprules(25) by fastforce
        next
          case F2: False 
          have 0: "a \<in> carrier M"
            using A1 max_ideal_def by blast
          then have 1: "x \<otimes>\<^bsub>M\<^esub> a \<in> carrier M" 
            by (simp add: A2 \<open>ring M\<close> ring.ring_simprules(5))
          have 2: "ord (x \<otimes>\<^bsub>M\<^esub> a) = (ord x) + (ord a)"
            using prime 0 A2 F1 F2 val_prod  
            by (metis monoid.simps(1) padic_integers.ring_def 
                padic_integers_axioms partial_object.select_convs(1)
                ring.simps(1) ord)
          have 3: "ord x \<ge>0" 
            using F1 padic_integers.ring_def padic_integers_axioms padic_val_def ord by fastforce
          have 4: "ord a \<ge>1" 
            using A1 F2 max_ideal_def by blast
          have "ord (x \<otimes>\<^bsub>M\<^esub> a) \<ge>1" 
            using "2" "3" "4" by linarith 
          then show ?thesis 
            using "1" max_ideal_def by blast
        qed
      qed
      show "\<And>a x. a \<in> m \<Longrightarrow> x \<in> carrier M \<Longrightarrow> m \<subseteq> m" 
        by blast
    qed
    show "\<And>a x. a \<in> m \<Longrightarrow> x \<in> carrier M \<Longrightarrow> a \<otimes>\<^bsub>M\<^esub> x \<in> m" 
      by (metis (mono_tags, lifting) \<open>\<And>x a. \<lbrakk>a \<in> m; x \<in> carrier M\<rbrakk> \<Longrightarrow> x \<otimes>\<^bsub>M\<^esub> a \<in> m\<close> 
          cring.cring_simprules(14) max_ideal_def mem_Collect_eq padic_int_is_cring
          padic_integers.ring_def padic_integers_axioms prime)
  qed





  