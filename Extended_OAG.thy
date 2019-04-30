theory Extended_OAG
imports Main  "~~/src/HOL/Algebra/Ring"  "~~/src/HOL/Algebra/Valued_Fields/Ordered_Abelian_Group"
begin

record 'a  extended_ordered_monoid = "'a ordered_monoid" +
  infinity :: 'a ("\<infinity>\<index>")

(* constructor for build an EOM out of an OM*)


fun extended_mult :: "('a, 'm) ordered_monoid_scheme \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> 'a option"
  where 
"extended_mult G   None      None   = None"|
"extended_mult G  (Some a)   None   = None"|
"extended_mult G   None    (Some a) = None"|
"extended_mult G  (Some a) (Some b) = Some (a \<otimes>\<^bsub>G\<^esub>b)"

fun extended_order :: "('a, 'm) ordered_monoid_scheme \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> bool"
  where 
"extended_order G  None      None    = True"|
"extended_order G (Some a)   None    = True"|
"extended_order G  None     (Some a) = False"|
"extended_order G (Some a)  (Some b) = (a \<preceq>\<^bsub>G\<^esub> b)"


abbreviation
extended:: "('a, 'm) ordered_monoid_scheme \<Rightarrow> ('a option, 'm)  extended_ordered_monoid_scheme" where
"extended G \<equiv> \<lparr> carrier = (Some ` (carrier G)), mult = extended_mult G, one = Some (one G), le = extended_order G, infinity = None, \<dots> = (undefined :: 'm)\<rparr>   "


(*outlines the arithmetic of adding infinity to an ordered abelian group*) 

abbreviation
vals:: "('a, 'm)  extended_ordered_monoid_scheme \<Rightarrow> 'a set"
where "vals G \<equiv> carrier G \<union> {\<infinity>\<^bsub>G\<^esub>}"

locale extended_ordered_abelian_group = "ordered_abelian_group" + 
  assumes infinity_distinct: "\<infinity>\<^bsub>G\<^esub> \<notin> carrier G"
  assumes infinity_max1: " x \<in> carrier G \<Longrightarrow> le G x \<infinity>\<^bsub>G\<^esub>"
  assumes infinity_max2: " x \<in> carrier G \<Longrightarrow> \<not> le G \<infinity>\<^bsub>G\<^esub> x"
  assumes infinity_infinity: "le G \<infinity>\<^bsub>G\<^esub> \<infinity>\<^bsub>G\<^esub>"
  assumes infinity_plus_right: "x \<in> carrier G \<Longrightarrow> (x \<otimes>\<^bsub>G\<^esub> \<infinity>\<^bsub>G\<^esub>) =  \<infinity>\<^bsub>G\<^esub>"
  assumes infinity_plus_left: "x \<in> carrier G \<Longrightarrow> ( \<infinity>\<^bsub>G\<^esub> \<otimes>\<^bsub>G\<^esub> x) =  \<infinity>\<^bsub>G\<^esub>"
  assumes infinity_plus_infinity: "( \<infinity>\<^bsub>G\<^esub> \<otimes>\<^bsub>G\<^esub> \<infinity>\<^bsub>G\<^esub> ) =  \<infinity>\<^bsub>G\<^esub>"

lemma (in ordered_abelian_group) extended_is_eoag:
"extended_ordered_abelian_group (extended G)" 
proof
  show "\<And>x y. x \<in> carrier (extended G)   \<Longrightarrow> y \<in> carrier (extended G) \<Longrightarrow> x \<otimes>\<^bsub>extended G\<^esub> y \<in> carrier (extended G)" 
    using ab comm_groupE(1) by fastforce
  show "\<And>x y z.
       x \<in> carrier (extended G) \<Longrightarrow>
       y \<in> carrier (extended G) \<Longrightarrow>
       z \<in> carrier (extended G) \<Longrightarrow>
       x \<otimes>\<^bsub>extended G\<^esub> y \<otimes>\<^bsub>extended G\<^esub> z = x \<otimes>\<^bsub>extended G\<^esub> (y \<otimes>\<^bsub>extended G\<^esub> z)"
    using ab comm_groupE(3) by fastforce
  show "\<one>\<^bsub>extended G\<^esub> \<in> carrier (extended G)"
    by (simp add: one_in)
  show "\<And>x. x \<in> carrier (extended G) \<Longrightarrow> \<one>\<^bsub>extended G\<^esub> \<otimes>\<^bsub>extended G\<^esub> x = x"
    using a_monoid by auto
  show "\<And>x. x \<in> carrier (extended G) \<Longrightarrow> x \<otimes>\<^bsub>extended G\<^esub> \<one>\<^bsub>extended G\<^esub> = x"
    using a_monoid by auto
  show "\<And>x. x \<in> carrier (underlying_order (extended G)) \<Longrightarrow> x .=\<^bsub>underlying_order (extended G)\<^esub> x"
    by simp
  show " \<And>x y. x .=\<^bsub>underlying_order (extended G)\<^esub> y \<Longrightarrow>
           x \<in> carrier (underlying_order (extended G)) \<Longrightarrow>
           y \<in> carrier (underlying_order (extended G)) \<Longrightarrow> 
          y .=\<^bsub>underlying_order (extended G)\<^esub> x"
    by simp
  show "\<And>x y z.
       x .=\<^bsub>underlying_order (extended G)\<^esub> y \<Longrightarrow>
       y .=\<^bsub>underlying_order (extended G)\<^esub> z \<Longrightarrow>
       x \<in> carrier (underlying_order (extended G)) \<Longrightarrow>
       y \<in> carrier (underlying_order (extended G)) \<Longrightarrow> 
        z \<in> carrier (underlying_order (extended G)) \<Longrightarrow> 
      x .=\<^bsub>underlying_order (extended G)\<^esub> z"
    by simp
  show "\<And> x. x \<in> carrier (underlying_order (extended G)) \<Longrightarrow> x \<sqsubseteq>\<^bsub>underlying_order (extended G)\<^esub> x"
    using an_order has_order.an_order total_order.total_order_total by fastforce
  show "\<And>x y. x \<sqsubseteq>\<^bsub>underlying_order (extended G)\<^esub> y \<Longrightarrow>
           y \<sqsubseteq>\<^bsub>underlying_order (extended G)\<^esub> x \<Longrightarrow>
           x \<in> carrier (underlying_order (extended G)) \<Longrightarrow>
           y \<in> carrier (underlying_order (extended G)) \<Longrightarrow> 
           x .=\<^bsub>underlying_order (extended G)\<^esub> y"
    using an_order has_order.an_order 
      partial_order.le_antisym total_order.axioms(1) by fastforce
  show " \<And>x y z.
     x \<sqsubseteq>\<^bsub>underlying_order (extended G)\<^esub> y \<Longrightarrow>
     y \<sqsubseteq>\<^bsub>underlying_order (extended G)\<^esub> z \<Longrightarrow>
     x \<in> carrier (underlying_order (extended G)) \<Longrightarrow>
     y \<in> carrier (underlying_order (extended G)) \<Longrightarrow> 
     z \<in> carrier (underlying_order (extended G)) \<Longrightarrow>
     x \<sqsubseteq>\<^bsub>underlying_order (extended G)\<^esub> z"
  proof-
    fix x y z
    assume 0: "x \<sqsubseteq>\<^bsub>underlying_order (extended G)\<^esub> y" 
    assume 1: "y \<sqsubseteq>\<^bsub>underlying_order (extended G)\<^esub> z"
    assume 2: "x \<in> carrier (underlying_order (extended G))"
    assume 3: "y \<in> carrier (underlying_order (extended G))"
    assume 4: "z \<in> carrier (underlying_order (extended G))"
    show "x \<sqsubseteq>\<^bsub>underlying_order (extended G)\<^esub> z" 
    proof-
      obtain a where "x = Some a" 
        using "2" by auto
      obtain b where "y = Some b" 
        using "3" by auto
      obtain c where "z = Some c" 
        using "4" by auto
      have 5: "a \<sqsubseteq>\<^bsub>underlying_order (G)\<^esub>b" 
        using "0" \<open>x = Some a\<close> \<open>y = Some b\<close> by auto
      have 6: "b \<sqsubseteq>\<^bsub>underlying_order (G)\<^esub>c" 
        using "1" \<open>y = Some b\<close> \<open>z = Some c\<close> by auto 
      have 7: "a \<sqsubseteq>\<^bsub>underlying_order (G)\<^esub>c" using 5 6 an_order 
        by (smt "2" "3" "4" \<open>x = Some a\<close> \<open>y = Some b\<close> \<open>z = Some c\<close> has_order.an_order
            image_iff option.sel partial_object.select_convs(1) partial_order_def 
            total_order.axioms(1) weak_partial_order.le_trans)
      then show ?thesis 
        by (simp add: \<open>x = Some a\<close> \<open>z = Some c\<close>)
    qed
  qed
  show "\<And>x y z w.
       x .=\<^bsub>underlying_order (extended G)\<^esub> y \<Longrightarrow>
       z .=\<^bsub>underlying_order (extended G)\<^esub> w \<Longrightarrow>
       x \<in> carrier (underlying_order (extended G)) \<Longrightarrow>
       y \<in> carrier (underlying_order (extended G)) \<Longrightarrow>
       z \<in> carrier (underlying_order (extended G)) \<Longrightarrow>
       w \<in> carrier (underlying_order (extended G)) \<Longrightarrow> 
      (x \<sqsubseteq>\<^bsub>underlying_order (extended G)\<^esub> z) = (y \<sqsubseteq>\<^bsub>underlying_order (extended G)\<^esub> w)"
    by simp
  show "(.=\<^bsub>underlying_order (extended G)\<^esub>) = (=)" by simp
  show " \<And>x y. x \<in> carrier (underlying_order (extended G)) \<Longrightarrow>
           y \<in> carrier (underlying_order (extended G)) \<Longrightarrow> 
          x \<sqsubseteq>\<^bsub>underlying_order (extended G)\<^esub> y \<or> y \<sqsubseteq>\<^bsub>underlying_order (extended G)\<^esub> x"
    by (smt None_notin_image_Some an_order extended_order.elims(3)
        gorder.select_convs(1) has_order.an_order image_iff option.inject
        ordered_monoid.simps(1) partial_object.select_convs(1) total_order.total_order_total)
  show " \<And>a b c.
       a \<in> carrier (extended G) \<Longrightarrow>
       b \<in> carrier (extended G) \<Longrightarrow> 
       a \<preceq>\<^bsub>extended G\<^esub> b \<Longrightarrow>
       c \<in> carrier (extended G) \<Longrightarrow>
       a \<otimes>\<^bsub>extended G\<^esub> c \<preceq>\<^bsub>extended G\<^esub> b \<otimes>\<^bsub>extended G\<^esub> c" 
    using le_resp_mult by auto
  show "\<And>x y. x \<in> carrier (extended G) \<Longrightarrow> 
        y \<in> carrier (extended G) \<Longrightarrow> 
        x \<otimes>\<^bsub>extended G\<^esub> y = y \<otimes>\<^bsub>extended G\<^esub> x"
    using ab comm_groupE(4) by fastforce
  show "carrier (extended G) \<subseteq> Units (extended G)"
    proof fix x assume "x \<in> carrier (extended G)"
      obtain a where "x = Some a" 
        using \<open>x \<in> carrier (extended G)\<close> by auto
      obtain b where "b = inv a" 
        by simp
      have "Some b \<otimes>\<^bsub>extended G\<^esub> x = \<one>\<^bsub>extended G\<^esub>"  
        using \<open>b = inv a\<close> \<open>x = Some a\<close> \<open>x \<in> carrier (extended G)\<close> 
          ab comm_group.axioms(2) group.l_inv by fastforce
      then show "x \<in> Units (extended G)" using Units_def 
        by (smt \<open>\<And>y x. \<lbrakk>x \<in> carrier (extended G); y \<in> carrier (extended G)\<rbrakk> 
              \<Longrightarrow> x \<otimes>\<^bsub>extended G\<^esub> y = y \<otimes>\<^bsub>extended G\<^esub> x\<close> \<open>b = inv a\<close> 
            \<open>x = Some a\<close> \<open>x \<in> carrier (extended G)\<close> ab comm_group.axioms(2)
            group.inv_closed in_these_eq mem_Collect_eq partial_object.select_convs(1)
            these_image_Some_eq)
    qed
  show "\<infinity>\<^bsub>extended G\<^esub> \<notin> carrier (extended G)" 
    by simp
  show "\<And>x. x \<in> carrier (extended G) \<Longrightarrow> x \<preceq>\<^bsub>extended G\<^esub> \<infinity>\<^bsub>extended G\<^esub>"
    by auto
  show "\<And>x. x \<in> carrier (extended G) \<Longrightarrow> \<not> \<infinity>\<^bsub>extended G\<^esub> \<preceq>\<^bsub>extended G\<^esub> x" 
    by auto
  show "\<infinity>\<^bsub>extended G\<^esub> \<preceq>\<^bsub>extended G\<^esub> \<infinity>\<^bsub>extended G\<^esub>" sledgehammer
    by simp
  show "\<And>x. x \<in> carrier (extended G) \<Longrightarrow> x \<otimes>\<^bsub>extended G\<^esub> \<infinity>\<^bsub>extended G\<^esub> = \<infinity>\<^bsub>extended G\<^esub>" 
    by auto
  show "\<And>x. x \<in> carrier (extended G) \<Longrightarrow> \<infinity>\<^bsub>extended G\<^esub> \<otimes>\<^bsub>extended G\<^esub> x = \<infinity>\<^bsub>extended G\<^esub>" 
    by auto
  show "\<infinity>\<^bsub>extended G\<^esub> \<otimes>\<^bsub>extended G\<^esub> \<infinity>\<^bsub>extended G\<^esub> = \<infinity>\<^bsub>extended G\<^esub>" 
    by simp
qed

lemma (in extended_ordered_abelian_group) add_infinityR:
  assumes "x \<in> carrier G \<or> x = \<infinity>\<^bsub>G\<^esub>"
  shows " (x \<otimes>\<^bsub>G\<^esub> \<infinity>\<^bsub>G\<^esub>) =  \<infinity>\<^bsub>G\<^esub>"
proof (cases  "x = \<infinity>\<^bsub>G\<^esub>")
  case True
  then show " (x \<otimes>\<^bsub>G\<^esub> \<infinity>\<^bsub>G\<^esub>) =  \<infinity>\<^bsub>G\<^esub>" using infinity_plus_infinity by auto
next
  case False
  then show " (x \<otimes>\<^bsub>G\<^esub> \<infinity>\<^bsub>G\<^esub>) =  \<infinity>\<^bsub>G\<^esub>" using infinity_plus_right using assms by blast
qed

lemma (in extended_ordered_abelian_group) add_infinityL:
  assumes "x \<in> carrier G \<or> x = \<infinity>\<^bsub>G\<^esub>"
  shows " ( \<infinity>\<^bsub>G\<^esub> \<otimes>\<^bsub>G\<^esub> x) =  \<infinity>\<^bsub>G\<^esub>"
proof (cases  "x = \<infinity>\<^bsub>G\<^esub>")
  case True
  then show "  \<infinity>\<^bsub>G\<^esub> \<otimes>\<^bsub>G\<^esub> x =  \<infinity>\<^bsub>G\<^esub>" using infinity_plus_infinity by auto
  next
  case False
  then show " \<infinity>\<^bsub>G\<^esub> \<otimes>\<^bsub>G\<^esub> x =  \<infinity>\<^bsub>G\<^esub>" using infinity_plus_left using assms by blast
  qed

lemma (in extended_ordered_abelian_group) add_infinityOR:
  assumes "x \<in> vals G"
  assumes "y \<in> vals G"
  assumes "x = \<infinity> \<or> y = \<infinity>"
  shows " (x \<otimes>\<^bsub>G\<^esub> y) =  \<infinity>\<^bsub>G\<^esub>"
  using add_infinityL add_infinityR assms(1) assms(2) assms(3) by blast

(* The minimum function. Maybe makes more sense to add this elsewhere? We'll see.*)

abbreviation Min :: "[ ('a, 'm) extended_ordered_monoid_scheme, 'a, 'a] \<Rightarrow> 'a " ("Min\<index>")
  where "Min\<^bsub>G\<^esub>  x y \<equiv> (if (le G x y) then x else y)"


lemma (in extended_ordered_abelian_group) no_idempotents:
  assumes "x \<in> vals G"
  assumes "x \<otimes> x = \<one>"
  shows "x = \<one>" 
  using add_infinityOR assms(1) assms(2) no_idempotents1 by auto

(*forgetful functor to get the underlying order of an extended ordered monoid*)
abbreviation
  e_underlying_order :: "('a, 'm) extended_ordered_monoid_scheme \<Rightarrow> ('a, 'm) gorder_scheme" ("Order\<index>")
  where "e_underlying_order G \<equiv> \<lparr>carrier = carrier G \<union> {\<infinity>\<^bsub>G\<^esub>}, eq = (=), gorder.le = le G
, \<dots> = (undefined:: 'm) \<rparr>"

lemma  (in extended_ordered_abelian_group) e_is_equals:
"eq (e_underlying_order G) = (=)" by auto

lemma (in extended_ordered_abelian_group) EOAG_is_equivalence:
  "equivalence (e_underlying_order G)" 
  using e_is_equals  by (simp add: equivalence_def)


lemma (in extended_ordered_abelian_group) EOAG_is_pOrdered0:
  "weak_partial_order Order\<^bsub>G\<^esub>"
proof
  show "\<And>x. x \<in> carrier Order\<^bsub>G\<^esub>  \<Longrightarrow> x \<sqsubseteq>\<^bsub>Order\<^bsub>G\<^esub> \<^esub> x"
    using an_order has_order.an_order infinity_infinity 
      total_order.total_order_total by fastforce
  show "\<And>x y. x \<sqsubseteq>\<^bsub>Order\<^bsub>G\<^esub> \<^esub> y \<Longrightarrow>
           y \<sqsubseteq>\<^bsub>Order\<^bsub>G\<^esub>\<^esub> x \<Longrightarrow>
           x \<in> carrier Order\<^bsub>G\<^esub> \<Longrightarrow>
           y \<in> carrier Order\<^bsub>G\<^esub> \<Longrightarrow> x .=\<^bsub>Order\<^bsub>G\<^esub>\<^esub> y"
  proof-
    fix x y
    assume 0:"x \<sqsubseteq>\<^bsub>Order\<^bsub>G\<^esub> \<^esub> y"
    assume 1:"y \<sqsubseteq>\<^bsub>Order\<^bsub>G\<^esub>\<^esub> x"
    assume 2:"x \<in> carrier Order\<^bsub>G\<^esub>"
    assume 3:"y \<in> carrier Order\<^bsub>G\<^esub>"
    then show "x .=\<^bsub>Order\<^bsub>G\<^esub>\<^esub> y"    
    proof(cases "x = infinity G")
      case True
      then show ?thesis 
        using "0" "3" infinity_max2 by auto
      next
        case False
        then have "y \<noteq> infinity G" 
          using "1" "2" infinity_max2 by auto
        then have "x \<in>carrier G" and "y \<in> carrier G" 
          using "2" False apply auto[1] using "3" \<open>y \<noteq> \<infinity>\<close> by auto
        then have "x = y"  
          using an_order has_order.an_order total_order.total_order_total
            e_is_equals  "0" "1" partial_order.le_antisym total_order.axioms(1) by fastforce
        then show ?thesis using e_is_equals  by simp
      qed
    qed
  show "\<And>x y z.
       x \<sqsubseteq>\<^bsub>Order\<^bsub>G\<^esub> \<^esub> y \<Longrightarrow>
       y \<sqsubseteq>\<^bsub>Order\<^bsub>G\<^esub> \<^esub> z \<Longrightarrow>
       x \<in> carrier Order\<^bsub>G\<^esub> \<Longrightarrow>
       y \<in> carrier Order\<^bsub>G\<^esub> \<Longrightarrow>
       z \<in> carrier Order\<^bsub>G\<^esub> \<Longrightarrow> x \<sqsubseteq>\<^bsub>Order\<^bsub>G\<^esub> \<^esub> z"
    by (smt Un_insert_right an_order gorder.simps(1) has_order.an_order
        infinity_max1 infinity_max2 insert_iff partial_object.select_convs(1) 
        partial_order_def sup_bot.comm_neutral total_order.axioms(1) 
        weak_partial_order.le_trans)
  show "\<And>x y z w.
       x .=\<^bsub>Order\<^bsub>G\<^esub>\<^esub> y \<Longrightarrow>
       z .=\<^bsub>Order\<^bsub>G\<^esub>\<^esub> w \<Longrightarrow>
       x \<in> carrier Order\<^bsub>G\<^esub> \<Longrightarrow>
       y \<in> carrier Order\<^bsub>G\<^esub> \<Longrightarrow>
       z \<in> carrier Order\<^bsub>G\<^esub> \<Longrightarrow>
       w \<in> carrier Order\<^bsub>G\<^esub> \<Longrightarrow>
       (x \<sqsubseteq>\<^bsub>Order\<^bsub>G\<^esub>\<^esub> z) = (y \<sqsubseteq>\<^bsub>Order\<^bsub>G\<^esub>\<^esub> w)"
    by simp
  show "\<And>x. x \<in> carrier Order\<^bsub>G\<^esub>  \<Longrightarrow> x .=\<^bsub>Order \<^bsub>G\<^esub> \<^esub> x" 
    by simp
  show "\<And>x y. x .=\<^bsub>Order\<^bsub>G\<^esub> \<^esub> y \<Longrightarrow>
           x \<in> carrier Order\<^bsub>G\<^esub>  \<Longrightarrow>
           y \<in> carrier Order\<^bsub>G\<^esub>  \<Longrightarrow> y .=\<^bsub>Order\<^bsub>G\<^esub> \<^esub> x"
    by simp
  show "\<And>x y z.
       x .=\<^bsub>Order\<^bsub>G\<^esub>\<^esub> y \<Longrightarrow>
       y .=\<^bsub>Order\<^bsub>G\<^esub>\<^esub> z \<Longrightarrow>
       x \<in> carrier Order\<^bsub>G\<^esub> \<Longrightarrow>
       y \<in> carrier Order\<^bsub>G\<^esub> \<Longrightarrow>
       z \<in> carrier Order\<^bsub>G\<^esub> \<Longrightarrow> x .=\<^bsub>Order\<^bsub>G\<^esub>\<^esub> z"
    by simp
qed


lemma (in extended_ordered_abelian_group) EOAG_is_pOrdered:
  "partial_order (e_underlying_order G)"
  using EOAG_is_pOrdered0  e_is_equals partial_order.intro partial_order_axioms.intro by blast


lemma (in extended_ordered_abelian_group) EOAG_is_ordered0:
 " \<lbrakk>x \<in> carrier (e_underlying_order G); y \<in> carrier (e_underlying_order G)\<rbrakk>
           \<Longrightarrow> x \<sqsubseteq>\<^bsub>e_underlying_order G\<^esub> y \<or> y \<sqsubseteq>\<^bsub>e_underlying_order G\<^esub> x"
  using  EOAG_is_pOrdered 
  by (metis EOAG_is_equivalence EOAG_is_pOrdered0
      Un_insert_right an_order equivalence.refl
      gorder.select_convs(1) has_order.an_order 
      infinity_max1 insertE partial_object.select_convs(1) 
      sup_bot.right_neutral total_order.total_order_total
      weak_partial_order.weak_refl)

lemma (in extended_ordered_abelian_group) EOAG_is_ordered:
  "total_order (e_underlying_order G)"
using EOAG_is_ordered0 EOAG_is_pOrdered partial_order.total_orderI by blast

lemma (in extended_ordered_abelian_group) refl:
  assumes "x \<in> carrier G \<union> {\<infinity>}"
  shows "x \<preceq>\<^bsub>G\<^esub> x"
  using assms EOAG_is_ordered0 by auto 

lemma (in extended_ordered_abelian_group) trans:
  assumes "x \<in> carrier G \<union> {\<infinity>}"
  assumes "y \<in> carrier G \<union> {\<infinity>}"
  assumes "z \<in> carrier G \<union> {\<infinity>}"
  assumes "x \<preceq>\<^bsub>G\<^esub> y"
  assumes "y \<preceq>\<^bsub>G\<^esub> z"
shows "x \<preceq>\<^bsub>G\<^esub> z" 
  using assms(1) assms(2) assms(3) assms(4) assms(5) 
      extended_ordered_abelian_group.EOAG_is_pOrdered
      extended_ordered_abelian_group_axioms 
      gorder.select_convs(1) partial_object.select_convs(1)
      partial_order_def weak_partial_order.le_trans
       by smt 

lemma (in extended_ordered_abelian_group) anti_symm:
  assumes "x \<in> carrier G \<union> {\<infinity>}"
  assumes "y \<in> carrier G \<union> {\<infinity>}"
  assumes "x \<preceq>\<^bsub>G\<^esub> y"
  assumes "y \<preceq>\<^bsub>G\<^esub> x"
  shows "x = y" 
 using assms(1) assms(2) assms(3) 
    assms(4) extended_ordered_abelian_group.EOAG_is_pOrdered
    extended_ordered_abelian_group_axioms
    partial_order.le_antisym by fastforce


lemma (in extended_ordered_abelian_group) E_le_resp_mult:
assumes   "a \<in> carrier G \<union> {\<infinity>}"
assumes "b \<in> carrier G \<union> {\<infinity>}" 
assumes "le G a b"
assumes "c \<in> carrier G\<union> {\<infinity>}" 
shows   "((le G)(a\<otimes>\<^bsub>G\<^esub>c) (b\<otimes>\<^bsub>G\<^esub>c))"
proof (cases "a = \<infinity> \<or> b = \<infinity>")
  case True
  then show "((le G)(a\<otimes>\<^bsub>G\<^esub>c) (b\<otimes>\<^bsub>G\<^esub>c))"
  proof (cases "a = \<infinity>")
    case True
    then have "b = \<infinity>" 
    using assms(2) assms(3) infinity_max2 by auto
    then show "((le G)(a\<otimes>\<^bsub>G\<^esub>c) (b\<otimes>\<^bsub>G\<^esub>c))"
    using True assms(3) assms(4) infinity_plus_infinity infinity_plus_left by auto
  next
    case False
    then have "b = \<infinity>"
    using True by auto
    from this show "((le G)(a\<otimes>\<^bsub>G\<^esub>c) (b\<otimes>\<^bsub>G\<^esub>c))"
      using a_monoid assms(1) assms(4) infinity_infinity
        infinity_max1 infinity_plus_infinity infinity_plus_left
        infinity_plus_right monoid.m_closed by force
  qed
next 
  case False
  then show "((le G)(a\<otimes>\<^bsub>G\<^esub>c) (b\<otimes>\<^bsub>G\<^esub>c))" 
    using assms(1) assms(2) assms(3) assms(4)
      infinity_infinity infinity_plus_right le_resp_mult by auto
qed

lemma (in extended_ordered_abelian_group) mult_closed:
assumes   "a \<in> carrier G \<union> {\<infinity>}"
assumes "b \<in> carrier G \<union> {\<infinity>}" 
shows "a \<otimes>\<^bsub>G\<^esub> b \<in> carrier G \<union> {\<infinity>\<^bsub>G\<^esub>}"
proof
  assume "a \<otimes> b \<notin> {\<infinity>}"
  show "a \<otimes> b \<in> carrier G " 
    using \<open>a \<otimes> b \<notin> {\<infinity>}\<close> a_monoid assms(1) assms(2) infinity_plus_infinity
      infinity_plus_left infinity_plus_right monoid.m_closed by force
qed

lemma (in extended_ordered_abelian_group) E_le_resp_mult2:
assumes "a \<in> carrier G \<union> {\<infinity>}"
assumes "b \<in> carrier G \<union> {\<infinity>}" 
assumes "c \<in> carrier G \<union> {\<infinity>}"
assumes "d \<in> carrier G \<union> {\<infinity>}" 
assumes "le G a b"
assumes "le G c d"
shows  "((le G)(a\<otimes>\<^bsub>G\<^esub>c) (b\<otimes>\<^bsub>G\<^esub>d))"
proof-
  from E_le_resp_mult have 1: "((le G)(a\<otimes>\<^bsub>G\<^esub>c) (b\<otimes>\<^bsub>G\<^esub>c))" 
  using assms(1) assms(2) assms(3) assms(5) by blast
  from E_le_resp_mult have 2: "((le G)(b\<otimes>\<^bsub>G\<^esub>c) (b\<otimes>\<^bsub>G\<^esub>d))" 
  by (metis (no_types, lifting) Un_insert_right assms(2) assms(3) assms(4) assms(6) extended_ordered_abelian_group.infinity_max2 extended_ordered_abelian_group_axioms infinity_max1 infinity_plus_left infinity_plus_right insertE le_resp_mult1 sup_bot.right_neutral)
  from 1 and 2 show "((le G)(a\<otimes>\<^bsub>G\<^esub>c) (b\<otimes>\<^bsub>G\<^esub>d))" 
  by (metis (no_types, lifting) assms(1) assms(2) assms(3) assms(4) extended_ordered_abelian_group.EOAG_is_pOrdered extended_ordered_abelian_group_axioms gorder.simps(1) mult_closed partial_object.select_convs(1) partial_order_def weak_partial_order.le_trans)
qed

lemma (in extended_ordered_abelian_group) chain:
assumes "a \<in> carrier G \<union> {\<infinity>}"
assumes "b \<in> carrier G \<union> {\<infinity>}" 
assumes "c \<in> carrier G \<union> {\<infinity>}"
assumes "le G a b"
assumes "le G b c"
assumes "a \<noteq> b"
shows "a \<noteq> c"
proof
  assume "a = c"
  then have "a = b"
  using assms(1) assms(2) assms(4) assms(5) extended_ordered_abelian_group.EOAG_is_pOrdered extended_ordered_abelian_group_axioms partial_order.le_antisym by fastforce
  from this and assms(6) show False by auto
qed
end
