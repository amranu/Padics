theory Ordered_Abelian_Group
imports  Main "~~/src/HOL/Algebra/Ring"  "~~/src/HOL/Algebra/Order"
begin

(*an ordered monoid record*)

record 'a ordered_monoid = "'a monoid" +
  le :: "['a, 'a] => bool" (infixl  "\<preceq>\<index>" 50)
 
(*a locale for an ordered monoid, that is: an instance of 'a ordered_monoid where the 
  carrier is a monoid, and the le relation is an order relation which respects the operation. *)

(*forgetful functor to get the underlying order of an ordered monoid*)
abbreviation
  underlying_order :: "('a, 'm) ordered_monoid_scheme \<Rightarrow> ('a, 'm) gorder_scheme"
  where "underlying_order G \<equiv> \<lparr>carrier = carrier G, eq = (=), gorder.le = le G
, \<dots> = (undefined:: 'm) \<rparr>"


locale has_order = 
  fixes G (structure)
  assumes an_order:
    "total_order (underlying_order G)"

lemma has_orderI:
  fixes G (structure)
  assumes "total_order (underlying_order G)"
  shows "has_order G"
  by (simp add: has_order.intro assms)

(*an ordered monoid is a monoid with a total order which respects the operation*)
locale ordered_monoid = 
  fixes G (structure)
  assumes a_monoid: 
    "monoid G"
  assumes an_order:
   "has_order G"
  assumes le_resp_mult:
    "\<lbrakk> a \<in> carrier G; b \<in> carrier G;le G a b;c \<in> carrier G \<rbrakk> \<Longrightarrow>((le G)(a\<otimes>\<^bsub>G\<^esub>c) (b\<otimes>\<^bsub>G\<^esub>c))"


locale ordered_abelian_group = ordered_monoid +
  assumes ab: 
    "comm_group  G"
  assumes one_in: 
    "\<one>\<^bsub>G\<^esub> \<in> carrier G"

lemma (in ordered_abelian_group) le_resp_mult1:
    "\<lbrakk> a \<in> carrier G; b \<in> carrier G;le G a b;c \<in> carrier G \<rbrakk> \<Longrightarrow>((le G) (c\<otimes>\<^bsub>G\<^esub>a)  (c\<otimes>\<^bsub>G\<^esub>b) )"
  using le_resp_mult by (simp add: ab comm_groupE(4))
  

lemma (in ordered_abelian_group) inv_0:
  assumes D:"x \<in> carrier G"
  assumes P: "\<one>\<^bsub>G\<^esub> \<preceq>\<^bsub>G\<^esub> x"
  shows "(inv x) \<preceq>\<^bsub>G\<^esub>  \<one>\<^bsub>G\<^esub>"
proof-
  from le_resp_mult and P have "((inv x) \<otimes>\<^bsub>G\<^esub> \<one>\<^bsub>G\<^esub>) \<preceq>\<^bsub>G\<^esub> ( (inv x) \<otimes>\<^bsub>G\<^esub> x)"
    by (meson D ab comm_groupE(2) comm_group_def group.inv_closed le_resp_mult1)  
  from this show  "(inv x) \<preceq>\<^bsub>G\<^esub> \<one>\<^bsub>G\<^esub>" 
    by (simp add: D a_monoid ab comm_group.axioms(2) group.l_inv)
qed


lemma (in ordered_abelian_group) inv_1:
  assumes D:"x \<in> carrier G"
  assumes P: "x  \<preceq>\<^bsub>G\<^esub> \<one>\<^bsub>G\<^esub>"
  shows "\<one>\<^bsub>G\<^esub> \<preceq>\<^bsub>G\<^esub>(inv x)"
proof-
  from le_resp_mult and P have " ( (inv x) \<otimes>\<^bsub>G\<^esub> x)\<preceq>\<^bsub>G\<^esub> ((inv x) \<otimes>\<^bsub>G\<^esub> \<one>\<^bsub>G\<^esub>)"
    by (meson D ab comm_groupE(2) comm_group_def group.inv_closed le_resp_mult1)  
  from this show " \<one>\<^bsub>G\<^esub>  \<preceq>\<^bsub>G\<^esub> (inv x)" 
    by (simp add: D a_monoid ab comm_group.axioms(2) group.l_inv)
qed


lemma (in ordered_abelian_group) inv_or:
  assumes D:"x \<in> carrier G"
  shows "\<one>\<^bsub>G\<^esub> \<preceq>\<^bsub>G\<^esub>(inv x) \<or>(inv x) \<preceq>\<^bsub>G\<^esub> \<one>\<^bsub>G\<^esub>"
  using inv_1 and inv_0 and  a_monoid an_order assms has_order.an_order monoid.one_closed total_order.total_order_total by fastforce


lemma (in ordered_abelian_group) no_idempotents0:
  fixes x
  assumes "x \<in> carrier G"
  assumes "inv x = x"
  shows "x = \<one>" using inv_or and has_order_def and assms(1)
  using an_order assms(2) inv_0 inv_1 one_in partial_order.le_antisym total_order.axioms(1) by fastforce

lemma (in ordered_abelian_group) no_idempotents1:
  fixes x
  assumes "x \<in> carrier G"
  assumes "x \<otimes> x = \<one>"
  shows "x = \<one>" 
  by (simp add: a_monoid assms(1) assms(2) monoid.inv_char ordered_abelian_group.no_idempotents0 ordered_abelian_group_axioms)

end