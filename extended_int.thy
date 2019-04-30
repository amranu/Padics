theory extended_int
imports Ordered_Abelian_Group Main Extended_OAG
begin

abbreviation int_group :: "int monoid" 
  where "int_group \<equiv> \<lparr>carrier = UNIV, mult = (+), one = 1\<rparr>"

abbreviation int_oag :: "int ordered_monoid" 
  where "int_oag \<equiv> \<lparr>carrier = UNIV, mult = (+), one = 1, le = (\<le>) \<rparr>"

abbreviation int_eoag :: "int option extended_ordered_monoid" where
  "int_eoag \<equiv> (extended int_oag)"



end