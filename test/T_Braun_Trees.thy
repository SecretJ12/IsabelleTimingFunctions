theory T_Braun_Trees
  imports "../src/TimingFunction" "afp/Priority_Queue_Braun"
begin

declare [[time_prefix = "T'_"]]


text \<open>Define timing function\<close>
define_time_fun insert
text \<open>del_min contains a let\<close>
text \<open>del_left contains a let\<close>
text \<open>sift_down contains a let through =:\<close>

text \<open>Proove equality\<close>
theorem "T'_insert a t = T_insert a t"
  by (induction t arbitrary: a) auto

end