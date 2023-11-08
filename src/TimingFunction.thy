theory TimingFunction
  imports Main
  keywords "define_time_fun" :: thy_decl
    and    "define_atime_fun" :: thy_decl
    and    "define_time_trivial" :: thy_decl
begin

ML_file TrivialFuns.ML
ML_file TimingFunction.ML

define_time_trivial "(+)"
define_time_trivial "(<)"
define_time_trivial "Not"

end