theory TimingFunction
  imports Main
  keywords "define_time_fun" :: thy_decl
    and    "define_time_0" :: thy_decl
begin

ML_file ZeroFuns.ML
ML_file TimingFunction.ML

define_time_0 "(+)"
define_time_0 "(<)"
define_time_0 "Not"
define_time_0 "Num.numeral_class.numeral"
define_time_0 "(=)"

end