# BachelorThesisTimingFunctions
The goal of the bachelor thesis is to extend the Proof Assistant Isabelle by the automatic generation of runtime functions.

The file implements the following commands
```Isabelle
define_time_fun {NameOfFunction}
define_atime_fun {NameOfFunction}
```
The first command generates the running time function of the given function by the strict conversion schema. The second command generates the the asymptotic running time functions by neglecting all constants except of one.

All functions seen as trivial are converted as constant.
Trivial functions are constructors as well as manually defined functions. Functions can be marked as trivial with the following command
```Isabelle
define_time_trivial {NameOfFunction}
```
By default the following functions are marked as trivial
```Isabelle
(+)
(<)
Not
```

Only functions of the current theory can be converted into their timing functions.
Called functions get translated automatically if they are needed. They also need to be in the same theory.

Currently still in progress:
- Translating case patterns
- Translating lambdas
- Translating functions with custom termination scheme
