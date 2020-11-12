HotStuff specifications in TLA+ for safety model checking   
Newest version - HotStuffAlpha.tla   
Apalache version(deprecated, for some reason takes too much time in Apalache) - ApalacheHotStuffCutted.tla   
Base version(deprecated, issue with leader stages) - HotStuffSketch.tla   


Example of cfg file - HotStuffAlpha.cfg. To configure leader function you can add line like this [v \in 0..MaxView |-> v % N] (for example) right into TLA+ specification 

