# From System T to Continuation-Passing Style
In this project, I proved the type correctness of a translation from system T
to continuation-passing style (CPS).

The translation was first implemented [here][translation] in Coq, but the proof
was stuck and moved to [paper](cps/cps.pdf).

## Reference
- [From system F to typed assembly language][ftal]
- [The Penn Locally Nameless Metatheory Library][metalib]
- [Ott: Tool for the working semanticist][ott]
- [LNgen: Tool Support for Locally Nameless Representations][lngen]

[ott]:http://www.cl.cam.ac.uk/~pes20/ott/
[ftal]:http://dl.acm.org/citation.cfm?id=319345
[lngen]:https://github.com/plclub/lngen
[metalib]:https://github.com/plclub/metalib
[translation]:https://github.com/liyishuai/cps/blob/master/Translate.v
