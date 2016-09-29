# Coq scripts based on PFPL

The code in this subdirectory requires the [Metatheory](https://github.com/plclub/metalib) library to compile. When you use Coq with this library, you'll need to add the -R flag to rename it from `metalib` to `Metalib`.

For example, suppose `<METALIB>` is the path that I cloned the repo into.

Then my build files look like:

    _CoqProject

       -R <METALIB> Metalib
       Ch4.v


    Makefile
       METALIB=<METALIB>

       %.vo: %.v Makefile
         coqc -R $(METALIB) Metalib $*.v

You can also generate `Makefile` with the following command:

    % coq_makefile -f _CoqProject -o Makefile

To have this configuration work with Emacs, you should update Proof General to version ≥ 4.3pre.

If this is your first time to build, you might need to initialize the submodule via

    % git submodule update --init

and run `make` in folder `metalib`.
