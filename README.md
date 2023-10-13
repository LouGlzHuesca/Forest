# Forest

[Forest.v](Forest.v) implements the basic features of RNmatrix [1]. Building upon this, [S4.v](S4.v) implements the RNmatrix described in [2] for the modal logic S4.

To run, open the folder inside some terminal.  In the terminal, first run:

```bash
coqc Forest.v
```

Then:

```bash
coqc S4.v
```

Please look inside [S4.v](S4.v) to learn about how to run with different examples.

# References

1. CONIGLIO, Marcelo E.; TOLEDO, Guilherme V. Two Decision Procedures for da Costa’s C n Logics Based on Restricted Nmatrix Semantics. Studia Logica, v. 110, n. 3, p. 601-642, 2022.
2. GRÄTZ, Lukas. Truth tables for modal logics T and S4, by using three-valued non-deterministic level semantics. Journal of Logic and Computation, v. 32, n. 1, p. 129-157, 2022.
