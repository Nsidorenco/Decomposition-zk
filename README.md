
# Installation requirements
- Why3 1.2.1
- Z3 4.8.6
- Alt-Ergo 2.3.0
- Easycrypt Git hash 30079829a1911b1f5905d31f84946ad825764971
  - It is recommended to run ```easycrypt why3config``` to set up the smt solvers.

# About the files
## Decomposition.eca
Defines the abstraction notion of a decompostion protocol and they security defintions.

## Commitment.eca
Defines security of commitments schemes (With no secret keys)

## SigmaProtocols.eca
Security definitions of Sigma-Protocols

## Folding
General lemmas about foldr

## ZKBooDecomposition
An implementation of the ZKBoo MPC protocol, following the notion of decomposition protocols from ```Decomposition.eca```.

## ZKBooTransformation
A valid instance of a Sigma-Protocol, based on the ZKBoo Sigma-Protocol, showing security based on any decomposition satifying the security definitions.
