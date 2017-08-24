# General information 
Author : Cherif Mohamed Sami

Internship period : May 22 - August 11, 2017

Team & laboratory : 2XS, CRIStAL (https://www.cristal.univ-lille.fr/)

Related Projects : 
- PIP protokernel (http://pip.univ-lille1.fr/)
- DEC language (https://github.com/ptorrx/DeepC4Pip)

# Abstract 
Formal proofs on program correctness are becoming longer and more com-
plex especially when dealing with critical software. Therefore, it is essential
to make these proofs as structured as possible, legible and amendable. The
purpose of this research is to study proofs specified in DEC, an intermedi-
ate deeply embedded language for the translation of the PIP protokernel,
a minimal OS kernel with provable isolation, to C. We specifically want to
check whether the strict structuring of DEC is reflected in invariant proofs
and to compare them to those in the shallow embedding in which PIP is
specified. To that end, three distinct invariants in the shallow embedding
were replicated in DEC. Their program functions were modelled modularly
and the invariant proofs were done correspondingly.

# Folders 
* developmentBS : preliminary work (previous version of DEC)
* developmentCS : invariant proofs can be found in files Hoare_getFstShadow.v, Hoare_writeVirtualInv.v and Hoare_initVAddrTable.v
* obselete - other files 
* report : see report_main.pdf for internship report




