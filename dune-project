(lang dune 2.9)

(name lustrec)
(version 1.7)

(using dune_site 0.1)
(using menhir 2.0)
(generate_opam_files true)

(license LGPL)
(authors "Pierre-Loic Garoche <ploc@garoche.net>"
         "Xavier Thirioux <thirioux@enseeiht.fr>")
(maintainers "Pierre-Loic Garoche <ploc@garoche.net>")
(source (uri git+https://cavale.enseeiht.fr/git/lustrec#unstable))
(bug_reports https://cavale.enseeiht.fr/redmine/projects/lustrec/issues)
(homepage https://cavale.enseeiht.fr/redmine/projects/lustrec/)

(package
 (name lustrec)
 (sites
  (lib plugins)
  (lib verifiers)
  (lib include)
  (share testgen))
 (synopsis "A Lustre compiler toolset")
 (description
   "lustrec is structured around the modular compilation scheme proposed by \
    Biernacki, Colaço, Hamon, and Pouzet at LCTES'08.  It is an open source \
    lustre compiler that provides verification capabilities. It is currently \
    mainly used through the CocoSim platform, a Matlab toolbox to perform V&V \
    of Simulink models. Within CocoSim, the Lustre language is used as an \
    intermediate representation and relies mainly on lustrec to produce code \
    or verification artifacts.")
 (depends
    conf-gmp
    ocamlgraph
    menhir
    zarith
    yojson
    ppx_deriving_yojson
    ; cmdliner
    dune-site)
 (depopts z3))
