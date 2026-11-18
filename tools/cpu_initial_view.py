#!/usr/bin/env python3
"""Instantiate the shared initial-register theorem in four existing source templates.

Engineering author: OpenAI Codex. Four existing proof bodies are rewritten;
no new design-specific theorem, premise, or exported declaration is introduced.
The universal proof lives in canonical CPUISARegView.v.
"""
import re
MODULES={'SteelTmplBoot','Srv32TmplBoot','NervRrGlue','A5RrGlue'}
DEFAULT_LEMMA='CPUISARegView.CPUISARegView.isa_view_initial_state'
def instantiate(text,module,lemma=DEFAULT_LEMMA,provider_import=None):
 if module not in MODULES:return text,[]
 # Qualified identifiers contain dots, so locate the proof delimiter rather
 # than using the first period as the end of the theorem statement.
 pattern=r'(?P<statement>\bLemma\s+isa_view_initial\b.*?)\s*Proof\.(?P<body>.*?)Qed\.'
 matches=list(re.finditer(pattern,text,re.S))
 if len(matches)!=1:raise ValueError(f'{module}: expected exactly one isa_view_initial proof, found {len(matches)}')
 match=matches[0];statement=match['statement'];assert statement.rstrip().endswith('.')
 initial={'SteelTmplBoot':'IV.initial','Srv32TmplBoot':'initial','NervRrGlue':'DF.initial','A5RrGlue':'initial'}[module]
 register='r' if module=='A5RrGlue' else 'i'
 replacement=statement+'\nProof. (* proof_author: OpenAI Codex; existing proof specialization. *) exact ('+lemma+' (getInstMem ('+initial+' image)) '+register+'). Qed.'
 result=text[:match.start()]+replacement+text[match.end():]
 if provider_import and 'Require Import '+provider_import+'.' not in result:result='Require Import '+provider_import+'.\n'+result
 return result,[{'theorem':'isa_view_initial','statement':statement,'generic_lemma':lemma,'proof_author':'OpenAI Codex','narrow_llm_existing_proof_rewrite':True}]
