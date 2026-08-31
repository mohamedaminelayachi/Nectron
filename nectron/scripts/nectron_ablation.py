from typing import Union
from .pyramid import Pyramid
from .nectron_openai import NectronOpenAI
from .pyramid_exceptions import NonCompilableNAR

import os
import openai
import pathlib

class NectronForAblation:

    def __init__(self, api_key: Union[str, pathlib.WindowsPath, pathlib.PosixPath] = None, 
                 openrouter_model_id: str = 'openai/gpt-4o-mini', explanation: bool = True):


        self.generator = NectronOpenAI(model_id=openrouter_model_id, 
                                        explanation=explanation)
        try:
            if api_key is None or len(api_key) == 0:
                raise ConnectionError
            elif os.path.exists(api_key):
                self.generator.InitClient(api_key_path=api_key)
            else:
                self.generator.InitClient(api_key=api_key)
        except openai.AuthenticationError:
            raise openai.AuthenticationError

        self.reset()
        self.explanation = explanation

    def reset(self):
        self.conversion_engine = Pyramid()
        self.correction_max = 3
        self.rri_max = 3
        self.tots_max = 3

    def generate_contracts(self, description: str, rri: int, num_tots: int):
        
        assert rri <= self.rri_max, f"Reflective Reasoning Intensity should be less than {self.rri_max}."
        assert num_tots <= self.tots_max, f"The allowed number of Tree-of-Thoughts should be less than {self.tots_max}."
   
        srs_generation = self.generator.generate_srs(program_description=description)

        srs = srs_generation[0]
        srs_exp = srs_generation[1]

        nar_generation = self.generator.generate_nar(srs=srs)

        nar = nar_generation[0]
        nar_exp = nar_generation[1]

        corrected_nar = nar
        correction_exp = ''
        contracts_seed = ''

        correction_amount = self.correction_max

        flag = True
        grammar_ok = True
        while flag and correction_amount > 0 and grammar_ok:
            try:
                self.conversion_engine.read_nar_from_generated(generated_nar=corrected_nar)
                contracts_seed = self.conversion_engine.compile()
            except NonCompilableNAR:
                nar_correction = self.generator.correct_syntax(nar_code=nar, srs=srs)
                corrected_nar = nar_correction[0]
                correction_exp = nar_correction[1]
                grammar_ok = (corrected_nar.find('var:') != -1 and corrected_nar.find('action:') != -1
                                  and corrected_nar.find('return:') != -1)
                correction_amount -= 1
            else:
                flag = False
        
        if correction_amount > 0 and grammar_ok:

            plan = self.generator.generate_ToT(program_description=description, num_app=num_tots)
            
            if rri == 0:
                simple_refinement = self.generator.refine_contracts(contracts=contracts_seed.string(),
                                                                            verification_plan=plan)
            elif rri > 0:
                simple_refinement = self.generator.refine_contracts(contracts=contracts_seed.string(),
                                                                            verification_plan=plan)
                
                reflective_refinement = self.generator.reflective_reasoning(contracts=contracts_seed.string(),
                                                                                verification_plan=plan,
                                                                                batch_samples=rri)
                # if len(reflective_refinement) == 3:
                #     suggestions = reflective_refinement[2]
                # else:
                #     suggestions = []

            suggestions = []

            simple_refined_contracts = f"{contracts_seed.get_imports()}\n/*@\n" + simple_refinement[0].replace('/*@', '').replace('*/', '').strip('\n') + '\n*/'
            reflective_refined_contracts = f"{contracts_seed.get_imports()}\n/*@\n" + reflective_refinement[0].replace('/*@', '').replace('*/', '').strip('\n') + '\n*/'

            refinement_exp = reflective_refinement[1]
            
            sphinx = self.generator.sphinx(contracts=contracts_seed.string(), verification_plan=plan)

            revised_contracts = f"{contracts_seed.get_imports()}\n/*@\n" + sphinx[0].replace('/*@', '').replace('*/', '').strip('\n') + '\n*/'
            revision_exp = sphinx[1]

            return {
                "program_description": description,
                "acsl_contracts": revised_contracts,
                "sequential_reasoning_strategy": srs,
                "nar_program": nar,
                "corrected_nar": corrected_nar,
                "contracts_seeds": f"{contracts_seed.get_imports()}\n{contracts_seed.string()}",
                "verification_plan": plan,
                "times_corrected": self.correction_max - correction_amount,
                "srs_explanation": srs_exp,
                "nar_generation_explanation": nar_exp,
                "nar_correction_explanation": correction_exp,
                "refinement_explanation": refinement_exp,
                "revision_explanation": revision_exp,
                "suggestions": suggestions,
                "ablations": {
                    "seeds": f"{contracts_seed.get_imports()}\n{contracts_seed.string()}",
                    "reflective_refinement": reflective_refined_contracts,
                    "simple_refinement": simple_refined_contracts,
                    "augmented_refinement": revised_contracts
                }
            }
        else:
            return {
                "program_description": description,
                "acsl_contracts": 'ScopeError: The provided prompt is outside the scope of contracts that NECTRON can generate.',
                "sequential_reasoning_strategy": srs,
                "nar_program": nar,
                "corrected_nar": corrected_nar,
                "contracts_seeds": 'ScopeError: The provided prompt is outside the scope of contracts that NECTRON can generate.',
                "verification_plan": '',
                "times_corrected": self.correction_max - correction_amount,
                "srs_explanation": srs_exp,
                "nar_generation_explanation": nar_exp,
                "nar_correction_explanation": correction_exp,
                "refinement_explanation": '',
                "revision_explanation": '',
                "suggestions": [],
                "ablations": {
                    "seeds": '//ScopeError: The provided prompt is outside the scope of contracts that NECTRON can generate.',
                    "reflective_refinement": '//ScopeError: The provided prompt is outside the scope of contracts that NECTRON can generate.',
                    "simple_refinement": '//ScopeError: The provided prompt is outside the scope of contracts that NECTRON can generate.',
                    "augmented_refinement": '//ScopeError: The provided prompt is outside the scope of contracts that NECTRON can generate.'
                }
            }
        
    def reconstruct_program(self, corrupted_code: str, specification: str):
        """
        This method is used to prompt the model to reconstruct and restore the non-corrupted program using the specification.
        :param corrupt_code: The corrupt code
        :param specification: the ACSL specification to be used to eliminate the semantic noise.
        :return:
        """
        return self.generator.reconstruct_program(corrupted_code=corrupted_code, specification=specification)
    
    def generate_zero_shot(self, description: str):
        return self.generator.generate_zero_shot(description=description)