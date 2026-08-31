
from typing import Union
from .pyramid import Pyramid
from .nectron_openai import NectronOpenAI
from .pyramid_exceptions import NonCompilableNAR

import os
import openai
import pathlib


class Nectron:

    def __init__(self, api_key: Union[str, pathlib.WindowsPath, pathlib.PosixPath] = None, 
                 openrouter_model_id: str = 'openai/gpt-4o-mini'):

        self.generator = NectronOpenAI(model_id=openrouter_model_id)
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

    def reset(self):
        self.conversion_engine = Pyramid()
        self.correction_max = 3

    def generate_contracts(self, description: str):

        srs = ''
        nar_generation = self.generator.generate_nar(srs=description)

        nar = nar_generation[0]

        corrected_nar = nar
        contracts_seed = ''

        correction_amount = self.correction_max

        flag = True
        grammar_ok = True

        while flag and correction_amount > 0 and grammar_ok:
            try:
                self.conversion_engine.read_nar_from_generated(generated_nar=corrected_nar)
                contracts_seed = self.conversion_engine.compile()
            except NonCompilableNAR:
                nar_correction = self.generator.correct_syntax(nar_code=nar, srs=description)
                corrected_nar = nar_correction[0]
                grammar_ok = (corrected_nar.find('var:') != -1 and corrected_nar.find('action:') != -1
                                  and corrected_nar.find('return:') != -1)
                correction_amount -= 1
            else:
                flag = False
        

        if correction_amount > 0 and grammar_ok:

            return {
                "program_description": description,
                "acsl_contracts": f"{contracts_seed.get_imports()}\n{contracts_seed.string()}",
                "sequential_reasoning_strategy": srs,
                "nar_program": nar,
                "corrected_nar": corrected_nar,
                "times_corrected": self.correction_max - correction_amount
            }
        else:
            return {
                "program_description": description,
                "acsl_contracts": 'ScopeError: The provided prompt is outside the scope of contracts that NECTRON can generate.',
                "sequential_reasoning_strategy": srs,
                "nar_program": nar,
                "corrected_nar": corrected_nar,
                "times_corrected": self.correction_max - correction_amount
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