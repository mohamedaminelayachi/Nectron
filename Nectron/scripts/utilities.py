import json
import os
from dataclasses import dataclass
from typing import Union


@dataclass
class NectronState:
    program_description: Union[str, None]
    acsl_contracts: Union[str, None]
    seeds: Union[str, None]
    srs: Union[str, None]
    nar_representation: Union[str, None]
    srs_exp: Union[str, None]
    nar_gen_exp: Union[str, None]
    refinement_exp: Union[str, None]
    suggestions: Union[list, None]

    def to_dict(self, unroll_suggestions: bool=False):
        if unroll_suggestions:
            data = {
                "program_description": self.program_description,
                "acsl_contracts": self.acsl_contracts,
                "sequential_reasoning_strategy": self.srs,
                "seeds": self.seeds,
                "nar_representation": self.nar_representation,
                "srs_explanation": self.srs_exp,
                "nar_generation_explanation": self.nar_gen_exp,
                "refinement_explanation": self.refinement_exp,
            }

            for index, s in enumerate(self.suggestions):
                data[f'suggestion_{index+1}'] = s

            return data
        else:
            return {
                "program_description": self.program_description,
                "acsl_contracts": self.acsl_contracts,
                "sequential_reasoning_strategy": self.srs,
                "seeds": self.seeds,
                "nar_representation": self.nar_representation,
                "srs_explanation": self.srs_exp,
                "nar_generation_explanation": self.nar_gen_exp,
                "refinement_explanation": self.refinement_exp,
                "suggestions": self.suggestions
            }

    def is_empty(self):

        values = [item for item in self.to_dict(unroll_suggestions=True).values()]
        for value in values:
            if value is not None and len(value) > 0:
                return False

        return True

    def is_full(self):
        return not self.is_empty()

    def __matmul__(self, other):
        if self == other:
            return other
        if isinstance(other, NectronState):
            if len(self.program_description) == 0:
                self.program_description = other.program_description
            if len(self.acsl_contracts) == 0:
                self.acsl_contracts = other.acsl_contracts
            if len(self.srs) == 0:
                self.srs = other.srs
            if len(self.seeds) == 0:
                self.seeds = other.seeds
            if len(self.nar_representation) == 0:
                self.nar_representation = other.nar_representation
            if len(self.srs_exp) == 0:
                self.srs_exp = other.srs_exp
            if len(self.nar_gen_exp) == 0:
                self.nar_gen_exp = other.nar_gen_exp
            if len(self.refinement_exp) == 0:
                self.refinement_exp = other.refinement_exp

            self.suggestions = other.suggestions

        return self


def nullable_processor(item):
    if item is None:
        return ''
    else:
        return item


def read_nectron_file(file_path: str):
    if os.path.exists(file_path):
        with open(file_path, 'r') as fp:
            file = json.load(fp)

        state_entries = [
            "program_description",
            "acsl_contracts",
            "seeds",
            "sequential_reasoning_strategy",
            "nar_representation",
            "srs_explanation",
            "nar_generation_explanation",
            "refinement_explanation",
            "suggestions",
        ]

        for entry in file:
            if entry not in state_entries:
                return None

        state = NectronState(
            program_description=file['program_description'],
            acsl_contracts=file['acsl_contracts'],
            seeds=file['seeds'],
            srs=file['sequential_reasoning_strategy'],
            nar_representation=file['nar_representation'],
            srs_exp=file['srs_explanation'],
            nar_gen_exp=file['nar_generation_explanation'],
            refinement_exp=file['refinement_explanation'],
            suggestions=file['suggestions']
        )

        return state
    else:
        return None


def read_nectron_settings(file_path: str):
    if os.path.exists(file_path):
        with open(file_path, 'r') as fp:
            file = json.load(fp)

        config_entries = [
            'api_key',
            'backend_model',
            'model_identifier',
            'reflective_reasoning_intensity',
            'default_export_extension',
            'explanation',
            'program_description',
            'acsl_contracts',
            'srs',
            'nar_representation',
            'seeds'
        ]

        configuration = {}
        for entry in file:
            configuration[entry] = file[entry]
            if entry not in config_entries:
                return None

        return configuration
    else:
        raise FileNotFoundError
