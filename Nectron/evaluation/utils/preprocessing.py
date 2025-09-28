import os, json, re, shutil
from collections import Counter

class InferencePreprocessor:

    """
        Used to preprocess models' inferences such as delimiter corrections,
        library imports ordering, etc. This ensures the we don't lose evaluation
        results (syntax errors) just for small mistakes.

        No preprocessing is done with LLMs.
    """

    def __init__(self, input_dir: str = '', output_dir: str = ''):
        
        self.input_dir = input_dir
        self.output_dir = output_dir

    @staticmethod
    def preprocess(text: str):
        """
            Light preprocessing of text: delimiter correction, library imports ordering, etc.
        """
        text = text.replace('`d\n', '\n').replace('l\n', '').replace('c\n', '')
        text = text.replace('`', '').replace('\nd\n', '\n').replace('d\ni', 'i')

        lib_rx_pattern = r"#include <\w+.*h*>"

        libraries = set(re.findall(lib_rx_pattern, text))

        for index, lib in enumerate(libraries):
            text = text.replace(lib, '')
            temp = text.split('\n')

            temp.insert(index, lib)

            text = '\n'.join(temp)

        text = text.replace('`', '').replace('\n\n', '\n')

        return text
    
    def get_all_delimiters(self):
        """
            Used to get the delimiters generated and consequently - due to the unpredictibility of inference -
            hallucinations.
        """
        targets = {}
        
        for modelf in os.listdir(self.input_dir):
            targets[modelf] = {'delimiters': [], 'tags': [], 'hal_file_indices': 0}
            for subfolder in os.listdir(os.path.join(self.input_dir, modelf)):
                if not subfolder.endswith('.json'):
                    for idx, file in enumerate(os.listdir(os.path.join(self.input_dir, modelf, subfolder))):
                        with open(os.path.join(self.input_dir, modelf, subfolder, file), 'r') as fp:
                            source_code = fp.read()
                        if source_code.find('```') != -1:
                            delimiter_matches = list(map(lambda x: x.group(), re.finditer(r"```[\w]+\n*", source_code)))
                            targets[modelf]['delimiters'].extend(delimiter_matches)
                            targets[modelf]['delimiters'] = list(set(targets[modelf]['delimiters']))
                            targets[modelf]['hal_file_indices'] += 1
                        if source_code.find('<') != -1:
                            tag_matches = list(map(lambda x: x.group(), re.finditer(r"</*[\w]+>\n*", source_code)))
                            targets[modelf]['tags'].extend(tag_matches)
                            targets[modelf]['tags'] = list(set(targets[modelf]['tags']))
                            targets[modelf]['hal_file_indices'] += 1
                        
        return targets
    
    def iterate_and_preprocess(self, zero_shot: bool = False):
        """
            Iterates over all inferences (for each model) and preprocess them.
            
            :param zero_shot: used to indicate that the preprocessing will be applied over zero shot inferences,
                              thereby avoiding preprocessing things that are not necessary.
        """

        for modelf in os.listdir(self.input_dir):
            os.makedirs(os.path.join(self.output_dir, modelf), exist_ok=True)
            print(f"\nPreprocessing: {modelf}")
            for subfolder in os.listdir(os.path.join(self.input_dir, modelf)):
                print(f"\tPreprocessing: {modelf}/{subfolder}")
                if not subfolder.endswith('.json'):
                    os.makedirs(os.path.join(self.output_dir, modelf, subfolder), exist_ok=True)
                    for idx, file in enumerate(os.listdir(os.path.join(self.input_dir, modelf, subfolder))):
                        with open(os.path.join(self.input_dir, modelf, subfolder, file), 'r') as fp:
                            source_code = fp.read()

                        source_code = self.preprocess(source_code)

                        with open(os.path.join(self.output_dir, modelf, subfolder, file), 'w') as fp:
                            fp.write(source_code)
                else:
                    json_file = os.path.join(self.input_dir, modelf, subfolder)
                    
                    if json_file.find('results') != -1:
                        with open(json_file, 'r') as fp:
                            results = json.load(fp)

                        for idx, entry in enumerate(results['inferred_programs']):
                            entry['fused_refined_acsl_code'] = self.preprocess(entry['fused_refined_acsl_code'])
                            entry['fused_seeds_acsl_code'] = self.preprocess(entry['fused_seeds_acsl_code'])

                            for idy, fused_reconstruction in enumerate(entry['fused_refined_acsl_reconstruction']):
                                entry['fused_refined_acsl_reconstruction'][idy] = self.preprocess(fused_reconstruction)

                            for idy, reconstruction in enumerate(entry['reconstruction_with_contracts']):
                                entry['reconstruction_with_contracts'][idy] = self.preprocess(reconstruction)

                            if not zero_shot:
                                for idy, fused_reconstruction in enumerate(entry['fused_seeds_acsl_reconstruction']):
                                    entry['fused_seeds_acsl_reconstruction'][idy] = self.preprocess(fused_reconstruction)
                                
                                for idy, reconstruction in enumerate(entry['reconstruction_with_seeds']):
                                    entry['reconstruction_with_seeds'][idy] = self.preprocess(reconstruction)

                            results['inferred_programs'][idx] = entry

                        with open(os.path.join(self.output_dir, modelf, subfolder), 'w') as fp:
                            json.dump(results, fp, indent=4)
                    else:
                        if not zero_shot and json_file.find('nectron') != -1:
                            shutil.copy(json_file, os.path.join(self.output_dir, modelf, subfolder))


if __name__ == '__main__':

    ip = InferencePreprocessor(input_dir='evaluation/zero_shot', output_dir='evaluation/evals/zero_shot_inference')

    # ip.iterate_and_preprocess(zero_shot=True)
  

    