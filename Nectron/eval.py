import time, json, os, subprocess
from scripts.nectron import Nectron
from evaluation.utils import preprocessing
import random
import multiprocessing


class NectronInferrer:

    """The main inference class for the Nectron system"""
    def __init__(self, 
                eval_dataset_path: str,
                gemini_api_key: str,
                openrouter_api_key: str,
                output_dir: str,
                explanation: bool = False):
        
        """
        :param eval_dataset_path: the path to the json file storing the dataset.
            Each entry in this dataset has: program description, verbosity,
            and m corrupted implementations, and the function name for masking.

        :param gemini_api_key: the api key for Gemini.
        
        :param openrouter_api_key: the api key for OpenRouter services.

        :param output_dir: the directory where inferences will be saved.

        :param explanation: a boolean that controls if the model should 
            return the explanation to every call in the pipeline. Set it to false
            to have an optimized context length.
        """

        self.evd_path = eval_dataset_path
        self.output_dir = output_dir
        
        # The IDs of LLMs. Check the OpenRouter API Docs for model IDs.
        self.supported_models = {
            1: 'google/gemma-3n-e4b-it',
            2: 'meta-llama/llama-3.1-8b-instruct',
            3: 'openai/gpt-4o-mini',
            4: 'openai/gpt-oss-20b',
            5: 'meta-llama/llama-4-maverick',
            6: 'mistralai/devstral-small',
            7: 'openai/gpt-oss-120b',
            8: 'google/gemini-2.0-flash',
            9: 'google/gemini-2.5-flash'
        }

        self.selected_models = None

        self.gemini_api_key = gemini_api_key
        self.openrouter_api_key = openrouter_api_key
        self.explanation = explanation

        self.ip = preprocessing.InferencePreprocessor()

    def __setup_models(self) -> list:
        print('\n|---------------- Nectron Inference -----------------|\n')
        print('|------------- List of Supported Models -------------|\n')
        for i, m in self.supported_models.items():
            print(f'\tKey: {i}, Model: {m}')
        
        models = input("\nUse keys to select models (space to select more or 'all' to select all of them): ").strip().split(' ')
        print('')
        if len(models) == 1 and models[0].lower() == 'all':
            return list(self.supported_models.values())
        elif len(models) >= 1:
            selected_models = []
            for model in models:
                model_key = int(model.strip()) 
                if model_key in self.supported_models:
                    selected_models.append(self.supported_models[model_key])
                else:
                    print(f'Key {model_key} is not supported.')

            if not selected_models:
                print('\nNo key has been given. Exiting program.')
                exit(1)

            return list(set(selected_models))
        else:
            print('\nNo key has been given. Exiting program.')
            exit(1)

    @staticmethod
    def __get_model_name(identifier: str):
        name = identifier.split('/')[1]
        idx = name.find(':')
        if idx != -1:
            name = name[:idx+1]
        
        return name


    def infer_nectron(self, rri: int, num_tots: int, sleep: bool = False):

        """
        This method creates the evaluation dataset via the Nectron pipeline.

        It takes the program description, pass it to the Nectron system, 
        and, first, fuses the seeds with the implementation; 
        then, second, fuses the refined contracts with the implementation.

        It also uses the corrupted implementation along with the refined contracts
        as well as the seeds to reconstructs the original program, then fuses each 
        reconstructed program with those contracts.

        All the files are saved on disk in the following structure (for each model):

        output_dir/model/code_with_contracts -> Original Implementation + Refined ACSL

        output_dir/model/code_with_seeds -> Original Implementation + ACSL Seeds

        output_dir/model/reconstruction_with_contracts -> reconstructed implementation + Refined ACSL

        output_dir/model/reconstruction_with_seeds -> reconstructed implementation + ACSL Seeds

        :param sleep: a boolean to control if one wants the method to sleep
            for random times (60 to 70 seconds) to not be blocked by the 
            OpenRouter API.
        """

        self.selected_models = self.__setup_models()

        with open(self.evd_path, 'r') as fp:
            programs = json.load(fp)

        print(f'\nThere are {len(programs)} programs to be inferred.\n')

        start_index, end_index = 0, -1
        bound_selection = input('Do you wish to infer from a specifc range (Y/n): ')
        
        if bound_selection.lower() in ['yes', 'y']:
            start_index = max(int(input('\nStart Index: ')), start_index)
            start_index = start_index if start_index < len(programs) else 0

            end_index = min(int(input('End Index: ')), len(programs)-1)
            end_index = end_index if -len(programs) <= end_index < len(programs) else -1

        print(f'\nResults of the inference will be saved in: {self.output_dir}/nectron_inference')

        for identifier in self.selected_models:

            model_name = self.__get_model_name(identifier).replace('-','_')

            print(f"\nInferring Model: {model_name.title().replace('_', ' ')}")

            self.output_dir = os.path.join(self.output_dir, 'nectron_inference')

            os.makedirs(self.output_dir, exist_ok=True)
            os.makedirs(os.path.join(self.output_dir, f'{model_name.lower()}'), exist_ok=True)
            os.makedirs(os.path.join(self.output_dir, f'{model_name.lower()}', 
                                     'code_with_contracts'), exist_ok=True)
            os.makedirs(os.path.join(self.output_dir, f'{model_name.lower()}', 
                                     'code_with_seeds'), exist_ok=True)
            os.makedirs(os.path.join(self.output_dir, f'{model_name.lower()}',
                                      'reconstruction_with_contracts'), exist_ok=True)
            os.makedirs(os.path.join(self.output_dir, f'{model_name.lower()}', 
                                     'reconstruction_with_seeds'), exist_ok=True)
            
            model = None
            if identifier.find('gemini') != -1:
                model = Nectron(api_key=self.gemini_api_key, gemini_enabled=True, explanation=self.explanation)
            else:
                model = Nectron(api_key=self.openrouter_api_key, gemini_enabled=False, openrouter_model_id=identifier, explanation=self.explanation)

            if os.path.exists(os.path.join(self.output_dir, f'{model_name.lower()}', f'results.json')):
                
                with open(os.path.join(self.output_dir, f'{model_name.lower()}', f'results.json'), 'r') as fp:
                    results = json.load(fp)
            else:
                results = {'model': identifier, 'inferred_programs': []}

            if os.path.exists(os.path.join(self.output_dir, f'{model_name.lower()}',
                                            f'nectron_outputs.json')):
                
                with open(os.path.join(self.output_dir, f'{model_name.lower()}', 
                                       f'nectron_outputs.json'), 'r') as fp:
                    evaluations = json.load(fp)
            else:
                evaluations = []

            time_taken = []
            
            print('\nStarting...\n')

            for index, program in enumerate(programs[start_index:end_index]):
                
                tic = time.perf_counter()
                model.reset()

                evaluation = model.generate_contracts(description=program['description'], rri=rri, num_tots=num_tots)

                if evaluation['acsl_contracts'].find('ScopeError') == -1:
                    fused_refined_acsl_code = evaluation['acsl_contracts'] + '\n' + program['c_implementation']
                else:
                    fused_refined_acsl_code = f'//{evaluation['acsl_contracts']}\n' + program['c_implementation']

                if evaluation['contracts_seeds'].find('ScopeError') == -1:
                    fused_seeds_acsl_code = evaluation['contracts_seeds'] + '\n' + program['c_implementation']
                else:
                    fused_seeds_acsl_code = f'//{evaluation['contracts_seeds']}\n' + program['c_implementation']

                fused_refined_reconstructions, fused_seeds_reconstructions = [], []
                refined_reconstructions, seeds_reconstructions = [], []

                for idy, corrupted_version in enumerate(program['c_corrupted_implementation']):

                    masked_corrupted_code = corrupted_version.replace(program['function_name'], 'foo')

                    tic = time.perf_counter()
                    flag = False

                    while not flag:
                        try:
                            if (evaluation['contracts_seeds'].find('ScopeError') != -1):

                                reconstruction_with_contracts = fused_refined_reconstructions[0]
                                reconstruction_with_seeds = fused_seeds_reconstructions[0]
                            
                            else:
                                reconstruction_with_contracts = model.reconstruct_program(corrupted_code=masked_corrupted_code, 
                                                                        specification=evaluation['acsl_contracts']).replace('foo', program['function_name'])
                                reconstruction_with_contracts = self.ip.preprocess(reconstruction_with_contracts)

                                reconstruction_with_seeds = model.reconstruct_program(corrupted_code=masked_corrupted_code, 
                                                                        specification=evaluation['contracts_seeds']).replace('foo', program['function_name'])
                                reconstruction_with_seeds = self.ip.preprocess(reconstruction_with_seeds)

                            flag = True
                        except:
                            flag = False

                    if evaluation['acsl_contracts'].find('ScopeError') != -1:
                        fused_refined_acsl_reconstruction = self.ip.preprocess(reconstruction_with_contracts)
                    else:
                        fused_refined_acsl_reconstruction = self.ip.preprocess(evaluation['acsl_contracts'] + '\n' + reconstruction_with_contracts)

                    if evaluation['contracts_seeds'].find('ScopeError') != -1:
                        fused_seeds_acsl_reconstruction = self.ip.preprocess(reconstruction_with_seeds)
                    else:
                        fused_seeds_acsl_reconstruction = self.ip.preprocess(evaluation['contracts_seeds'] + '\n' + reconstruction_with_seeds)

                    fused_refined_reconstructions.append(fused_refined_acsl_reconstruction)
                    fused_seeds_reconstructions.append(fused_seeds_acsl_reconstruction)

                    refined_reconstructions.append(
                        reconstruction_with_contracts.replace('//ScopeError: The provided prompt is outside the scope of contracts that NECTRON can generate.\n', '')
                    )
                    seeds_reconstructions.append(
                        reconstruction_with_seeds.replace('//ScopeError: The provided prompt is outside the scope of contracts that NECTRON can generate.\n', '')
                    )

                    with open(os.path.join(self.output_dir, f'{model_name.lower()}', 
                                           'reconstruction_with_contracts', f'program_{index+start_index}_{idy+1}.c'), 'w') as fp:
                        fp.write(fused_refined_acsl_reconstruction)

                    with open(os.path.join(self.output_dir, f'{model_name.lower()}', 
                                           'reconstruction_with_seeds', f'program_{index+start_index}_{idy+1}.c'), 'w') as fp:
                        fp.write(fused_seeds_acsl_reconstruction)

                toc = time.perf_counter()

                compiled = 1 if evaluation['contracts_seeds'].find("ScopeError") == -1 else 0

                results['inferred_programs'].append({
                    'program_index': index + start_index,
                    'program_description': program['description'],
                    'verbosity': program['verbosity'],
                    'complexity': program['complexity'],
                    'times_corrected': evaluation['times_corrected'],
                    'implementation': program['c_implementation'],
                    'fused_refined_acsl_code': fused_refined_acsl_code,
                    'fused_seeds_acsl_code': fused_seeds_acsl_code,
                    'fused_refined_acsl_reconstruction': fused_refined_reconstructions,
                    'fused_seeds_acsl_reconstruction': fused_seeds_reconstructions,
                    'adl_compiled': compiled,
                    'reconstruction_with_contracts': refined_reconstructions,
                    'reconstruction_with_seeds': seeds_reconstructions,
                    'time_taken': toc - tic
                })

                evaluations.append(evaluation)

                with open(os.path.join(self.output_dir, f'{model_name.lower()}', 
                                       'code_with_contracts', f'program_{index+start_index}.c'), 'w') as fp:
                    fp.write(fused_refined_acsl_code)

                with open(os.path.join(self.output_dir, f'{model_name.lower()}', 
                                       'code_with_seeds', f'program_{index+start_index}.c'), 'w') as fp:
                    fp.write(fused_seeds_acsl_code)

                with open(os.path.join(self.output_dir, f'{model_name.lower()}', 
                                       f'results.json'), 'w') as fp:
                    json.dump(results, fp, indent=4)

                with open(os.path.join(self.output_dir, f'{model_name.lower()}', 
                                       f'nectron_outputs.json'), 'w') as fp:
                    json.dump(evaluations, fp, indent=4)

                time_taken.append(toc - tic)

                print(f'\tTime Taken To Infer Program {index+start_index}: {toc - tic:.3f} seconds. '
                      f'Average Time Taken: {sum(time_taken) / len(time_taken):.3f} seconds')
                
                if (index + 1) % 5 == 0 and sleep:
                    sleep_for = random.randint(20, 30)
                    print(f'\tSleeping For: {sleep_for} seconds.')
                    time.sleep(sleep_for)
                
            print(f'\nFinished Inference of Model: {model_name.title().replace('_', ' ')}\n')

        print('\nInference Completed.\n')

    def infer_zero_shot(self, sleep: bool = False):
        """
        This method creates the evaluation dataset via the zero-shot pipeline.

        It takes the program description, pass it to the model through the
        zero-shot prompt, and fuses the generated contracts with the implementation.

        It also uses the corrupted implementation along with the generated contracts
        to reconstructs the original program, then fuses each reconstructed program
        with those contracts.

        All the files are saved on disk in the following structure (for each model):

        output_dir/model/code_with_contracts -> Original Implementation + Generated ACSL

        output_dir/model/reconstruction_with_contracts -> reconstructed implementation + Generated ACSL

        :param sleep: a boolean to control if one wants the method to sleep
            for random times (20 to 30 seconds) to not be blocked by the 
            OpenRouter API.
        """

        self.selected_models = self.__setup_models()

        with open(self.evd_path, 'r') as fp:
            programs = json.load(fp)

        print(f'\nThere are {len(programs)} programs to be inferred.\n')

        start_index, end_index = 0, -1
        bound_selection = input('Do you wish to infer from a specifc range (Y/n): ')
        
        if bound_selection.lower() in ['yes', 'y']:
            start_index = max(int(input('\nStart Index: ')), start_index)
            start_index = start_index if start_index < len(programs) else 0

            end_index = min(int(input('End Index: ')), len(programs)-1)
            end_index = end_index if -len(programs) <= end_index < len(programs) else -1

        print(f'\nResults of the zero shot inference will be saved in: {self.output_dir}')

        for identifier in self.selected_models:

            model_name = self.__get_model_name(identifier).replace('-','_')

            self.output_dir = os.path.join(self.output_dir, 'zero_shot_inference')
            os.makedirs(self.output_dir, exist_ok=True)
            os.makedirs(os.path.join(self.output_dir, f'{model_name.lower()}'), exist_ok=True)
            os.makedirs(os.path.join(self.output_dir,
                                      f'{model_name.lower()}', 'code_with_contracts'), exist_ok=True)
            os.makedirs(os.path.join(self.output_dir, f'{model_name.lower()}', 
                                     'reconstruction_with_contracts'), exist_ok=True)

            print(f"\nEvaluating Model: {model_name.title().replace('_', ' ')}")
            
            model = None
            if identifier.find('gemini') != -1:
                model = Nectron(api_key=self.gemini_api_key, gemini_enabled=True)
            else:
                model = Nectron(api_key=self.openrouter_api_key, gemini_enabled=False, 
                                openrouter_model_id=identifier, explanation=self.explanation)

            if os.path.exists(os.path.join(self.output_dir, f'{model_name.lower()}', f'results.json')):
                
                with open(os.path.join(self.output_dir, f'{model_name.lower()}', f'results.json'), 'r') as fp:
                    results = json.load(fp)
            else:
                results = {'model': identifier, 'inferred_programs': []}

            time_taken = []
            
            print('\nStarting...\n')

            for index, program in enumerate(programs[start_index:end_index]):

                current_index = index + start_index
                
                tic = time.perf_counter()

                zero_shot_spec = self.ip.preprocess(model.generate_zero_shot(description=program['description']))

                fused_refined_reconstructions, refined_reconstructions = [], []

                for idy, corrupted_version in enumerate(program['c_corrupted_implementation']):

                    masked_corrupted_code = corrupted_version.replace(program['function_name'], 'foo')
                    reconstruction_with_contracts = model.reconstruct_program(
                        corrupted_code=masked_corrupted_code, 
                        specification=zero_shot_spec
                    ).replace('foo', program['function_name']) # Unmasking

                    reconstruction_with_contracts = self.ip.preprocess(reconstruction_with_contracts)

                    fused_refined_acsl_reconstruction = self.ip.preprocess(zero_shot_spec + '\n' + reconstruction_with_contracts)

                    with open(os.path.join(self.output_dir, f'{model_name.lower()}', 
                                           'reconstruction_with_contracts', 
                                           f'program_{current_index}_{idy+1}.c'), 'w') as fp:
                        fp.write(fused_refined_acsl_reconstruction)

                    refined_reconstructions.append(reconstruction_with_contracts)
                    fused_refined_reconstructions.append(fused_refined_acsl_reconstruction)

                fused_refined_acsl_code = self.ip.preprocess(zero_shot_spec + '\n' + program['c_implementation'])

                toc = time.perf_counter()

                results['inferred_programs'].append({
                    'program_index': index + start_index,
                    'program_description': program['description'],
                    'verbosity': program['verbosity'],
                    'times_corrected': 0,
                    'implementation': program['c_implementation'],
                    'fused_refined_acsl_code': fused_refined_acsl_code,
                    'fused_seeds_acsl_code': 'No Seeds in Zero Shot',
                    'fused_refined_acsl_reconstruction': fused_refined_reconstructions,
                    'fused_seeds_acsl_reconstruction': 'No Seeds in Zero Shot',
                    'adl_compiled': 'No ADL in Zero Shot',
                    'reconstruction_with_contracts': refined_reconstructions,
                    'reconstruction_with_seeds': 'No Seeds in Zero Shot',
                    'time_taken': toc - tic
                })

                with open(os.path.join(self.output_dir, f'{model_name.lower()}', 
                                       'code_with_contracts', f'program_{current_index}.c'), 'w') as fp:
                    fp.write(fused_refined_acsl_code)

                with open(os.path.join(self.output_dir, f'{model_name.lower()}', f'results.json'), 'w') as fp:
                    json.dump(results, fp, indent=4)

                time_taken.append(toc - tic)

                print(f'\tTime Taken To Infer Program {index+start_index}: {toc - tic:.3f} seconds. '
                      f'Average Time Taken: {sum(time_taken) / len(time_taken):.3f} seconds')
                
                if (index + 1) % 5 == 0 and sleep:
                    sleep_for = random.randint(20, 30)
                    print(f'\tSleeping For: {sleep_for} seconds.')
                    time.sleep(sleep_for)
                
            print(f'\nFinished Inference of Model: {model_name.title().replace('_', ' ')}\n')

        print('\nInference Completed.\n')


class NectronEvaluator:

    """The main evaluation class for the Nectron system"""

    def __init__(self, inference_dir: str,
                 save_dir: str, 
                 rri: int, 
                 tot: int,
                 ):
        
        """
        :param inference_dir: the directory that stores all inferences from models.
            it's the folder set up when NectronInferrer is used.

        :param save_dir: the save directory for evaluation.

        :param rri: the reflective reasoning intensity (e.g. how many reflections 
            are performed). The same as the 'r' variable in the paper.

        :param tot: the number of trees-of-thought.

        :param eval_script_template_path: the path for the evaluation script template
            that is used to create the shell script to perform the evaluation.
            (A deprecated argument)
        """

        self.inference_dir = inference_dir
        self.save_dir = save_dir
        self.rri = rri
        self.tot = tot
        self.eval_script_template = ''

        self.raw_evaluations = []

    def create_evaluation_script(self, save_dir: str):
        """
            Used to create the shell evaluation script to evaluate the model. (Deprecated)

            :param save_dir: The save directory of the evaluation script, must be 
                        placed in the same directory as the inferred C/ACSL files.
        """
        script = self.eval_script_template.replace('<rri>', str(self.rri))
        script = script.replace('<tot>', str(self.tot))
        output_dir = os.path.join(save_dir, "eval_output")
        script = script.replace('<res_dir>', f"\"{output_dir}\"")
        script = script.replace('<src_dir>', f"\"{save_dir}\"")

        with open(os.path.join(save_dir, 'evaluate.sh'), 'w', newline='\n') as fp:
            fp.write(script)

        os.chmod(os.path.join(save_dir, 'evaluate.sh'), 0o755)

        return 0
    
    @staticmethod
    def preprocess_eval_result(result: str):
        """
        This method preprocess the output of Frama-C's analysis.

        :param result: a string output of the Frama-C's analysis.
        """
        stats = {'proved goals': 0, 'total goals': 0, 'timeout': 0,
                 'terminating': 0, 'unreachable': 0, 'qed': 0,
                 'alt-ergo': 0}
        
        for line in result.splitlines():
            if line.find('Proved goals:') != -1:
                pg = line.split(':')[1].strip().split('/')
                stats['proved goals'] = int(pg[0].split('(')[0].strip())
                stats['total goals'] = int(pg[1].split('(')[0].strip())
            elif line.find('Terminating:') != -1:
                stats['Terminating'] = int(line.split(':')[1].strip().split('(')[0].strip())
            elif line.find('Unreachable:') != -1:
                stats['unreachable'] = int(line.split(':')[1].strip().split('(')[0].strip())
            elif line.find('Qed:') != -1:
                stats['qed'] = int(line.split(':')[1].strip().split('(')[0].strip())
            elif line.find('Timeout:') != -1:
                stats['timeout'] = int(line.split(':')[1].strip().split('(')[0].strip())
            elif line.find('Alt-Ergo:') != -1:
                stats['alt-ergo'] = int(line.split(':')[1].strip().split('(')[0].strip())

        return stats
    
    @staticmethod
    def calculate_adherence_score(stats: dict):
        """
        This method calculates the adherence score.

        :param stats: a dictionary containing all the results
            from the Frama-C verificaion run on the given
            program.
        """
        if stats['total goals'] != 0:
            return stats['proved goals'] / stats['total goals']

        return 0
    
    def run_frama_c(self, filepath: str):
        """
        This method runs Frama-C's static analysis on a program.

        :param filepath: the path of the .c file that contains
            the ACSL contracts along the C program.
        """
        print(f"\tFile: {filepath}")
        try:
            result = subprocess.run(
                        ["frama-c", "-wp", "-rte", filepath],
                        capture_output=True,
                        text=True
                    )
            return {
                "file": filepath.split('/')[-1].strip(),
                "returncode": result.returncode,
                'eval_stats': self.preprocess_eval_result(result.stdout),
                "output": result.stdout,
                "errors": result.stderr
            }
        except:
            result = 'Decoding Error'
        
            return {
                    "file": filepath.split('/')[-1].strip(),
                    "returncode": -1,
                    'eval_stats': self.preprocess_eval_result(result),
                    "output": result,
                    "errors": result
                }
        
    def evaluate(self, model_exclusion: list = [], zero_shot: bool=False):
        """
        This method performs the evaluation on the dataset provided. It iterates over
        all contracts fused programs (original and corrupted) and pass them to Frama-C.
        Next, the results of Frama-C are preprocessed to get the necessary statistics
        to compute the adherence, and subsequentely, the performance.

        :param model_exclusion: a list of models to exclude from the evaluation.
        :param zero_shot: a boolean used to control the pipeline on which the evaluation
            will be performed: Nectron or Zero-Shot. If it's set to false, then the Nectron
            system will be evaluated; otherwise, zero-shot.
        """

        if zero_shot:
            self.save_dir = os.path.join(self.save_dir, 'zero_shot_evaluation')
        else:
            self.save_dir = os.path.join(self.save_dir, 'nectron_evaluation')
            
        all_results = []
        if not zero_shot:
            print(f"\n------------------- Evaluating Nectron (rri = {self.rri}; tots = {self.tot}) -------------------\n")
        else:
            print(f"\n------------------- Evaluating Zero Shot -------------------\n")


        print(f'Evaluation results will saved in: {self.save_dir}\n')

        for modelf in os.listdir(self.inference_dir):

            if modelf in model_exclusion:
                continue

            print(f"\nEvaluating Model: {modelf}\n")
            if zero_shot:
                model_results = {'refinement_acsl': [], 
                                 'refinement_reconstructions': []}
            else:
                model_results = {'refinement_acsl': [], 'seeds_acsl': [],
                            'refinement_reconstructions': [],
                            'seeds_reconstructions': []}
            for subfolder in os.listdir(os.path.join(self.inference_dir, modelf)):
                if not subfolder.endswith('.json'):
                    print(f"\nTarget: {subfolder}\n")
                    save_key = ''
                    if subfolder == 'code_with_contracts':
                        save_key = 'refinement_acsl'
                    elif subfolder == 'code_with_seeds':
                        save_key = 'seeds_acsl'
                    elif subfolder == 'reconstruction_with_contracts':
                        save_key = 'refinement_reconstructions'
                    elif subfolder == 'reconstruction_with_seeds':
                        save_key = 'seeds_reconstructions'

                    
                    c_files = []
                    for c_file in os.listdir(os.path.join(self.inference_dir, modelf, subfolder)):
                        c_files.append(os.path.join(self.inference_dir, modelf, subfolder, c_file))

                    with multiprocessing.Pool(multiprocessing.cpu_count()) as pool:
                        model_results[save_key] = pool.map(self.run_frama_c, c_files)

            # Program Adherence: Iterate over all programs
            # Evaluate the program, then iterate over
            # its m reconstructions and evaluate them
            # Next, take their average and multiply it
            # by whatever you got in the program evaluation


            pairs = [('refinement_acsl', 'refinement_reconstructions')]
            refinement_results = []
            performance = {'refinement': 0}

            if not zero_shot:
                pairs = [('refinement_acsl', 'refinement_reconstructions'), ('seeds_acsl', 'seeds_reconstructions')]
                seeds_results = []
                performance = {'refinement': 0, 'seeds': 0}

            for pair in pairs:
                for program in model_results[pair[0]]:
                    p_idx = int(program['file'].split('_')[1].split('.')[0])

                    program_score = self.calculate_adherence_score(program['eval_stats'])
                    m = 0
                    reconstruction_scores = []

                    for reconstruction in model_results[pair[1]]:
                        index = int(program['file'].split('_')[1].split('.')[0])

                        if index == p_idx:
                            reconstruction_score = self.calculate_adherence_score(reconstruction['eval_stats'])
                            reconstruction_scores.append(reconstruction_score)
                            m += 1
                    
                    r_mean_score = sum(reconstruction_scores) / m

                    adherence_score = program_score * r_mean_score

                    if pair[0].find('refinement') != -1:
                        performance['refinement'] += adherence_score / len(model_results[pair[0]])
                        refinement_results.append({
                            "alpha": adherence_score,
                            "program_score": program_score,
                            "reconstruction_mean_score": r_mean_score,
                            "reconstructions_scores": reconstruction_scores
                        })

                    if not zero_shot and pair[0].find('seeds') != -1:
                        performance['seeds'] += adherence_score / len(model_results[pair[0]])
                        seeds_results.append({
                            "alpha": adherence_score,
                            "program_score": program_score,
                            "reconstruction_mean_score": r_mean_score,
                            "reconstructions_scores": reconstruction_scores
                        })

            if not zero_shot:
                print(f"\nModel: {modelf} has achieved a performance of {performance['refinement'] * 100:.3f}% for Refinement"
                    f" and {performance['seeds'] * 100:.3f}% for Seeds.\n")
            else:
                print(f"\nModel: {modelf} has achieved a performance of {performance['refinement'] * 100:.3f}% for Zero-Shot.")

            entry = {
                'model': modelf,
                'results': model_results,
                'performance': performance
            }

            os.makedirs(self.save_dir, exist_ok=True)
            os.makedirs(os.path.join(self.save_dir, modelf), exist_ok=True)

            with open(os.path.join(self.save_dir, modelf, 'evaluation.json'), 'w') as fp:
                json.dump(entry, fp, indent=4)

            with open(os.path.join(self.save_dir, modelf, 'refinement_eval.json'), 'w') as fp:
                json.dump(refinement_results, fp, indent=4)

            if not zero_shot:
                with open(os.path.join(self.save_dir, modelf, 'seeds_eval.json'), 'w') as fp:
                    json.dump(seeds_results, fp, indent=4)

            all_results.append(entry)

        if os.path.exists(os.path.join(self.save_dir, 'complete_evaluations.json')):
            with open(os.path.join(self.save_dir, 'complete_evaluations.json'), 'r') as fp:
                old_results = json.load(fp)

            old_results.extend(all_results)
        else:
            with open(os.path.join(self.save_dir, 'complete_evaluations.json'), 'w') as fp:
                json.dump(all_results, fp, indent=4)

        print('\nFinished Evaluation.')


if __name__ == '__main__':
    
    # 1) You must create the evaluation dataset. To create run the lines (1) below.

    # inf = NectronInferrer(eval_dataset_path='evaluation/eval_programs.json',
    #                          gemini_api_key='YOUR_GEMINI_API_KEY',
    #                          openrouter_api_key='YOUR_OPEN_ROUTER_API_KEY',
    #                          output_dir='YOUR_INFERENCE_DIR', explanation=False) # 1

    # inf.infer_nectron(rri=2, num_tots=1) # 1

    # inf.infer_zero_shot() # 1

    # 2) After you create the evaluation dataset, run the following lines (2) to launch the evaluation.

    # neval = NectronEvaluator(inference_dir='YOUR_INFERENCE_DIR',
    #                          save_dir='EVAL_SAVE_DIR',
    #                          rri=2, tot=1) # 2


    # neval.evaluate(zero_shot=False, model_exclusion=['llama-3.1-8b-instruct']) # 2
    
    # neval.evaluate(zero_shot=True) # Run this if you want the zero-shot inference. Make sure to change the save directory.

    pass