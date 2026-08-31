import multiprocessing
import preprocessing

from .nectron import Nectron
import time, json, os, subprocess

class NectronInferrer:

    """The main inference class for the Nectron system"""
    def __init__(self, 
                eval_dataset_path: str,
                openrouter_api_key: str,
                output_dir: str):
        
        """
        :param eval_dataset_path: the path to the json file storing the dataset.
            Each entry in this dataset has: program description, verbosity,
            and m corrupted implementations, and the function name for masking.
        
        :param openrouter_api_key: the api key for OpenRouter services.

        :param output_dir: the directory where inferences will be saved.

        """

        self.evd_path = eval_dataset_path
        self.output_dir = output_dir
        
        # The IDs of LLMs. Check the OpenRouter API Docs for model IDs.
        self.supported_models = {
            1: 'google/gemma-3n-e4b-it',
            2: 'google/gemma-4-26b-a4b-it',
            3: 'openai/gpt-4o-mini',
            4: 'openai/gpt-oss-20b',
            5: 'x-ai/grok-4-fast',
            6: 'mistralai/devstral-small',
            7: 'openai/gpt-oss-120b',
            8: 'openai/gpt-5.4-nano',
            9: 'inception/mercury-2',
            10: 'meta-llama/llama-3.1-8b-instruct',
            11: 'google/gemini-2.0-flash',
            12: 'google/gemini-2.5-flash',
            13: 'meta-llama/llama-4-maverick'
        }

        self.selected_models = None
        self.openrouter_api_key = openrouter_api_key

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


    def infer_nectron(self):

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
                                      'reconstruction_with_contracts'), exist_ok=True)

            model = Nectron(api_key=self.openrouter_api_key, openrouter_model_id=identifier)
            
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

            for index, program in enumerate(programs[start_index:end_index+1]):
                
                tic = time.perf_counter()
                model.reset()

                evaluation = model.generate_contracts(description=program['description'])

                if evaluation['acsl_contracts'].find('ScopeError') == -1:
                    fused_refined_acsl_code = evaluation['acsl_contracts'] + '\n' + program['c_implementation']
                else:
                    fused_refined_acsl_code = f'//{evaluation['acsl_contracts']}\n' + program['c_implementation']

                fused_refined_reconstructions = []
                refined_reconstructions= []

                for idy, corrupted_version in enumerate(program['c_corrupted_implementation']):

                    masked_corrupted_code = corrupted_version.replace(program['function_name'], 'foo')

                    if evaluation['acsl_contracts'].find('ScopeError') != -1:

                        reconstruction_with_contracts = "//Couldn't reconstruct, Non-Compilable NAR\n" + corrupted_version
                    
                    else:
                        reconstruction_with_contracts = model.reconstruct_program(corrupted_code=masked_corrupted_code, 
                                                                specification=evaluation['acsl_contracts']).replace('foo', program['function_name'])
                        reconstruction_with_contracts = self.ip.preprocess(reconstruction_with_contracts)


                    if evaluation['acsl_contracts'].find('ScopeError') != -1:
                        fused_refined_acsl_reconstruction = self.ip.preprocess(reconstruction_with_contracts)
                    else:
                        fused_refined_acsl_reconstruction = self.ip.preprocess(evaluation['acsl_contracts'] + '\n' + reconstruction_with_contracts)

                    fused_refined_reconstructions.append(fused_refined_acsl_reconstruction)

                    refined_reconstructions.append(
                        reconstruction_with_contracts.replace('//ScopeError: The provided prompt is outside the scope of contracts that NECTRON can generate.\n', '')
                    )

                    with open(os.path.join(self.output_dir, f'{model_name.lower()}', 
                                           'reconstruction_with_contracts', f'program_{index+start_index}_{idy+1}.c'), 'w') as fp:
                        fp.write(fused_refined_acsl_reconstruction)

                toc = time.perf_counter()

                compiled = 1 if evaluation['acsl_contracts'].find("ScopeError") == -1 else 0

                results['inferred_programs'].append({
                    'program_index': index + start_index,
                    'program_description': program['description'],
                    'verbosity': program['verbosity'],
                    'times_corrected': evaluation['times_corrected'],
                    'implementation': program['c_implementation'],
                    'fused_refined_acsl_code': fused_refined_acsl_code,
                    'fused_refined_acsl_reconstruction': fused_refined_reconstructions,
                    'nar_compiled': compiled,
                    'reconstruction_with_contracts': refined_reconstructions,
                    'time_taken': toc - tic
                })

                evaluations.append(evaluation)

                with open(os.path.join(self.output_dir, f'{model_name.lower()}', 
                                       'code_with_contracts', f'program_{index+start_index}.c'), 'w') as fp:
                    fp.write(fused_refined_acsl_code)

                with open(os.path.join(self.output_dir, f'{model_name.lower()}', 
                                       f'results.json'), 'w') as fp:
                    json.dump(results, fp, indent=4)

                with open(os.path.join(self.output_dir, f'{model_name.lower()}', 
                                       f'nectron_outputs.json'), 'w') as fp:
                    json.dump(evaluations, fp, indent=4)

                time_taken.append(toc - tic)

                print(f'\tTime Taken To Infer Program {index+start_index}: {toc - tic:.3f} seconds. '
                      f'Average Time Taken: {sum(time_taken) / len(time_taken):.3f} seconds')
                
            print(f'\nFinished Inference of Model: {model_name.title().replace('_', ' ')}\n')

        print('\nInference Completed.\n')

    def infer_zero_shot(self):
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
            
            model = Nectron(api_key=self.openrouter_api_key, openrouter_model_id=identifier)

            if os.path.exists(os.path.join(self.output_dir, f'{model_name.lower()}', f'results.json')):
                
                with open(os.path.join(self.output_dir, f'{model_name.lower()}', f'results.json'), 'r') as fp:
                    results = json.load(fp)
            else:
                results = {'model': identifier, 'inferred_programs': []}

            time_taken = []
            
            print('\nStarting...\n')

            for index, program in enumerate(programs[start_index:end_index+1]):

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
                    'fused_refined_acsl_reconstruction': fused_refined_reconstructions,
                    'nar_compiled': 'No NAR in Zero Shot',
                    'reconstruction_with_contracts': refined_reconstructions,
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
                
            print(f'\nFinished Inference of Model: {model_name.title().replace('_', ' ')}\n')

        print('\nInference Completed.\n')

    def preprocess_inferences(self, inferences_dir: str, clean_out_dir: str):

        os.makedirs(clean_out_dir, exist_ok=True)

        subdirs = ['code_with_contracts',
                   'reconstruction_with_contracts']
        
        for subset in subdirs:
            os.makedirs(os.path.join(clean_out_dir, subset), 
                        exist_ok=True)
            path = os.path.join(inferences_dir, subset)
            for file in os.listdir(path):
                filepath = os.path.join(path, file)
                if filepath.endswith('.c'):
                    with open(filepath, 'r') as fp:
                        code = fp.read()

                    clean_code = self.ip.preprocess(code)

                    save_path = os.path.join(clean_out_dir, subset, file)

                    with open(save_path, 'w') as fp:
                        fp.write(clean_code)

            print(f'Finished Subset: {subset}')

        print(f'Finished cleaning, check: {clean_out_dir}')


class NectronEvaluator:

    """The main evaluation class for the Nectron system"""

    def __init__(self, inference_dir: str,
                 save_dir: str
                 ):
        
        """
        :param inference_dir: the directory that stores all inferences from models.
            it's the folder set up when NectronInferrer is used.

        :param save_dir: the save directory for evaluation.

        """

        self.inference_dir = inference_dir
        self.save_dir = save_dir
        self.eval_script_template = ''

        self.raw_evaluations = []

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
            print(f"\n------------------- Evaluating Nectron -------------------\n")
        else:
            print(f"\n------------------- Evaluating Zero Shot -------------------\n")

        print(f'Evaluation results will be saved in: {self.save_dir}\n')

        for modelf in os.listdir(self.inference_dir):

            if modelf in model_exclusion:
                continue

            print(f"\nEvaluating Model: {modelf}\n")

            model_results = {'acsl': [],
                        'acsl_reconstructions': []}
            
            for subfolder in os.listdir(os.path.join(self.inference_dir, modelf)):
                if not subfolder.endswith('.json'):
                    print(f"\nTarget: {subfolder}\n")
                    save_key = ''
                    if subfolder == 'code_with_contracts':
                        save_key = 'acsl'
                    elif subfolder == 'reconstruction_with_contracts':
                        save_key = 'acsl_reconstructions'

                    
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

            pair = ('acsl', 'acsl_reconstructions')
            symbolic_engine_results = []
            performance = {'acsl': 0}

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

                performance['acsl'] += adherence_score / len(model_results[pair[0]])

                symbolic_engine_results.append({
                    "alpha": adherence_score,
                    "program_score": program_score,
                    "reconstruction_mean_score": r_mean_score,
                    "reconstructions_scores": reconstruction_scores
                })

            if not zero_shot:
                print(f"\nModel: {modelf} has achieved a performance of {performance['acsl'] * 100:.3f}%.\n")
            else:
                print(f"\nModel: {modelf} has achieved a performance of {performance['acsl'] * 100:.3f}% in Zero-Shot.")

            entry = {
                'model': modelf,
                'results': model_results,
                'performance': performance
            }

            os.makedirs(self.save_dir, exist_ok=True)
            os.makedirs(os.path.join(self.save_dir, modelf), exist_ok=True)

            with open(os.path.join(self.save_dir, modelf, 'evaluation.json'), 'w') as fp:
                json.dump(entry, fp, indent=4)

            with open(os.path.join(self.save_dir, modelf, 'acsl_eval.json'), 'w') as fp:
                json.dump(symbolic_engine_results, fp, indent=4)

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

    # inf = NectronInferrer(eval_dataset_path='NectronBench/nectron_bench.json',
    #                          openrouter_api_key='',
    #                          output_dir='Evalv2/NoSRSAblation') # 1

    # inf.infer_nectron(num_tots=1) # 1

    # inf.preprocess_inferences('Ablation/fixed_progs_no_plan/nectron_inference/gpt_4o_mini', 
    #                           'Ablation/fixed_progs_no_plan/clean_no_plan_inferences/gpt_4o_mini')

    # inf.infer_zero_shot() # 1

    # 2) After you create the evaluation dataset, run the following lines (2) to launch the evaluation.

    # neval = NectronEvaluator(inference_dir='Evalv2/NoSRSAblation/nectron_inference',
    #                          save_dir='Evalv2/NoSRSAblation/NoSRS_Eval',
    #                          tot=0) # 2


    # neval.evaluate(zero_shot=False, model_exclusion=['gpt_4o_mini', 'gpt_oss_20b', 
    #                                                  'gpt_oss_120b', 'gpt_5.4_nano',
    #                                                  'gemma_4_26b_a4b_it', 'mercury_2'])
    
    # neval.evaluate(zero_shot=True) # Run this if you want the zero-shot inference. Make sure to change the save directory.

    pass