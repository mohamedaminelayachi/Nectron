try:
    import json
    import google.generativeai as genai
    from typing import Union
    from google.api_core.exceptions import InvalidArgument
except ImportError:
    raise ImportError("You seem to have missed some dependencies. Make sure to check the requirements.")


class NectronGemini:

    def __init__(self, explanation: bool = True, identifier: str = 'gemini-2.5-flash'):
        self.__api_key = None
        self.__client = None
        self.__model: genai.GenerativeModel
        self.__num_requests = None
        self.__sleep = None
        if explanation:
            with open('./prompts/prompts.json', 'r', encoding='utf8') as fp:
                self.__prompts = json.load(fp)
        else:
            with open('./prompts/no_exp_prompts.json', 'r', encoding='utf8') as fp:
                self.__prompts = json.load(fp)
        self.__pd = None
        self.__explanation = explanation
        self.identifier = identifier

    def InitClient(self, api_key: str = None, api_key_path: str = None, num_requests: int = 20, sleep: int = 2):
        """
        Before the generation starts, this method must be called first, since it is responsible for initializing
        the client with the proper API key. As such, a connection to the LLM will be established.
        :param api_key: a string that holds the value for the API key.
        :param api_key_path: a string that holds the path where the API key is located. When used, api_key won't be
        used.
        :param num_requests: The allowed number of requests which the system can send through the API (Per Minute).
        :param sleep: The time that the system should wait before sending requests (In Seconds).
        :return:
        """
        if api_key_path is not None:
            with open(api_key_path, 'r') as fp:
                try:
                    api_key = json.load(fp)["GEMINI_API_KEY"]
                except KeyError:
                    api_key = json.load(fp)["API_KEY"]
                except Exception:
                    raise Exception("API Key not found.")
            self.__api_key = api_key
        elif api_key is not None:
            self.__api_key = api_key
        else:
            raise Exception("You haven't provided an API Key.")

        try:
            genai.configure(api_key=self.__api_key)
        except Exception:
            raise InvalidArgument

        self.__client = True
        self.__model = genai.GenerativeModel(self.identifier)
        self.__num_requests = int(abs(num_requests))
        self.__sleep = int(abs(sleep))

    def __quick_check(self, **kwargs) -> Union[bool, Exception]:
        """
        quick_check() checks for errors related to the client initialization and the model's input.
        :param kwargs:
        :return:
        """
        if self.__client is None:
            raise Exception("Client has not been initialized."
                            " Use InitClient() with a valid API key to initialize your client.")

        if 'program_description' in kwargs.keys() and len(kwargs['program_description']) == 0:
            raise Exception("ERROR: You have provided an empty description. Please provide a valid description.")

        if 'prompt' in kwargs.keys() and len(kwargs['prompt']) == 0:
            raise Exception("ERROR: You have provided an empty prompt. Please provide a valid prompt.")

        if 'nar_code' in kwargs.keys() and len(kwargs['nar_code']) == 0:
            raise Exception("ERROR: An empty NAR program. Please provide a valid NAR program.")

        if 'contracts' in kwargs.keys() and len(kwargs['contracts']) == 0:
            raise Exception("ERROR: An empty set of contracts was provided. Please provide a valid set of contracts.")

        if 'srs' in kwargs.keys() and len(kwargs['srs']) == 0:
            raise Exception("ERROR: An empty Sequential Reasoning Strategy was provided. Please provide a valid SRS.")

        return True

    def generate_srs(self, program_description: str) -> Union[str, tuple]:
        """
        This method is used to interact with the model to generate a response for the given prompt.
        :param program_description: The program's description.
        :return:
        """
        if self.__quick_check(description=program_description):
            self.__pd = program_description
            prompt = self.__prompts["srs"].replace('PROGRAM_DESCRIPTION', program_description)
            response = self.__model.generate_content(prompt)

            srs_begin = '<srs>'
            srs_end = '</srs>'

            exp_begin = '<explanation>'
            exp_end = '</explanation>'

            if self.__explanation:
                if response is not None and len(response.text) > 0:
                    return (response.text[response.text.find(srs_begin) + len(srs_begin) + 1
                                    :response.text.find(srs_end)].strip('\n'),
                            response.text[response.text.find(exp_begin) + len(exp_begin) + 1:
                            response.text.find(exp_end)].strip('\n'))
            else:
                if response is not None and len(response.text) > 0:
                    return (response.text[response.text.find(srs_begin) + len(srs_begin) + 1
                                    :response.text.find(srs_end)].strip('\n'), '')

    def correct_syntax(self,
                       nar_code: str,
                       srs: str,
                       modular_example_class: str = None) -> Union[str, tuple]:
        """
        Syntax Correction is a way the contracts generation system employs to fix syntax and semantic errors that
        might be occurring in the NAR representation, thereby improving the robustness of the system during the contracts
        generation process that is done by Pyramid. This method implements the exact behavior by leveraging the
        capabilities of LLMs.

        :param nar_code: The NAR representation.
        :param srs: The sequential reasoning strategy.
        :param modular_example_class: Depending on the type of errors that might be occurring in the given NAR representation,
                                    a dynamic process picks the right example to guide the LLM in the correction.
        :return: This method returns the corrected NAR representation and the LLM explanation for its correction decisions.
        """
        if self.__quick_check(nar_code=nar_code):
            prompt = self.__example_modularity().replace('INPUT_NAR_PROGRAM', nar_code).replace('INPUT_SRS', srs)
            response = self.__model.generate_content(prompt)

            nar_begin = '<nar>'
            nar_end = '</nar>'

            exp_begin = '<explanation>'
            exp_end = '</explanation>'

            if self.__explanation:
                if response is not None and len(response.text) > 0:
                    return (response.text[response.text.find(nar_begin) + len(nar_begin) + 1
                                        :response.text.find(nar_end)].strip('\n'),
                            response.text[response.text.find(exp_begin) + len(exp_begin) + 1:
                                        response.text.find(exp_end)].strip('\n'))
            else:
                if response is not None and len(response.text) > 0:
                    return (response.text[response.text.find(nar_begin) + len(nar_begin) + 1
                                        :response.text.find(nar_end)].strip('\n'), '')

    def refine_contracts(self,
                         contracts: str,
                         verification_plan: str) -> Union[str, tuple]:
        """
        Contracts Refinement is a way the contract generation system employs to extend a given set of contracts and
        improve their completeness. This method implements the exact behavior by leveraging the capabilities of LLMs.
        :param contracts: The set of contracts that were generated by Pyramid.
        :param verification_plan: The verification plan constructed from ToTs.
        :return: This method returns the extended set of contracts and the LLM explanation for its extension decisions.
        """
        if self.__quick_check(contracts=contracts):
            prompt = self.__prompts['contracts_refinement'].replace('INPUT_CONTRACTS', contracts).replace('%VPLAN%', verification_plan).replace("PROGRAM_DESCRIPTION", self.__pd)
            response = self.__model.generate_content(prompt)

            contracts_begin = '<contracts>'
            contracts_end = '</contracts>'

            exp_begin = '<explanation>'
            exp_end = '</explanation>'

            if self.__explanation:
                if response is not None and len(response.text) > 0:
                    return (response.text[response.text.find(contracts_begin) + len(contracts_begin) + 1
                                    :response.text.find(contracts_end)].strip('\n'),
                            response.text[response.text.find(exp_begin) + len(exp_begin) + 1:
                            response.text.find(exp_end)-1].strip('\n'))
            else:
                if response is not None and len(response.text) > 0:
                    return (response.text[response.text.find(contracts_begin) + len(contracts_begin) + 1
                                    :response.text.find(contracts_end)].strip('\n'), '')

    def generate_nar(self, srs: str) -> Union[str, tuple]:
        """
        Contracts Refinement is a way the contract generation system employs to extend a given set of contracts and
        improve their completeness. This method implements the exact behavior by leveraging the capabilities of LLMs.

        :param srs: The sequential reasoning strategy.
        :return:
        """
        if self.__quick_check(srs=srs):
            prompt = self.__prompts['nar_generation'].replace('INPUT_SRS', srs)
            response = self.__model.generate_content(prompt)

            nar_begin = '<nar>'
            nar_end = '</nar>'

            exp_begin = '<explanation>'
            exp_end = '</explanation>'

            if self.__explanation:
                if response is not None and len(response.text) > 0:
                    return (response.text[response.text.find(nar_begin) + len(nar_begin) + 1
                                    :response.text.find(nar_end)].strip('\n'),
                            response.text[response.text.find(exp_begin) + len(exp_begin) + 1:
                            response.text.find(exp_end)].strip('\n'))
            else:
                if response is not None and len(response.text) > 0:
                    return (response.text[response.text.find(nar_begin) + len(nar_begin) + 1
                                    :response.text.find(nar_end)].strip('\n'), '')

    def reflective_reasoning(self, contracts: str, verification_plan: str, batch_samples: int) -> Union[str, tuple]:
        """
            Reflective Reasoning is an approach to maximize logical consistencies in contracts generation. This method
            implements this process by generating multiple contracts' set samples, and pass them to an LLM that employs
            its reasoning to the best of its ability to mitigate inconsistencies.
            :param contracts: The set of contracts that were generated by Pyramid.
            :param verification_plan: The verification plan constructed from ToTs.
            :param batch_samples: Number of contracts' set samples.
            :return: This method returns the extended set of contracts and the LLM explanation for its extension decisions.
        """
        batch = []
        batch_exps = []
        for sample in range(batch_samples):
            contracts_set = self.refine_contracts(contracts, verification_plan)
            batch.append('<contracts>\n' + contracts_set[0].strip('\n') + '\n</contracts>')
            batch_exps.append(contracts_set[1].strip('\n'))

        contracts_samples = '\n\n'.join(batch)
        prompt = self.__prompts['reflective_reasoning'].replace('%DEVELOPERS%', str(batch_samples))
        prompt = prompt.replace('%VPLAN%', verification_plan).replace('%INSERT_BATCH_SAMPLES%', contracts_samples).replace("PROGRAM_DESCRIPTION", self.__pd)
        response = self.__model.generate_content(prompt)

        contracts_begin = '<contracts>'
        contract_end = '</contracts>'

        exp_begin = '<explanation>'
        exp_end = '</explanation>'

        if self.__explanation:
            if response is not None and len(response.text) > 0:
                return (response.text[response.text.find(contracts_begin) + len(contracts_begin) + 1
                                :response.text.find(contract_end)].strip('\n'),
                        response.text[response.text.find(exp_begin) + len(exp_begin) + 1:
                                response.text.find(exp_end)].strip('\n'), list(zip(batch, batch_exps)))
        else:
            if response is not None and len(response.text) > 0:
                return (response.text[response.text.find(contracts_begin) + len(contracts_begin) + 1
                                :response.text.find(contract_end)].strip('\n'), '', list(zip(batch, batch_exps)))
            
    def sphinx(self, contracts: str, verification_plan: str) -> Union[str, tuple]:
        """
        Sphinx is the revision engine of contracts, it is the last step in Nectron's pipeline, it employs a content
        augmented process to revise the generated contracts, which subsequently mitigate logical inconsistencies.
        :param contracts: The set of contracts that were generated by Pyramid.
        :param verification_plan: The verification plan constructed from ToTs.
        :return: This method returns the revised set of contracts and the LLM explanation for its revision decisions.
        """
        prompt = self.__prompts['sphinx'].replace('%VPLAN%', verification_plan).replace('INPUT_CONTRACTS', contracts).replace("PROGRAM_DESCRIPTION", self.__pd)
        response = self.__model.generate_content(prompt)

        contracts_begin = '<acsl_revised>'
        contract_end = '</acsl_revised>'

        exp_begin = '<explanation>'
        exp_end = '</explanation>'

        if self.__explanation:
            if response is not None and len(response.text) > 0:
                return (response.text[response.text.find(contracts_begin) + len(contracts_begin) + 1
                                    :response.text.find(contract_end)].strip('\n'),
                        response.text[
                        response.text.find(exp_begin) + len(exp_begin) + 1:
                        response.text.find(exp_end)].strip('\n'))
        else:
            if response is not None and len(response.text) > 0:
                return (response.text[response.text.find(contracts_begin) + len(contracts_begin) + 1
                                    :response.text.find(contract_end)].strip('\n'), '')

    def __example_modularity(self):
        return self.__prompts['syntax_correction'].replace('\n<modular_example>\n', '').replace('\n</modular_example>\n', '')

    def generate_ToT(self,
                     program_description: str,
                     num_app: int
        ) -> str:
        """
        This method is used to interact with the model to generate a Tree-of-Thoughts for the given program description.
        :param program_description: The program's description.
        :param num_app: The number of distinct approaches to be generated.
        :return:
        """
        if self.__quick_check(description=program_description):
            self.__pd = program_description
            prompt = self.__prompts["ToT"].replace('PROGRAM_DESCRIPTION', program_description).replace("%NUMBER%", str(num_app))
            response = self.__model.generate_content(prompt).text

            begin_tag = "<approach>"
            end_tag = "</approach>"

            evaluation_prompt = self.__prompts["ToT_eval"].replace('PROGRAM_DESCRIPTION', program_description)

            trees = ''
            for item in response[response.find(begin_tag) + len(begin_tag):].strip('\n').split(begin_tag):
                approach = item[:item.find(end_tag)].strip('\n')
                trees += f"{begin_tag}\n{approach}\n{end_tag}\n\n"

            evaluation_prompt = evaluation_prompt.replace('%%INSERT_APPROACHES%%', trees.strip('\n'))
            evaluation_response = self.__model.generate_content(evaluation_prompt).text

            obt = "<optimal_approach>"
            oet = "</optimal_approach>"

            optimal_approach = evaluation_response[evaluation_response.find(obt)+len(obt):evaluation_response.find(oet)]
            optimal_approach = optimal_approach.replace('**', '')

            return optimal_approach
        
    def reconstruct_program(self, corrupted_code: str, specification: str) -> str:
        """
        This method is used to prompt the model to reconstruct and restore the non-corrupted program using the specification.
        :param corrupt_code: The corrupt code
        :param specification: the ACSL specification to be used to eliminate the semantic noise.
        :return:
        """
        prompt = self.__prompts["reconstruct"].replace('CORRUPTED_CODE', corrupted_code).replace('ACSL_SPECIFICATION', specification)
        response = self.__model.generate_content(prompt)

        recon_begin = '<reconstructed>'
        recon_end = '</reconstructed>'

        if response is not None and len(response.text) > 0:
            return response.text[response.text.find(recon_begin) + len(recon_begin) + 1
                            :response.text.find(recon_end)].strip('\n')
        
    def generate_zero_shot(self, description: str) -> str:
        """
        This method is used to prompt the model to generate the acsl specification given a (zero shot) description of the program.
        :param description: the description of the program.
        :return:
        """
        prompt = self.__prompts["zero_shot"].replace('PROGRAM_DESCRIPTION', description)
        response = self.__model.generate_content(prompt)

        recon_begin = '<acsl>'
        recon_end = '</acsl>'

        if response is not None and len(response.text) > 0:
            return response.text[response.text.find(recon_begin) + len(recon_begin) + 1
                            :response.text.find(recon_end)].strip('\n')


if __name__ == '__main__':

    ins = NectronGemini()
    ins.InitClient(api_key="YOUR_GEMINI_API_KEY")
    description = "A program that takes in an integer x and returns x + 1."
    op = ins.generate_srs(description)
    print(op[0])
