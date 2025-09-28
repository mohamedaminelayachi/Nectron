import os
import platform
import pandas as pd
import yaml
import json
import ctypes
import dearpygui.dearpygui as dpg

from google.api_core.exceptions import InvalidArgument
from openai import AuthenticationError
from .macros import *
from .utilities import *
from .nectron import Nectron, NonCompilableNAR


class NectronApp:
    """
    The NectronApp is the only class used to instantiate the user interface that facilitates the interaction with the
    Nectron system.
    """
    def __init__(self):
        dpg.create_context()
        self.__window = dpg.window(tag=MAIN_WINDOW)
        self.__menu_bar = dpg.menu_bar()
        self.__file_menu = dpg.menu(label='File')
        self.__edit_menu = dpg.menu(label='Edit')
        self.__view_menu = dpg.menu(label='View')

        with dpg.font_registry():

            self.__default_font = dpg.add_font("scripts/app_assets/JetBrainsMono-Regular.ttf", 26)
            self.__second_font = dpg.add_font("scripts/app_assets/JetBrainsMono-Regular.ttf", 24)

        self.__current_file = None
        self.__current_state = NectronState(*(['']*len(NectronState.__dict__['__annotations__'])))
        if os.path.exists('./settings/settings.json'):
            self.__configuration = read_nectron_settings('./settings/settings.json')
        else:
            self.__configuration = {
                'api_key': '',
                'backend_model': 'Gemini',
                'model_identifier': 'gemini-2.5-flash',
                'reflective_reasoning_intensity': 1,
                'default_export_extension': 'JSON',
                'explanation': False,
                'program_description': True,
                'acsl_contracts': True,
                'srs': True,
                'nar_representation': True,
                'seeds': True
            }

            with open('./settings/settings.json', 'w') as fp:
                json.dump(self.__configuration, fp)

        self.__nectron = None
        self.__rr_intensity_scale = 3
        self.__samples = int(self.__configuration['reflective_reasoning_intensity'])
        self.__current_state.suggestions = [''] * (self.__samples + 2)
        self.__undo_redo_stack = []
        self.__undo_redo_stack.append(self.__current_state)
        self.__current_index = 0
        self.__current_suggestion_index = 0
        self.__version = 1.0

        self.__default_gemini = 'gemini-2.5-flash'
        self.__default_openrouter = 'openai/gpt-oss-20b'

    def __create_menu(self):
        with self.__menu_bar:
            with self.__file_menu:
                dpg.add_menu_item(tag=LOAD_MENU_ITEM, label='Load', callback=self.__load_state, default_value=True)
                with dpg.tooltip(LOAD_MENU_ITEM, delay=0.5):
                    dpg.add_text('Ctrl + L')

                dpg.add_menu_item(tag=SAVE_MENU_ITEM, label='Save', callback=self.__save_state)
                with dpg.tooltip(SAVE_MENU_ITEM, delay=0.5):
                    dpg.add_text('Ctrl + S')

                dpg.add_menu_item(tag=SAVE_AS_MENU_ITEM, label='Save as', callback=self.__save_state_as)
                with dpg.tooltip(SAVE_AS_MENU_ITEM, delay=0.5):
                    dpg.add_text('Shift + S')

                with dpg.menu(label='Export'):
                    dpg.add_menu_item(tag=EXPORT_DATA_ITEM, label='Export Data', callback=self.__export_data,
                                      default_value=True)

                    with dpg.tooltip(EXPORT_DATA_ITEM, delay=0.5):
                        dpg.add_text('Ctrl + E')

                    dpg.add_menu_item(tag=EXPORT_STATE_ITEM, label='Export State as Data', default_value=True,
                                      callback=self.__export_state_as_data)

                    with dpg.tooltip(EXPORT_STATE_ITEM, delay=0.5):
                        dpg.add_text('Ctrl + R')

                dpg.add_menu_item(tag=SETTINGS_MENU_ITEM, label='Settings', callback=self.__settings,
                                  default_value=True)

                with dpg.tooltip(SETTINGS_MENU_ITEM, delay=0.5):
                    dpg.add_text('Alt + S')

            with self.__edit_menu:

                dpg.add_menu_item(tag=UNDO_MENU_ITEM, label='Undo', callback=self.__undo)
                with dpg.tooltip(UNDO_MENU_ITEM, delay=0.5):
                    dpg.add_text('Ctrl + Z')

                dpg.add_menu_item(tag=REDO_MENU_ITEM, label='Redo', callback=self.__redo)
                with dpg.tooltip(REDO_MENU_ITEM, delay=0.5):
                    dpg.add_text('Ctrl + Y')

                dpg.add_menu_item(tag=CLEAR_MENU_ITEM, label='Clear', callback=self.__clear)
                with dpg.tooltip(CLEAR_MENU_ITEM, delay=0.5):
                    dpg.add_text('Ctrl + N')

            with self.__view_menu:

                self.__srs_menu_view = dpg.add_menu_item(tag=SRS_MENU_ITEM, label="Sequential Reasoning Strategy",
                                                         check=True, callback=self.__srs_log)
                with dpg.tooltip(SRS_MENU_ITEM, delay=0.5):
                    dpg.add_text('Alt + 1')
                self.__nar_menu_view = dpg.add_menu_item(tag=NAR_MENU_ITEM, label="NAR Generation", check=True,
                                                         callback=self.__nar_generator_log)
                with dpg.tooltip(NAR_MENU_ITEM, delay=0.5):
                    dpg.add_text('Alt + 2')
                self.__sc_menu_view = dpg.add_menu_item(tag=SC_MENU_ITEM, label="Contract Seeds", check=True,
                                                        callback=self.__contracts_seeds_log)
                with dpg.tooltip(SC_MENU_ITEM, delay=0.5):
                    dpg.add_text('Alt + 3')

            dpg.add_menu_item(tag=ABOUT_MENU_ITEM, label='About', callback=self.__about, default_value=True)

    def __inference_distributor(self):
        if dpg.does_item_exist(PD_FIELD):
            dpg.set_value(PD_FIELD, self.__current_state.program_description)
        if dpg.does_item_exist(CONTRACT_FIELD):
            dpg.set_value(CONTRACT_FIELD, self.__current_state.acsl_contracts)
            dpg.set_value(REFINEMENT_EXPLANATION, self.__current_state.refinement_exp)
            dpg.configure_item(CONTRACT_TOOLTIP, show=True)
        if dpg.does_item_exist(SRS_VIEW):
            dpg.set_value(SRS_VIEW, self.__current_state.srs)
            dpg.set_value(SRS_EXPLANATION, self.__current_state.srs_exp)
        if dpg.does_item_exist(NAR_VIEW):
            dpg.set_value(NAR_VIEW, self.__current_state.nar_representation)
            dpg.set_value(NAR_EXPLANATION, self.__current_state.nar_gen_exp)
        if dpg.does_item_exist(SC_VIEW):
            dpg.set_value(SC_VIEW, self.__current_state.seeds)

        for item in reversed(range(self.__rr_intensity_scale + 2)):
            if dpg.does_item_exist(f'CIRCLE_{item}'):
                dpg.delete_item(f'CIRCLE_{item}')

        offset = 20
        init_x = 1167
        for item in reversed(range(len(self.__current_state.suggestions))):
            if self.__build_state__().is_full() and item == 0:
                dpg.draw_circle(tag=f'CIRCLE_{item}', radius=5, center=[init_x - offset, 490],
                                fill=(255, 255, 255, 255), parent=MAIN_WINDOW)
            else:
                dpg.draw_circle(tag=f'CIRCLE_{item}', radius=5, center=[init_x - offset, 490], fill=(0, 0, 0, -255),
                                parent=MAIN_WINDOW)
            init_x -= offset

        self.__current_suggestion_index = 0

    def __clear(self):
        if self.__build_state__().is_full():
            self.__current_state = NectronState(*([''] * len(NectronState.__dict__['__annotations__'])))
            self.__current_file = None
            self.__current_state.suggestions = [''] * (self.__samples + 2)
            self.__undo_redo_stack.append(self.__current_state)
            self.__current_index += 1
            self.__inference_distributor()
        else:
            with dpg.window(popup=True, modal=True):
                dpg.add_text(default_value='Nothing to clear, already empty.', wrap=600)

    def __load_ok(self, sender, data):
        self.__current_file = data['file_path_name']
        self.__current_state = read_nectron_file(data['file_path_name'])

        if self.__current_state is None:
            if dpg.does_item_exist(NECTRON_LOADING_FAILURE):
                dpg.delete_item(NECTRON_LOADING_FAILURE)
            error = 'Invalid state file was provided. Please check the validity of the file and try again.'
            with dpg.window(tag=NECTRON_LOADING_FAILURE, no_collapse=True, pos=(300, 400)):
                dpg.add_text(default_value=error, wrap=600)
        else:
            self.__undo_redo_stack.append(self.__current_state)
            self.__current_index += 1
            self.__inference_distributor()
        
        dpg.set_value(LOAD_MENU_ITEM, True)

        if dpg.does_item_exist(FILE_DIALOG):
            dpg.delete_item(FILE_DIALOG)


    @staticmethod
    def __cancel_load():
        if dpg.does_item_exist(FILE_DIALOG):
            dpg.delete_item(FILE_DIALOG)

        dpg.set_value(LOAD_MENU_ITEM, True)

    def __load_state(self):
        if dpg.get_value(LOAD_MENU_ITEM):
            dpg.set_value(LOAD_MENU_ITEM, False)
            with dpg.file_dialog(tag=FILE_DIALOG, show=True, width=900, height=600, callback=self.__load_ok,
                                 cancel_callback=self.__cancel_load, modal=True, label='Load'):
                dpg.add_file_extension(".json")
        else:
            dpg.delete_item(FILE_DIALOG)

    def __build_state__(self):
        program_description = nullable_processor(dpg.get_value(PD_FIELD))
        acsl_contracts = nullable_processor(dpg.get_value(CONTRACT_FIELD))
        refinement_exp = nullable_processor(dpg.get_value(REFINEMENT_EXPLANATION))

        if dpg.does_item_exist(SRS_VIEW):
            srs = nullable_processor(dpg.get_value(SRS_VIEW))
            srs_exp = dpg.get_value(SRS_EXPLANATION)
        else:
            srs, srs_exp = '', ''

        if dpg.does_item_exist(NAR_VIEW):
            nar_representation = nullable_processor(dpg.get_value(NAR_VIEW))
            nar_gen_exp = nullable_processor(dpg.get_value(NAR_EXPLANATION))
        else:
            nar_representation, nar_gen_exp = '', ''

        if dpg.does_item_exist(SC_VIEW):
            seeds = nullable_processor(dpg.get_value(SC_VIEW))
        else:
            seeds = ''

        state = NectronState(
            program_description=program_description,
            acsl_contracts=acsl_contracts,
            seeds=seeds,
            srs=srs,
            nar_representation=nar_representation,
            srs_exp=srs_exp,
            nar_gen_exp=nar_gen_exp,
            refinement_exp=refinement_exp,
            suggestions=self.__current_state.suggestions,
        )

        return state

    def __save_state(self):
        if dpg.does_item_exist(SAVE_FILE_DIALOG):
            dpg.delete_item(SAVE_FILE_DIALOG)
        state = self.__build_state__()
        if self.__current_file is not None and not os.path.exists(self.__current_file):
            with dpg.file_dialog(tag=SAVE_FILE_DIALOG, show=True, width=900, height=600,
                                 callback=self.__save_file_ok, label='Save', modal=True):
                dpg.add_file_extension(".json")
        if state != self.__current_state:
            if self.__current_file is None or not os.path.exists(self.__current_file):
                with dpg.file_dialog(tag=SAVE_FILE_DIALOG, show=True, width=900, height=600,
                                     callback=self.__save_file_ok, label='Save', modal=True):
                    dpg.add_file_extension(".json")
            else:
                if os.path.exists(self.__current_file):
                    with open(self.__current_file, 'w') as fp:
                        json.dump((state @ self.__current_state).to_dict(), fp, indent=4)
                else:
                    with dpg.file_dialog(tag=SAVE_FILE_DIALOG, show=True, width=900, height=600,
                                         callback=self.__save_file_ok, label='Save', modal=True):
                        dpg.add_file_extension(".json")

    def __save_state_as(self):
        if dpg.does_item_exist(SAVE_FILE_DIALOG):
            dpg.delete_item(SAVE_FILE_DIALOG)

        if self.__build_state__().is_full():
            with dpg.file_dialog(tag=SAVE_FILE_DIALOG, show=True, width=900, height=600,
                                 callback=self.__save_file_ok, label='Save as', modal=True):
                dpg.add_file_extension(".json")

    def __save_file_ok(self, sender, data):
        self.__current_file = data['file_path_name']
        self.__current_state = self.__build_state__() @ self.__current_state
        if self.__current_state is not None:
            with open(self.__current_file, 'w') as fp:
                json.dump(self.__current_state.to_dict(), fp, indent=4)

    def __view_shortcuts(self):
        if dpg.is_key_pressed(dpg.mvKey_1) and dpg.get_value(SRS_MENU_ITEM) is False:
            dpg.set_value(SRS_MENU_ITEM, True)
            self.__srs_log()
        elif dpg.is_key_pressed(dpg.mvKey_1) and dpg.get_value(SRS_MENU_ITEM) is True:
            dpg.set_value(SRS_MENU_ITEM, False)
            self.__srs_log()
        elif dpg.is_key_pressed(dpg.mvKey_2) and dpg.get_value(NAR_MENU_ITEM) is False:
            dpg.set_value(NAR_MENU_ITEM, True)
            self.__nar_generator_log()
        elif dpg.is_key_pressed(dpg.mvKey_2) and dpg.get_value(NAR_MENU_ITEM) is True:
            dpg.set_value(NAR_MENU_ITEM, False)
            self.__nar_generator_log()
        elif dpg.is_key_pressed(dpg.mvKey_3) and dpg.get_value(SC_MENU_ITEM) is False:
            dpg.set_value(SC_MENU_ITEM, True)
            self.__contracts_seeds_log()
        elif dpg.is_key_pressed(dpg.mvKey_3) and dpg.get_value(SC_MENU_ITEM) is True:
            dpg.set_value(SC_MENU_ITEM, False)
            self.__contracts_seeds_log()
        elif dpg.is_key_pressed(dpg.mvKey_S) and dpg.get_value(SETTINGS_MENU_ITEM) is False:
            if dpg.does_item_exist(SETTINGS_VIEW):
                dpg.delete_item(SETTINGS_VIEW)
            dpg.set_value(SETTINGS_MENU_ITEM, True)
        elif dpg.is_key_pressed(dpg.mvKey_S) and dpg.get_value(SETTINGS_MENU_ITEM) is True:
            self.__settings()

    def __shortcuts(self):
        if dpg.is_key_pressed(dpg.mvKey_G):
            self.__generate()
        elif dpg.is_key_pressed(dpg.mvKey_L) and dpg.get_value(LOAD_MENU_ITEM) is False:
            if dpg.does_item_exist(FILE_DIALOG):
                dpg.delete_item(FILE_DIALOG)
            dpg.set_value(LOAD_MENU_ITEM, True)
        elif dpg.is_key_pressed(dpg.mvKey_L) and dpg.get_value(LOAD_MENU_ITEM) is True:
            self.__load_state()
        elif dpg.is_key_pressed(dpg.mvKey_S):
            self.__save_state()
        elif dpg.is_key_pressed(dpg.mvKey_N):
            self.__clear()
        elif dpg.is_key_pressed(dpg.mvKey_E):
            self.__export_data()
        elif dpg.is_key_pressed(dpg.mvKey_R):
            self.__export_state_as_data()
        elif dpg.is_key_pressed(dpg.mvKey_Z):
            self.__undo()
        elif dpg.is_key_pressed(dpg.mvKey_Y):
            self.__redo()

    def __shift_shortcuts(self):
        if dpg.is_key_pressed(dpg.mvKey_S):
            self.__save_state_as()

    @staticmethod
    def __on_close_settings():
        dpg.set_value(SETTINGS_MENU_ITEM, True)
        if dpg.does_item_exist(SETTINGS_VIEW):
            dpg.delete_item(SETTINGS_VIEW)

    def __settings(self):
        if dpg.get_value(SETTINGS_MENU_ITEM):
            dpg.set_value(SETTINGS_MENU_ITEM, False)
            with dpg.window(tag=SETTINGS_VIEW, label='Settings', pos=(85, 230), width=1000, height=510,
                            no_resize=True, no_collapse=True, modal=True,
                            on_close=self.__on_close_settings):
                dpg.add_text(tag=API_KEY_TEXT, default_value='API Key')
                dpg.add_input_text(tag=API_KEY_FIELD, hint="Enter the API Key", width=984,
                                   default_value=self.__configuration['api_key'], password=True)
                dpg.add_text(default_value='Backend Model')
                dpg.add_radio_button(['Gemini', 'OpenRouter'], horizontal=True,
                                     indent=20, tag=MODEL_RADIO,
                                     default_value=self.__configuration['backend_model'])
                dpg.add_text(default_value='Model Identifier', pos=(350, 112))
                dpg.add_input_text(tag=MODEL_IDENTIFIER_FIELD, hint="Enter the Model's Identifier", 
                                   width=340, pos=(350, 148), default_value=self.__configuration['model_identifier'])
                dpg.add_text(default_value='Generate Explanation', pos=(756, 112))
                dpg.add_checkbox(tag=GENERATE_EXPLANATION_CHECKBOX,
                                 default_value=self.__configuration['explanation'], pos=(756, 148))
                dpg.add_text(default_value='Reflective Reasoning Intensity (Higher Intensity, Slower Inference)')
                dpg.add_slider_int(tag=REFLECTIVE_REASONING_INTENSITY, min_value=0, 
                                   max_value=self.__rr_intensity_scale,
                                     default_value=self.__configuration['reflective_reasoning_intensity'],
                                     width=984)
                dpg.add_text(default_value='Default Export Extension')
                dpg.add_radio_button(['JSON', 'CSV', 'YAML', 'XML'], horizontal=True,
                                     indent=20, tag=EXTENSION_RADIO,
                                     default_value=self.__configuration['default_export_extension'])
                dpg.add_text(default_value='Data-Export Entries')
                dpg.add_checkbox(tag=PDCBOX, label='Program Description', indent=20,
                                 default_value=self.__configuration['program_description'])
                dpg.add_checkbox(tag=ACSLBOX, label='ACSL Contracts', pos=(320, 364),
                                 default_value=self.__configuration['acsl_contracts'])
                dpg.add_checkbox(tag=SRSBOX, label='Sequential Reasoning Strategy', pos=(550, 364),
                                 default_value=self.__configuration['srs'])
                dpg.add_checkbox(tag=NARBOX, label='NAR', indent=20, pos=(50, 400),
                                 default_value=self.__configuration['nar_representation'])
                dpg.add_checkbox(tag=SCBOX, label='Seeds', pos=(320, 400),
                                 default_value=self.__configuration['seeds'])
                dpg.add_button(label='OK', width=40, pos=(420, 460), callback=self.__build_configuration)
                dpg.add_button(label='Cancel', pos=(480, 460), callback=self.__cancel_settings_callback)

        else:
            dpg.delete_item(SETTINGS_VIEW)

    def __indexing_bullets_draw(self):
        previous_samples = self.__samples + 2
        if self.__samples == 0:
            for item in reversed(range(previous_samples)):
                if dpg.does_item_exist(f'CIRCLE_{item}'):
                    dpg.delete_item(f'CIRCLE_{item}')

            offset = 20
            init_x = 1167
            dpg.draw_circle(tag=f'CIRCLE_1', radius=5, center=[init_x - offset, 490],
                            fill=(0, 0, 0, -255), parent=MAIN_WINDOW)
            init_x -= offset
            dpg.draw_circle(tag=f'CIRCLE_0', radius=5, center=[init_x - offset, 490],
                            fill=(255, 255, 255, 255), parent=MAIN_WINDOW)

            self.__current_suggestion_index = 0

        elif self.__samples > 0:
            offset = 20
            init_x = 1167
            for item in reversed(range(self.__samples + 2)):
                if dpg.does_item_exist(f'CIRCLE_{item}'):
                    dpg.delete_item(f'CIRCLE_{item}')
                if self.__build_state__().is_full() and item == 0:
                    dpg.draw_circle(tag=f'CIRCLE_{item}', radius=5, center=[init_x - offset, 490],
                                    fill=(255, 255, 255, 255), parent=MAIN_WINDOW)
                else:
                    dpg.draw_circle(tag=f'CIRCLE_{item}', radius=5, center=[init_x - offset, 490], fill=(0, 0, 0, -255),
                                    parent=MAIN_WINDOW)
                init_x -= offset

            self.__current_suggestion_index = 0
            dpg.configure_item(NEXT_SUGGESTION, enabled=True)
            dpg.configure_item(PREVIOUS_SUGGESTION, enabled=True)

    def __build_configuration(self):
        configuration = {
            'api_key': dpg.get_value(API_KEY_FIELD),
            'backend_model': dpg.get_value(MODEL_RADIO),
            'model_identifier': dpg.get_value(MODEL_IDENTIFIER_FIELD),
            'reflective_reasoning_intensity': dpg.get_value(REFLECTIVE_REASONING_INTENSITY),
            'default_export_extension': dpg.get_value(EXTENSION_RADIO),
            'explanation': dpg.get_value(GENERATE_EXPLANATION_CHECKBOX),
            'program_description': dpg.get_value(PDCBOX),
            'acsl_contracts': dpg.get_value(ACSLBOX),
            'srs': dpg.get_value(SRSBOX),
            'nar_representation': dpg.get_value(NARBOX),
            'seeds': dpg.get_value(SCBOX)
        }

        if self.__configuration != configuration:
            with open('./settings/settings.json', 'w') as fp:
                json.dump(configuration, fp, indent=4)
            self.__configuration = configuration

        dpg.set_value(SETTINGS_MENU_ITEM, True)
        dpg.delete_item(SETTINGS_VIEW)
        self.__samples = int(self.__configuration['reflective_reasoning_intensity'])
        self.__indexing_bullets_draw()

    @staticmethod
    def __cancel_settings_callback():
        dpg.set_value(SETTINGS_MENU_ITEM, True)
        dpg.delete_item(SETTINGS_VIEW)

    def __create_main_components(self):
        dpg.add_text("Program Description")
        dpg.add_input_text(tag=PD_FIELD, width=1160, height=400, multiline=True,
                           tab_input=True, on_enter=True)
        dpg.add_button(label='Generate', tag=GENERATE_BUTTON, callback=self.__generate, pos=(1064, 37))
        dpg.add_text("Refined Contracts")
        dpg.add_input_text(tag=CONTRACT_FIELD,
                           width=1160, height=400, multiline=True,
                           readonly=True)
        dpg.add_progress_bar(tag=PROGRESS_BAR, width=1150, height=5, pos=(12, 905))
        dpg.add_button(label=' > ', pos=(1124, 480), tag=NEXT_SUGGESTION, callback=self.__next_suggestion)
        dpg.add_button(label=' < ', pos=(1077, 480), tag=PREVIOUS_SUGGESTION, callback=self.__previous_suggestion)
        with dpg.tooltip(tag=CONTRACT_TOOLTIP, delay=0.5, parent=CONTRACT_FIELD):
            dpg.add_text(tag=REFINEMENT_EXPLANATION,
                         default_value='', wrap=1000)

        with dpg.tooltip(delay=1, parent=NEXT_SUGGESTION):
            dpg.add_text(default_value='Next Suggestion', wrap=1000)

        with dpg.tooltip(delay=1, parent=PREVIOUS_SUGGESTION):
            dpg.add_text(default_value='Previous Suggestion', wrap=1000)

        offset = 20
        init_x = 1167
        for item in reversed(range(self.__samples+2)):
            dpg.draw_circle(tag=f'CIRCLE_{item}', radius=5, center=[init_x - offset, 490], fill=(0, 0, 0, -255))
            init_x -= offset

        if dpg.get_value(REFINEMENT_EXPLANATION) == '':
            dpg.configure_item(CONTRACT_TOOLTIP, show=False)
        else:
            dpg.configure_item(CONTRACT_TOOLTIP, show=True)

        if self.__current_state is not None:
            dpg.set_value(CONTRACT_FIELD, self.__current_state.acsl_contracts)
            dpg.set_value(REFINEMENT_EXPLANATION, self.__current_state.refinement_exp)

        with dpg.tooltip(GENERATE_BUTTON, delay=0.5):
            dpg.add_text('Ctrl + G')

    def __next_suggestion(self):
        all_circles_exist = True
        for item in reversed(range(len(self.__current_state.suggestions))):
            if not dpg.does_item_exist(f'CIRCLE_{item}'):
                all_circles_exist = False

        if 0 <= self.__current_suggestion_index + 1 < len(self.__current_state.suggestions) and all_circles_exist:
            dpg.configure_item(f'CIRCLE_{self.__current_suggestion_index}', fill=(0, 0, 0, -255))
            self.__current_suggestion_index += 1

            if len(self.__current_state.suggestions[self.__current_suggestion_index]) > 0:
                dpg.set_value(CONTRACT_FIELD, self.__current_state.suggestions[self.__current_suggestion_index][0])
                dpg.set_value(REFINEMENT_EXPLANATION, self.__current_state.suggestions[self.__current_suggestion_index][1])
            dpg.configure_item(f'CIRCLE_{self.__current_suggestion_index}', fill=(255, 255, 255, 255))

    def __previous_suggestion(self):
        all_circles_exist = True
        for item in reversed(range(len(self.__current_state.suggestions))):
            if not dpg.does_item_exist(f'CIRCLE_{item}'):
                all_circles_exist = False

        if 0 <= self.__current_suggestion_index - 1 < len(self.__current_state.suggestions) and all_circles_exist:
            dpg.configure_item(f'CIRCLE_{self.__current_suggestion_index}', fill=(0, 0, 0, -255))
            self.__current_suggestion_index -= 1
            if len(self.__current_state.suggestions[self.__current_suggestion_index]) > 0:
                dpg.set_value(CONTRACT_FIELD, self.__current_state.suggestions[self.__current_suggestion_index][0])
                dpg.set_value(REFINEMENT_EXPLANATION, self.__current_state.suggestions[self.__current_suggestion_index][1])
            dpg.configure_item(f'CIRCLE_{self.__current_suggestion_index}', fill=(255, 255, 255, 255))

    def __export_data(self):
        
        if self.__build_state__().is_full():
            print('Yes')
            if dpg.get_value(EXPORT_DATA_ITEM):
                dpg.set_value(EXPORT_DATA_ITEM, False)
                with dpg.file_dialog(tag=EXPORT_FILE_DIALOG, show=True, width=900, height=600,
                                    callback=self.__export_data_ok,label='Export',
                                    cancel_callback=self.__cancel_export, modal=True):
                    extensions = ['JSON', 'CSV', 'YAML', 'XML']
                    dpg.add_file_extension(f".{self.__configuration['default_export_extension'].lower()}")
                    for extension in extensions:
                        if self.__configuration['default_export_extension'] != extension:
                            dpg.add_file_extension(f".{extension.lower()}")
            else:
                dpg.delete_item(EXPORT_FILE_DIALOG)
                dpg.set_value(EXPORT_DATA_ITEM, True)
        else:
            with dpg.window(popup=True, modal=True):
                dpg.add_text(default_value='Nothing to export, state is empty.', wrap=600)

    def __export_data_ok(self, sender, fdata):
        file_path = fdata['file_path_name']
        data = {}
        state = self.__build_state__() @ self.__current_state
        if self.__configuration['program_description']:
            data['program_description'] = state.program_description
        if self.__configuration['acsl_contracts']:
            data['acsl_contracts'] = state.acsl_contracts
        if self.__configuration['srs']:
            data['sequential_reasoning_strategy'] = state.srs
        if self.__configuration['nar_representation']:
            data['nar_representation'] = state.nar_representation
        if self.__configuration['seeds']:
            data['seeds'] = state.seeds

        extension = fdata['current_filter'].strip('.')
        if extension == 'json':
            with open(file_path, 'w') as fp:
                json.dump(data, fp, indent=4)
        elif extension == 'csv':
            pd.DataFrame([data]).to_csv(file_path, index=False, columns=['program_description',
                                        'acsl_contracts',
                                        'sequential_reasoning_strategy',
                                        'nar_representation',
                                        'seeds'])
        elif extension == 'yaml':
            with open(file_path, 'w') as fp:
                yaml.dump(data, fp, default_flow_style=False)
        elif extension == 'xml':
            pd.DataFrame([data]).to_xml(file_path, index=False, attr_cols=['program_description',
                                        'acsl_contracts',
                                        'sequential_reasoning_strategy',
                                        'nar_representation',
                                        'seeds'])

        dpg.delete_item(EXPORT_FILE_DIALOG)
        dpg.set_value(EXPORT_DATA_ITEM, True)

    @staticmethod
    def __cancel_export():
        dpg.delete_item(EXPORT_FILE_DIALOG)
        dpg.set_value(EXPORT_DATA_ITEM, True)

    def __export_state_as_data(self):

        if self.__build_state__().is_full():
            if dpg.get_value(EXPORT_DATA_ITEM):
                dpg.set_value(EXPORT_DATA_ITEM, False)
                with dpg.file_dialog(tag=EXPORT_FILE_DIALOG, show=True, width=900, height=600,
                                    callback=self.__export_state_as_data_ok, label='Export',
                                    cancel_callback=self.__cancel_export, modal=True):
                    extensions = ['JSON', 'CSV', 'YAML']
                    dpg.add_file_extension(f".{self.__configuration['default_export_extension'].lower()}")
                    for extension in extensions:
                        if self.__configuration['default_export_extension'] != extension:
                            dpg.add_file_extension(f".{extension.lower()}")
            else:
                dpg.delete_item(EXPORT_FILE_DIALOG)
                dpg.set_value(EXPORT_DATA_ITEM, True)
        else:
            with dpg.window(popup=True, modal=True):
                dpg.add_text(default_value='Nothing to export, state is empty.', wrap=600)

    def __export_state_as_data_ok(self, sender, fdata):
        file_path = fdata['file_path_name']
        state = self.__build_state__() @ self.__current_state
        extension = fdata['current_filter'].strip('.')
        if extension == 'json':
            data = state.to_dict()
            with open(file_path, 'w') as fp:
                json.dump(data, fp, indent=4)
        elif extension == 'csv':
            data = state.to_dict(unroll_suggestions=True)
            pd.DataFrame([data]).to_csv(file_path, index=False, columns=list(data.keys()))
        elif extension == 'yaml':
            data = state.to_dict(unroll_suggestions=True)
            with open(file_path, 'w') as fp:
                yaml.dump(data, fp, default_flow_style=False)

        dpg.delete_item(EXPORT_FILE_DIALOG)
        dpg.set_value(EXPORT_DATA_ITEM, True)

    def __srs_log(self):
        if dpg.get_viewport_width() == 1175:
            dpg.set_viewport_width(1895)
        if dpg.get_value(SRS_MENU_ITEM):
            if dpg.does_item_exist(NAR_VIEW):
                dpg.set_item_pos(NAR_VIEW_LABEL, pos=[1190, 480])

                if dpg.does_item_exist(SC_VIEW):
                    dpg.set_item_height(NAR_VIEW, 740)
                else:
                    dpg.set_item_height(NAR_VIEW, 400)

                dpg.set_item_pos(NAR_VIEW, pos=[1190, 516])

                dpg.add_text('Sequential Reasoning Strategy', pos=(1190, 40), parent=MAIN_WINDOW, tag=SRS_VIEW_LABEL)
                dpg.add_input_text(tag=SRS_VIEW, readonly=True, multiline=True, width=695, height=400,
                                   parent=MAIN_WINDOW, pos=(1190, 76))
            else:
                height = 840
                if dpg.does_item_exist(SC_VIEW):
                    height = 1180
                dpg.add_text('Sequential Reasoning Strategy', pos=(1190, 40), parent=MAIN_WINDOW, tag=SRS_VIEW_LABEL)
                dpg.add_input_text(tag=SRS_VIEW, readonly=True, multiline=True, width=695, height=height,
                                   parent=MAIN_WINDOW, pos=(1190, 76))

            with dpg.tooltip(tag=SRS_TOOLTIP, delay=0.5, parent=SRS_VIEW):
                dpg.add_text(tag=SRS_EXPLANATION,
                             default_value="Sequential Reasoning Strategy", wrap=700)

            if dpg.get_value(SRS_EXPLANATION) == '':
                dpg.configure_item(SRS_TOOLTIP, show=False)
            else:
                dpg.configure_item(SRS_TOOLTIP, show=True)

            if self.__current_state is not None:
                dpg.set_value(SRS_VIEW, self.__current_state.srs)
                dpg.set_value(SRS_EXPLANATION, self.__current_state.srs_exp)
        else:
            if dpg.does_item_exist(NAR_VIEW):
                dpg.set_item_pos(NAR_VIEW_LABEL, pos=[1190, 40])
                if dpg.does_item_exist(SC_VIEW):
                    dpg.set_item_height(NAR_VIEW, 1180)
                else:
                    dpg.set_item_height(NAR_VIEW, 840)
                dpg.set_item_pos(NAR_VIEW, pos=[1190, 76])
            else:
                dpg.set_viewport_width(1175)

            dpg.delete_item(SRS_VIEW_LABEL)
            dpg.delete_item(SRS_VIEW)
            dpg.delete_item(SRS_TOOLTIP)

    def __nar_generator_log(self):
        if dpg.get_viewport_width() == 1175 and not dpg.does_item_exist(SRS_VIEW):
            dpg.set_viewport_width(1895)

        if dpg.get_value(NAR_MENU_ITEM):
            if dpg.does_item_exist(SRS_VIEW):

                dpg.set_item_height(SRS_VIEW, 400)
                dpg.set_item_pos(SRS_VIEW, pos=[1190, 76])
                height = 400
                if dpg.does_item_exist(SC_VIEW):
                    height = 740

                dpg.add_text('NAR Generation', pos=(1190, 480), parent=MAIN_WINDOW, tag=NAR_VIEW_LABEL)
                dpg.add_input_text(tag=NAR_VIEW, readonly=True, multiline=True, width=695, height=height,
                                   parent=MAIN_WINDOW, pos=(1190, 516))
            else:

                height = 840

                if dpg.does_item_exist(SC_VIEW):
                    height = 1180

                dpg.add_text('NAR Generation', pos=(1190, 40), parent=MAIN_WINDOW, tag=NAR_VIEW_LABEL)
                dpg.add_input_text(tag=NAR_VIEW, readonly=True, multiline=True, width=695, height=height,
                                   parent=MAIN_WINDOW, pos=(1190, 76))

            with dpg.tooltip(tag=NAR_TOOLTIP, delay=0.5, parent=NAR_VIEW):
                dpg.add_text(tag=NAR_EXPLANATION,
                             default_value="NAR Program", wrap=700)

            if dpg.get_value(NAR_EXPLANATION) == '':
                dpg.configure_item(NAR_TOOLTIP, show=False)
            else:
                dpg.configure_item(NAR_TOOLTIP, show=True)

            if self.__current_state is not None:
                dpg.set_value(NAR_VIEW, self.__current_state.nar_representation)
                dpg.set_value(NAR_EXPLANATION, self.__current_state.nar_gen_exp)

        else:
            if dpg.does_item_exist(SRS_VIEW):
                if dpg.does_item_exist(SC_VIEW):
                    dpg.set_item_height(SRS_VIEW, 1180)
                else:
                    dpg.set_item_height(SRS_VIEW, 840)
                dpg.set_item_pos(SRS_VIEW, pos=[1190, 76])
            else:
                dpg.set_viewport_width(1175)

            dpg.delete_item(NAR_VIEW_LABEL)
            dpg.delete_item(NAR_VIEW)
            dpg.delete_item(NAR_TOOLTIP)

    def __contracts_seeds_log(self):
        if dpg.get_viewport_height() == 928:
            dpg.set_viewport_height(1265)

        if dpg.get_value(SC_MENU_ITEM):

            if dpg.does_item_exist(SRS_VIEW) and not dpg.does_item_exist(NAR_VIEW):
                dpg.set_item_height(SRS_VIEW, height=1180)

            if dpg.does_item_exist(NAR_VIEW):
                if dpg.does_item_exist(SRS_VIEW):
                    dpg.set_item_height(NAR_VIEW, height=740)
                else:
                    dpg.set_item_height(NAR_VIEW, height=1180)

            dpg.add_text('Contract Seeds', parent=MAIN_WINDOW, tag=SC_VIEW_LABEL)
            dpg.add_input_text(tag=SC_VIEW, readonly=True, multiline=True, width=1160, height=300,
                               parent=MAIN_WINDOW)

            with dpg.tooltip(tag=SC_TOOLTIP, delay=1, parent=SC_VIEW):
                dpg.add_text(tag=SC_EXPLANATION,
                             default_value="Contract seeds generated by the symbolic engine.", wrap=700)

            if dpg.get_value(SC_EXPLANATION) == '':
                dpg.configure_item(SC_TOOLTIP, show=False)
            else:
                dpg.configure_item(SC_TOOLTIP, show=True)

            if self.__current_state is not None:
                dpg.set_value(SC_VIEW, self.__current_state.seeds)
                # dpg.set_value(SC_EXPLANATION, self.__current_state.nar_cor_exp)

        else:
            if dpg.does_item_exist(SRS_VIEW) and not dpg.does_item_exist(NAR_VIEW):
                dpg.set_item_height(SRS_VIEW, 840)
            elif not dpg.does_item_exist(SRS_VIEW) and dpg.does_item_exist(NAR_VIEW):
                dpg.set_item_height(NAR_VIEW, 840)
            elif dpg.does_item_exist(SRS_VIEW) and dpg.does_item_exist(NAR_VIEW):
                dpg.set_item_height(NAR_VIEW, 400)
                dpg.set_item_height(SRS_VIEW, 400)

            dpg.set_viewport_height(928)

            dpg.delete_item(SC_VIEW_LABEL)
            dpg.delete_item(SC_VIEW)
            dpg.delete_item(SC_TOOLTIP)

    def run(self):
        with self.__window:
            self.__create_menu()
            self.__create_main_components()

        with dpg.theme() as item_theme:
            with dpg.theme_component(dpg.mvAll):
                dpg.add_theme_style(dpg.mvStyleVar_FrameRounding, 3, category=dpg.mvThemeCat_Core)

        dpg.bind_font(self.__default_font)
        dpg.bind_item_font(PD_FIELD, self.__second_font)
        dpg.bind_item_font(CONTRACT_FIELD, self.__second_font)
        dpg.bind_item_theme(MAIN_WINDOW, item_theme)

        with dpg.handler_registry():
            dpg.add_key_down_handler(dpg.mvKey_Control, callback=self.__shortcuts)
            dpg.add_key_down_handler(dpg.mvKey_Alt, callback=self.__view_shortcuts)
            dpg.add_key_down_handler(dpg.mvKey_Shift, callback=self.__shift_shortcuts)

        dpg.create_viewport(title="Nectron", width=1175, height=928, resizable=False,
                            small_icon='scripts/app_assets/nectron_icon_small.ico', large_icon='scripts/app_assets/nectron_icon_large.ico',
                            )

        dpg.setup_dearpygui()

        if platform.system() == 'Windows':
            ctypes.windll.shcore.SetProcessDpiAwareness(2)

        dpg.show_viewport()
        dpg.set_primary_window(MAIN_WINDOW, True)
        dpg.start_dearpygui()
        dpg.destroy_context()

    def __about(self):

        if dpg.does_item_exist(ABOUT_VIEW):
            dpg.delete_item('logo')
            dpg.delete_item(ABOUT_VIEW)
            dpg.set_value(ABOUT_MENU_ITEM, True)

        if dpg.get_value(ABOUT_MENU_ITEM):
            dpg.set_value(ABOUT_MENU_ITEM, False)
            width, height, channels, data = dpg.load_image("scripts/app_assets/nectron_logo_x1.png")

            with dpg.texture_registry(show=False):
                dpg.add_static_texture(width=width, height=height, default_value=data, tag="logo")

            with dpg.window(tag=ABOUT_VIEW, label='About', pos=(170, 250), width=500, height=300,
                            no_resize=True, no_collapse=True, popup=True):
                dpg.add_image("logo", width=220, height=250, pos=(310, 0))
                dpg.add_text(f'Nectron (Version {self.__version:.1f})', pos=(295, 240))
                dpg.add_text('Written by Mohamed Amine Layachi', pos=(230, 270))
                dpg.add_text('Paper - Nectron: Neurosymbolic Implementation-Free Contracts Generation', pos=(10, 300))
                dpg.add_text('Authors', pos=(373, 340))
                dpg.add_text('Mohamed Amine Layachi', pos=(287, 370))
                dpg.add_text('Khaoula Boukir', pos=(332, 400))

        else:
            dpg.delete_item(ABOUT_VIEW)

    def __redo(self):
        if 1 <= self.__current_index + 1 < len(self.__undo_redo_stack):
            self.__current_index += 1

            for item in reversed(range(len(self.__current_state.suggestions))):
                if dpg.does_item_exist(f'CIRCLE_{item}'):
                    dpg.delete_item(f'CIRCLE_{item}')

            self.__current_state = self.__undo_redo_stack[self.__current_index]

            offset = 20
            init_x = 1167
            # Here -2 because the ACSL contracts are also an entry of the suggestions.
            self.__samples = len(self.__current_state.suggestions) - 2
            for item in reversed(range(self.__samples + 2)):
                dpg.draw_circle(tag=f'CIRCLE_{item}', radius=5, center=[init_x - offset, 490], fill=(0, 0, 0, -255),
                                parent=MAIN_WINDOW)
                init_x -= offset

            self.__inference_distributor()

    def __undo(self):
        if 1 <= self.__current_index - 1 < len(self.__undo_redo_stack):
            self.__current_index -= 1

            for item in reversed(range(len(self.__current_state.suggestions))):
                if dpg.does_item_exist(f'CIRCLE_{item}'):
                    dpg.delete_item(f'CIRCLE_{item}')

            self.__current_state = self.__undo_redo_stack[self.__current_index]

            offset = 20
            init_x = 1167
            self.__samples = len(self.__current_state.suggestions) - 2
            for item in reversed(range(self.__samples+2)):
                dpg.draw_circle(tag=f'CIRCLE_{item}', radius=5, center=[init_x - offset, 490],
                                fill=(0, 0, 0, -255), parent=MAIN_WINDOW)
                init_x -= offset

            self.__inference_distributor()

    def __generate(self):
        self.__nectron_init()
        program_description = nullable_processor(dpg.get_value(PD_FIELD))
        if len(program_description) > 0:
            self.__current_index += 1
            self.__generate_contracts(description=program_description)
        else:
            if dpg.does_item_exist(NECTRON_NOTHING_TO_GENERATE):
                dpg.delete_item(NECTRON_NOTHING_TO_GENERATE)

            with dpg.window(tag=NECTRON_NOTHING_TO_GENERATE, popup=True, modal=True):
                dpg.add_text(default_value='Nothing to generate. Please provide a program description and try again.',
                             wrap=600)

    def __nectron_init(self):
        error_1 = 'The API Key is not provided. Please make sure you set up a valid API Key in the settings.'
        error_2 = ("You provided a file path instead of an API Key. Please check if there's an API Key in the file. "
                   "Otherwise, make sure to set up a valid API Key in the settings.")
        error_else = ('The API Key is not valid. Please check the validity of the API Key and try again.'
                        ' If the issue persist, contact the developer.')

        if self.__configuration['backend_model'] == 'OpenRouter':
            gemini_enabled = False
        else:
            gemini_enabled = True

        if self.__configuration['api_key'] == '':
            if dpg.does_item_exist(NECTRON_CONNECTION_WARNING):
                dpg.delete_item(NECTRON_CONNECTION_WARNING)
            with dpg.window(tag=NECTRON_CONNECTION_WARNING, popup=True, modal=True):
                dpg.add_text(default_value=error_1, wrap=600)
        elif os.path.exists(self.__configuration['api_key']):
            if dpg.does_item_exist(NECTRON_CONNECTION_WARNING):
                dpg.delete_item(NECTRON_CONNECTION_WARNING)
            with dpg.window(tag=NECTRON_CONNECTION_WARNING, popup=True, modal=True):
                dpg.add_text(default_value=error_2, wrap=600)
        else:
            try:
                gemini_id = self.__default_gemini
                openrouter_id = self.__default_openrouter
                current_model_id = self.__configuration['model_identifier']

                if gemini_enabled and current_model_id.find('gemini') != -1:
                    if current_model_id.find('/') == '-1':
                        temp_id = current_model_id.split('/')[1]
                        if len(temp_id) != 0:
                            gemini_id = temp_id
                    else:
                        gemini_id = current_model_id
                elif not gemini_enabled:
                    openrouter_id = current_model_id
                
                self.__nectron = Nectron(api_key=self.__configuration['api_key'], gemini_enabled=gemini_enabled,
                                         gemini_identifier=gemini_id, openrouter_model_id=openrouter_id,
                                         explanation=self.__configuration['explanation'])
                
                self.__nectron.generate_contracts = self.__generate_contracts
            except (InvalidArgument, AuthenticationError):
                if dpg.does_item_exist(NECTRON_CONNECTION_WARNING):
                    dpg.delete_item(NECTRON_CONNECTION_WARNING)
                with dpg.window(tag=NECTRON_CONNECTION_WARNING, popup=True, modal=True):
                    dpg.add_text(default_value=error_else, wrap=600)

    def __generate_contracts(self, description: str):
        if self.__nectron is not None:
            dpg.set_value(PROGRESS_BAR, 0.1)
            try:
                srs_generation = self.__nectron.generator.generate_srs(program_description=description)
            except (InvalidArgument, TypeError, AuthenticationError):
                if dpg.does_item_exist(NECTRON_CONNECTION_WARNING):
                    dpg.delete_item(NECTRON_CONNECTION_WARNING)
                dpg.set_value(PROGRESS_BAR, 0.0)
                error_else = ('The API Key is not valid. Please check the validity of the API Key and try again.'
                              ' If the issue persists, contact the developer.')
                with dpg.window(tag=NECTRON_CONNECTION_WARNING, popup=True, modal=True):
                    dpg.add_text(default_value=error_else, wrap=600)

                return

            dpg.set_value(PROGRESS_BAR, 0.2)

            srs = srs_generation[0]
            srs_exp = srs_generation[1]

            nar_generation = self.__nectron.generator.generate_nar(srs=srs)

            dpg.set_value(PROGRESS_BAR, 0.4)

            nar = nar_generation[0]
            nar_exp = nar_generation[1]
            corrected_nar = nar
            contracts_seed = ''

            correction_amount = self.__nectron.correction_max
            flag = True
            grammar_ok = True
            while flag and correction_amount > 0 and grammar_ok:
                try:
                    self.__nectron.conversion_engine.read_nar_from_generated(generated_nar=corrected_nar)
                    contracts_seed = self.__nectron.conversion_engine.compile()
                except NonCompilableNAR:
                    nar_correction = self.__nectron.generator.correct_syntax(nar_code=nar, srs=srs)
                    corrected_nar = nar_correction[0]
                    nar_exp = nar_correction[1]
                    grammar_ok = (corrected_nar.find('var:') != -1 and corrected_nar.find('action:') != -1
                                  and corrected_nar.find('return:') != -1)
                    correction_amount -= 1
                else:
                    flag = False

            dpg.set_value(PROGRESS_BAR, 0.8)

            if correction_amount > 0 and grammar_ok:
                suggestions = []
                if self.__samples == 0:
                    plan = self.__nectron.generator.generate_ToT(program_description=description, num_app=1)
                    refinement = self.__nectron.generator.refine_contracts(contracts=contracts_seed.string(),
                                                                            verification_plan=plan)
                elif self.__samples > 0:
                    plan = self.__nectron.generator.generate_ToT(program_description=description, num_app=self.__samples)
                    refinement = self.__nectron.generator.reflective_reasoning(contracts=contracts_seed.string(),
                                                                                verification_plan=plan,
                                                                                batch_samples=self.__samples)
                    suggestions = refinement[2]

                refined_contracts = refinement[0]
                refinement_exp = refinement[1]

                sphinx = self.__nectron.generator.sphinx(contracts=refined_contracts, verification_plan=plan)

                revised_contracts = f"{contracts_seed.get_imports()}\n/*@\n" + sphinx[0].replace('/*@', '').replace('*/', '').strip('\n') + '\n*/'
                revision_exp = sphinx[1]

                dpg.set_value(PROGRESS_BAR, 0)

                begin_tag = '<contracts>\n'
                end_tag = '\n</contracts>'
                suggestions = [[f"{contracts_seed.get_imports()}\n/*@\n" + sample[0].replace(begin_tag, '').replace(end_tag, '').replace('/*@', '').replace('*/', '') + '\n*/',
                                 sample[1]] for sample in suggestions]
                suggestions.insert(0, [revised_contracts, revision_exp])
                suggestions.insert(1, [f"{contracts_seed.get_imports()}\n/*@\n" + refinement[0].replace('/*@', '').replace('*/', '') + '\n*/', refinement_exp])

                self.__current_state = NectronState(
                    program_description=description,
                    acsl_contracts=revised_contracts,
                    seeds=contracts_seed.string(),
                    srs=srs,
                    nar_representation=corrected_nar,
                    srs_exp=srs_exp,
                    nar_gen_exp=nar_exp,
                    refinement_exp=revision_exp,
                    suggestions=suggestions,
                )
            else:
                dpg.set_value(PROGRESS_BAR, 0)
                self.__current_state = NectronState(
                    program_description=description,
                    acsl_contracts='The provided prompt is outside the scope of contracts that NECTRON can generate.',
                    seeds='Non Convertable NAR',
                    srs='',
                    nar_representation='',
                    srs_exp='',
                    nar_gen_exp='',
                    refinement_exp='',
                    suggestions=[],
                )

            self.__current_suggestion_index = 0
            self.__current_index += 1
            self.__undo_redo_stack.append(self.__current_state)

            self.__inference_distributor()