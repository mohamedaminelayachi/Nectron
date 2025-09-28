import argparse
from scripts import app
from eval import NectronInferrer
from eval import NectronEvaluator


def main():
    parser = argparse.ArgumentParser(
        description="CLI for running Nectron's app, inference, or evaluation."
    )

    subparsers = parser.add_subparsers(dest="command", required=True)

    parser_app = subparsers.add_parser("run_app", help="Run the main Nectron app (no arguments)")

    parser_inference = subparsers.add_parser(
        "run_inference",
        help="The Nectron Inference Framework"
    )
    parser_inference.add_argument(
        "--eval_dataset_path",
        default="evaluation/eval_programs.json",
        help="Path to evaluation dataset (default: evaluation/eval_programs.json)",
    )
    parser_inference.add_argument(
        "--gemini_api_key",
        required=True,
        help="Gemini API Key (required)",
    )
    parser_inference.add_argument(
        "--openrouter_api_key",
        required=True,
        help="OpenRouter API Key (required)",
    )
    parser_inference.add_argument(
        "--output_dir",
        required=True,
        help="Output directory for inference results (required)",
    )
    parser_inference.add_argument(
         "--explanation",
        action="store_true",
        help="Generate explanations (optional, default: False)",
    )
    parser_inference.add_argument(
        "--target",
        required=True,
        help='Inference Target: Nectron (n) or Zero-Shot (zs)'
    )
    parser_inference.add_argument(
        "--r",
        type=int,
        default=2,
        help="Number of runs or replications (r) (default: 2)",
    )
    parser_inference.add_argument(
        "--tot",
        type=int,
        default=1,
        help="Number of Trees-of-Thoughts (s) (default: 1)",
    )

    parser_evaluation = subparsers.add_parser(
        "run_evaluation",
        help="The Nectron Evaluation Framework"
    )
    parser_evaluation.add_argument(
        "--inference_dir",
        required=True,
        help="Directory from inference results (required)",
    )
    parser_evaluation.add_argument(
        "--save_dir",
        required=True,
        help="Directory to save evaluation results (required)",
    )
    parser_evaluation.add_argument(
        "--r",
        type=int,
        default=2,
        help="Reflective Reasoning Intensity (r) (default: 2)",
    )
    parser_evaluation.add_argument(
        "--tot",
        type=int,
        default=1,
        help="Number of Trees-of-Thoughts (s) (default: 1)",
    )
    parser_evaluation.add_argument(
        "--target",
        required=True,
        help='Evaluation Target: Nectron (n) or Zero-Shot (zs)'
    )
    parser_evaluation.add_argument(
        "--exclude_models",
        type=lambda s: [item.strip() for item in s.split(",")],
        default=[],
        help="Comma-separated list of model IDs to exclude from the evaluation, check model IDs."
    )

    args = parser.parse_args()

    if args.command == "run_app":
        ins = app.NectronApp()
        ins.run()

    elif args.command == "run_inference":
        inferrer = NectronInferrer(eval_dataset_path=args.eval_dataset_path,
            gemini_api_key=args.gemini_api_key,
            openrouter_api_key=args.openrouter_api_key,
            output_dir=args.output_dir,
            explanation=args.explanation)
        if args.target.lower() in ['nectron', 'n']:
            inferrer.infer_nectron(rri=args.r, num_tots=args.tot, sleep=False)
        elif args.target.lower() in ['zero-shot', 'zs']:
            inferrer.infer_zero_shot(sleep=False)

    elif args.command == 'run_evaluation':
        evaluator = NectronEvaluator(inference_dir=args.inference_dir,
            save_dir=args.save_dir,
            rri=args.r,
            tot=args.tot)
        
        if args.target.lower() in ['nectron', 'n']:
            evaluator.evaluate(model_exclusion=args.exclude_models)
        elif args.target.lower() in ['zero-shot', 'zs']:
            evaluator.evaluate(model_exclusion=args.exclude_models, zero_shot=True)

if __name__ == '__main__':

    main()