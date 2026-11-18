"""Controls for the actual planning validator; these are not theorem tests."""
import copy
import unittest
import plan


class PlanControls(unittest.TestCase):
    def setUp(self):
        self.data, self.coverage, self.obligations, self.external = copy.deepcopy(plan.load())
        self.tasks = {t['id']: t for t in self.data['tasks']}

    def validate(self):
        return plan.validate_records(self.data, self.coverage, self.obligations, self.external)

    def test_valid_snapshot(self):
        self.validate()
        plan.validate_files(self.data, self.coverage)

    def test_unknown_dependency(self):
        self.tasks['PB1.1']['dependencies'].append('PB999.1')
        with self.assertRaisesRegex(plan.PlanError, 'unknown dependency PB999.1'):
            self.validate()

    def test_dependency_cycle(self):
        self.tasks['PB1.1']['dependencies'].append('PB4.5')
        with self.assertRaisesRegex(plan.PlanError, 'dependency cycle'):
            self.validate()

    def test_open_question_not_a_proof(self):
        q = next(e for e in self.coverage['entries'] if e['id'] == '6.2')
        q['tasks'] = ['PB8.1']
        with self.assertRaisesRegex(plan.PlanError, 'open question incorrectly assigned'):
            self.validate()

    def test_verified_label_without_evidence(self):
        t = self.tasks['PB0.1']
        t['status'], t['proof_status'] = 'VERIFIED', 'CERTIFIED'
        with self.assertRaisesRegex(plan.PlanError, 'verification record required'):
            self.validate()

    def test_one_writer_rule(self):
        self.tasks['PB2.7']['owner_role'] = 'resources'
        with self.assertRaisesRegex(plan.PlanError, 'module owner conflict'):
            self.validate()

    def test_uncovered_statement(self):
        self.coverage['entries'][0]['tasks'] = []
        with self.assertRaisesRegex(plan.PlanError, 'uncovered paper statement'):
            self.validate()

    def test_premature_ready(self):
        self.tasks['PB1.1']['status'] = 'READY'
        with self.assertRaisesRegex(plan.PlanError, 'incomplete dependencies'):
            self.validate()

    def test_literal_statement_not_just_id(self):
        self.coverage['entries'][0]['statement'] += ' Changed claim.'
        with self.assertRaisesRegex(plan.PlanError, 'literal statement mismatch'):
            plan.validate_files(self.data, self.coverage)

    def test_module_import_cycle(self):
        graph = copy.deepcopy(plan.read_json(plan.ROOT / 'module-graph.json'))
        kernel = next(m for m in graph['modules'] if m['path'].endswith('/Kernel.lean'))
        kernel['local_imports'].append('release-core/Solution.lean')
        with self.assertRaisesRegex(plan.PlanError, 'local module import cycle'):
            plan.validate_module_graph(self.data, graph)

    def test_challenge_cannot_import_project(self):
        graph = copy.deepcopy(plan.read_json(plan.ROOT / 'module-graph.json'))
        graph['modules'][0]['local_imports'].append('release-core/PaperB/Spec.lean')
        with self.assertRaisesRegex(plan.PlanError, 'Challenge has project import'):
            plan.validate_module_graph(self.data, graph)

    def test_unreachable_release_module(self):
        graph = copy.deepcopy(plan.read_json(plan.ROOT / 'module-graph.json'))
        path = 'release-core/PaperB/Unused.lean'
        graph['modules'].append({'path':path,'local_imports':[],'owner_role':'graph','admission':'FIRST_3_2'})
        self.data['module_owners'][path] = 'graph'
        with self.assertRaisesRegex(plan.PlanError, 'unreachable planned first-release module'):
            plan.validate_module_graph(self.data, graph)

    def test_root_count_cannot_be_inflated(self):
        self.data['formal_roots_accepted'] = 1
        with self.assertRaisesRegex(plan.PlanError, 'certified root count'):
            self.validate()

    def test_missing_new_corollary(self):
        self.coverage['entries'] = [e for e in self.coverage['entries'] if e['id'] != '4.7']
        with self.assertRaisesRegex(plan.PlanError, 'wrong active manuscript inventory size'):
            self.validate()

    def test_unsupported_extension_closure(self):
        self.obligations['extension_obligations'][0]['status'] = 'CLOSED'
        with self.assertRaisesRegex(plan.PlanError, 'unsupported extension closure'):
            self.validate()

    def test_tracker_active_source_identity(self):
        self.data['manuscript']['sha256'] = '0' * 64
        with self.assertRaisesRegex(plan.PlanError, 'tracker active-source identity mismatch'):
            plan.validate_files(self.data, self.coverage)


if __name__ == '__main__':
    unittest.main(verbosity=2)
