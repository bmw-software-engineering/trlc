import unittest
from unittest.mock import patch, MagicMock
from trlc.ast import Symbol_Table

class TestRecordObject:
    def __init__(self, location, section):
        self.location = location
        self.section = section

class TestSection:
    def __init__(self, name):
        self.name = name

class TestIterRecordObjectsBySection(unittest.TestCase):

    @patch("trlc.ast.Symbol_Table.iter_record_objects")
    def test_iter_record_objects_by_section(self, mock_iter_record_objects):        
        mock_location = MagicMock(file_name='file1')
        mock_section1 = TestSection('section1')
        mock_section2 = TestSection('section2')
        record1 = TestRecordObject(mock_location, [mock_section1, mock_section2])
        mock_iter_record_objects.return_value = [record1]
        
        results = list(Symbol_Table().iter_record_objects_by_section())
        
        expected_results = [
            'file1',
            ('section1', 0),
            ('section2', 1),
            (record1, 1)
        ]
        
        self.assertEqual(results, expected_results)

if __name__ == '__main__':
    unittest.main()