import DirNode from "../classes/directory";
import { FileTypes } from "../classes/types";
import { Action, fileSystemReducer, SimulatedFileSystem } from "../filesystem";
import { getFileFromPath, mntHierarchyNested } from "../utils"

describe('fileSystemReducer', () => {
  let state: SimulatedFileSystem;
  beforeAll(() => {
    state = {
      fileHierarchy: new DirNode(mntHierarchyNested),
      logs: {},
    };
  })
  it(Action.COPY, () => {
    const newSystem = fileSystemReducer(state, {
      type: Action.NEW,
      value: {
        actionId: 'abc',
        location: '/mnt/c/usr/me',
        newFile: {
          type: FileTypes.DATA,
          data: { text: 'this is the text' },
          name: 'testFile.txt',
        }
      },
    });
    expect(getFileFromPath('/mnt/c/usr/me/testFile.txt', newSystem.fileHierarchy)).toBeTruthy();
  });
})