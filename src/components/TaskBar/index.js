import React, { Component } from "react";
import { TaskBar as TaskBarComponent } from "packard-belle";
import { ProgramContext } from "../../App";
import startMenuData from "../../data/start";

class TaskBar extends Component {
  static contextType = ProgramContext;

  render() {
    return (
      <ProgramContext.Consumer>
        {context => (
          <TaskBarComponent
            options={startMenuData}
            openWindows={context.openWindows}
          />
        )}
      </ProgramContext.Consumer>
    );
  }
}

export default TaskBar;
