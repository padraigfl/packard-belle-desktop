import React, { Component } from "react";
import { Theme, ExplorerView, ExplorerIcon } from "packard-belle";
import cx from "classnames";
import logo from "./logo.svg";
import "./App.css";
import Explorer from "./components/ExplorerWindow";
import TaskBar from "./components/TaskBar";
import ProgramProvider, { ProgramContext } from "./contexts/programs";
import ScaleProvider, { ScaleContext } from "./contexts/scale";

const testOptions = [
  {
    title: "Test",
    icon: logo,
    onClick: () => {},
    options: [
      {
        title: "Test",
        icon: logo,
        onClick: () => {}
      }
    ]
  },
  {
    title: "Test2",
    icon: logo,
    onClick: () => {}
  },
  {
    title: "Test3",
    icon: logo,
    onClick: () => {}
  },
  {
    title: "Test4",
    icon: logo,
    onClick: () => {}
  }
];

class Desktop extends Component {
  static contextType = ProgramContext;

  render() {
    return (
      <ProgramProvider>
        <ScaleContext.Consumer>
          {context => (
            <React.Fragment>
              <Theme
                className={cx("desktop", { desktopX2: context.scale === 2 })}
              >
                <ExplorerView options={testOptions}>
                  {testOptions.map(option => (
                    <ExplorerIcon key={option.title} {...option} />
                  ))}
                </ExplorerView>
                <TaskBar />
                <Explorer scale={context.scale} />
              </Theme>
              <button onClick={context.changeScale}>changeScale</button>
            </React.Fragment>
          )}
        </ScaleContext.Consumer>
      </ProgramProvider>
    );
  }
}

const App = () => (
  <ScaleProvider>
    <Desktop />
  </ScaleProvider>
);

// include corner thing if resizable
// body of explorer window needs to fill space

export default App;
