import React from "react";
import { WindowProgram } from "packard-belle";
import cx from "classnames";
import Window from "../tools/Window";
import { notepad16 } from "../../icons";
import "./_styles.scss";

const noop = () => {};

export const buildMenu = (props, state) => [
  {
    title: "File",
    options: [
      { title: "Open", isDisabled: true },
      { title: "Close", onClick: () => props.onClose(props) },
      {
        title: "Wrap",
        onClick: () => state.toggleWrap(!state.wrap),
        isChecked: state.wrap
      }
    ]
  },
  {
    title: "Help",
    options: [{ title: `About ${props.title}`, isDisabled: true }]
  }
];

const Notepad = props => {
  const [wrap, toggleWrap] = React.useState(false);
  const [text, setText] = React.useState(props.data.content || "");

  return (
    <Window
      {...props}
      initialHeight={props.initialHeight || 200}
      initialWidth={props.initialWidth || 200}
    >
      {rnd => (
        <WindowProgram
          className={cx("Notepad", {
            "Notepad--wrap": wrap,
            "Window--active": props.isActive
          })}
          title={`${props.title || "Untitled"} - Notepad`}
          icon={notepad16}
          footer={[
            { text: "needs 100% width height" },
            { text: "overflow control" }
          ]}
          onClose={() => props.onClose(props)}
          onMinimize={() => props.onMinimize(props)}
          onRestore={rnd.restore}
          onMaximize={rnd.maximize}
          changingState={rnd.state.isDragging || rnd.state.isResizing}
          menuOptions={buildMenu(props, { toggleWrap, wrap })}
          maximizeOnOpen={rnd.context.isMobile}
        >
          <div className="Notepad__textarea">
            <textarea onChange={e => setText(e.target.value)}>{text}</textarea>
          </div>
        </WindowProgram>
      )}
    </Window>
  );
};

Notepad.defaultProps = {
  data: {
    content: ""
  }
};

export default Notepad;
